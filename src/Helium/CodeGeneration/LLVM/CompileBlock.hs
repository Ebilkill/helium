{-| Module      :  CompileMethod
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.CompileBlock (compileBlock) where

import Data.String(fromString)
import Data.Word(Word32)
import Data.Either

import Debug.Trace

import Helium.CodeGeneration.LLVM.Env
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.CompileType
import Helium.CodeGeneration.LLVM.CompileBind
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.CompileConstructor(compileExtractFields, compileExtractCursorFields)
import Helium.CodeGeneration.LLVM.Struct(tagValue, tupleStruct)
import Helium.CodeGeneration.LLVM.CompileStruct
import qualified Helium.CodeGeneration.LLVM.Builtins as Builtins

import Lvm.Common.Id(Id, NameSupply, splitNameSupply, splitNameSupplies, mapWithSupply, freshId, idFromString)
import Lvm.Common.IdMap(findMap)
import qualified Lvm.Core.Type as Core
import Lvm.Core.Expr (PrimFun(..))

import Helium.CodeGeneration.Core.TypeEnvironment (typeOfPrimFun, typeOfPrimFunArity, isPackedType)

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.Primitive as Iridium
import LLVM.AST as AST
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import LLVM.AST.Constant (Constant(Int, Float, Array, Undef, GlobalReference))
import qualified LLVM.AST.IntegerPredicate as IntegerPredicate
import qualified LLVM.AST.Float as Float

import Data.List (maximumBy, group, sort, partition)
import Data.Function (on)

data Partial = Partial [Named Instruction] (Named Terminator) [BasicBlock]

infixr 3 +>
(+>) :: [Named Instruction] -> Partial -> Partial
instrs1 +> (Partial instrs2 terminator blocks) = Partial (instrs1 ++ instrs2) terminator blocks

compileBlock :: Env -> NameSupply -> Iridium.Block -> [BasicBlock]
compileBlock env supply (Iridium.Block name instruction) = BasicBlock (toName name) instrs term : blocks
  where
    Partial instrs term blocks = compileInstruction env supply instruction

compileInstruction :: Env -> NameSupply -> Iridium.Instruction -> Partial
compileInstruction env supply (Iridium.Let name expr next) = compileExpression env supply1 expr name +> compileInstruction env supply2 next
  where
    (supply1, supply2) = splitNameSupply supply
compileInstruction env supply (Iridium.LetAlloc binds next) =
  compileBinds env supply1 binds
  +> compileInstruction env supply2 next
  where
    (supply1, supply2) = splitNameSupply supply
compileInstruction env supply (Iridium.Jump to) = Partial [] (Do $ Br (toName to) []) []
compileInstruction env supply (Iridium.Return var) = Partial [] (Do $ Ret (Just $ toOperand env var) []) []
-- A Match has undefined behaviour if it does not match, so we do not need to check whether it actually matches.
compileInstruction env supply (Iridium.Match var _ _ [] next) = compileInstruction env supply next
compileInstruction env supply (Iridium.Match var target _ args next)
  | isPackedType (Iridium.variableType var)
    = -- bitcast to a void* (just in case we aren't a void* already) and go to the next element
      -- Going to the next element is important to skip the constructor tag (which is for case,
      -- not for match), and we can't easily fix this from the case itself.
      [ cursorTagName   := AST.BitCast (toOperand env var) voidPointer []
      , cursorStartName := getElementPtr (LocalReference voidPointer cursorTagName) [1]
      ]
      -- extract the fields
      +> compileExtractCursorFields env supply3 (LocalReference voidPointer cursorStartName) struct args
      -- compile whatever is next
      +> compileInstruction env supply4 next
  | otherwise
    = [ addressName := AST.BitCast (toOperand env var) (pointer t) []
      ]
      +> compileExtractFields env supply'' address struct args
      +> compileInstruction env supply''' next
    where
      -- isPackedType
      (cursorTagName,   supply1)  = freshName supply
      (cursorStartName, supply2)  = freshName supply1
      (supply3, supply4) = splitNameSupply supply2
      -- otherwise; we might want to merge this somehow but the name clashes would be... strange?
      t = structType env struct
      (addressName, supply') = freshName supply
      address = LocalReference (pointer t) addressName
      (supply'', supply''') = splitNameSupply supply'
      LayoutPointer struct = case target of
        Iridium.MatchTargetConstructor (Iridium.DataTypeConstructor conId _) -> findMap conId (envConstructors env)
        Iridium.MatchTargetTuple arity -> LayoutPointer $ tupleStruct arity
compileInstruction env supply (Iridium.Case var (Iridium.CaseConstructor alts))
  -- The variable is a packed (cursor) type
  | isPackedType (Iridium.variableType var) =
    let (instr, terminator) = compileCaseConstructorCursor env supply var alts'
    in  Partial instr terminator []
  -- All constructors are pointers
  | null inlines =
    let (instr, terminator) = compileCaseConstructorPointer env supply var pointers
    in Partial instr terminator []

  -- All constructors are inline
  | null pointers =
    -- Extract the most frequent branch
    let
      (defaultBranch, alts'') = caseExtractMostFrequentBranch inlines
      (instr, terminator) = compileCaseConstructorInline env supply var alts'' defaultBranch
    in
      Partial instr terminator []

  -- Only one pointer value
  | length pointers == 1 =
    let
      [CaseAlt _ _ pointerBranch] = pointers
      (instr, terminator) = compileCaseConstructorInline env supply var inlines pointerBranch
    in
      Partial instr terminator []

  -- Mixed
  | otherwise =
    let
      supply1 : supplyCaseInline : supplyCasePointer : _ = splitNameSupplies supply
      (pointerBranch, _) = freshId supply1

      -- Check whether an inline constructor matches, otherwise jump to the pointers branch
      (inlineInstr, inlineTerminator) = compileCaseConstructorInline env supply var inlines pointerBranch

      -- Check which pointer constructor matches
      (pointerInstr, pointerTerminator) = compileCaseConstructorPointer env supply var pointers
    in
      Partial inlineInstr inlineTerminator [BasicBlock (toName pointerBranch) pointerInstr pointerTerminator]

  where
    alts' = map (toCaseAlt env) alts
    (inlines, pointers) = partition altIsInline alts'

compileInstruction env supply (Iridium.Case var (Iridium.CaseInt alts defaultBranch)) = Partial [] (Do terminator) []
  where
    terminator :: Terminator
    terminator = Switch (toOperand env var) (toName defaultBranch) (map altToDestination alts) []
    altToDestination :: (Int, Id) -> (Constant, Name)
    altToDestination (value, to)
      = (Int (fromIntegral $ targetWordSize $ envTarget env) (fromIntegral value), toName to)

compileInstruction _ _ (Iridium.Unreachable _) = Partial [] (Do $ Unreachable []) []

compileExpression :: Env -> NameSupply -> Iridium.Expr -> Id -> [Named Instruction]
compileExpression env supply (Iridium.Literal (Iridium.LitString value)) name =
  [ namePtr := Alloca vectorType Nothing 0 []
  , Do $ Store False (LocalReference (pointer vectorType) namePtr) (ConstantOperand vector) Nothing 0 []
  -- Cast [n x i32]* to i32*
  , nameArray := BitCast (LocalReference (pointer vectorType) namePtr) voidPointer []
  , toName name := Call
    { tailCallKind = Nothing
    , callingConvention = Fast
    , returnAttributes = []
    , function = Right $ Builtins.unpackString
    , arguments =
      [ (ConstantOperand $ Int (fromIntegral $ targetWordSize $ envTarget env) $ fromIntegral $ length value, [])
      , (LocalReference voidPointer nameArray, [])
      ]
    , functionAttributes = []
    , metadata = []
    }
  ]
  where
    (namePtr, supply') = freshName supply
    (nameArray, _) = freshName supply'
    vectorType = ArrayType (fromIntegral $ length value) (IntegerType 32)
    vector = Array (IntegerType 32) $ map (\c -> Int 32 $ fromIntegral $ fromEnum c) value
compileExpression env supply (Iridium.Literal literal) name = [toName name := BitCast (ConstantOperand constant) t []]
  where
    constant :: Constant
    (constant, t) = case literal of
      Iridium.LitInt _ value ->
        ( Int (fromIntegral $ targetWordSize $ envTarget $ env) (fromIntegral $ value)
        , envValueType env
        )
      Iridium.LitFloat Iridium.Float32 value ->
        ( Float $ Float.Single $ realToFrac value
        , FloatingPointType FloatFP
        )
      Iridium.LitFloat Iridium.Float64 value ->
        ( Float $ Float.Double value
        , FloatingPointType DoubleFP
        )
compileExpression env supply expr@(Iridium.Call to@(Iridium.GlobalFunction global arity tp) args) name
  | not fakeIO && all isRight args =
    [ toName name := Call
        { tailCallKind = Nothing
        , callingConvention = compileCallingConvention convention
        , returnAttributes = []
        , function = Right $ globalFunctionToOperand env to
        , arguments = [(toOperand env arg, []) | Right arg <- args]
        , functionAttributes = []
        , metadata = []
        }
    ]
  | not fakeIO =
    let
      (name', supply') = freshName supply
      fromType = Iridium.typeToStrict retType
      toType = Iridium.typeOfExpr (envTypeEnv env) expr
      castArgument s (var, argType) =
        ( cast s' env (toOperand env var) argName (Iridium.variableType var) argType
        , LocalReference (compileType env argType) argName)
        where
          (argName, s') = freshNameFromId (Iridium.variableName var) s
      (castArgumentInstructions, argOperands) = unzip $ mapWithSupply castArgument supply' $ zip (rights args) $ rights argTypes
    in
      concat castArgumentInstructions
      ++
        [ name' := Call
          { tailCallKind = Nothing
          , callingConvention = compileCallingConvention convention
          , returnAttributes = []
          , function = Right $ globalFunctionToOperand env to
          , arguments = map (\arg -> (arg, [])) argOperands
          , functionAttributes = []
          , metadata = []
          }
        ]
      ++ cast supply env (LocalReference (compileType env fromType) name') (toName name) fromType toType
    -- We might need to cast the returned value and argument values, if type arguments were passed.
    -- Consider `%y = call @id: (forall a. !a -> a) $ {!Float} {%x: !Float}`
    -- Function 'id' will return the value as `i8*`, which we thus need to cast to Float
  | otherwise =
    [ toName nameValue := Call
        { tailCallKind = Nothing
        , callingConvention = compileCallingConvention convention
        , returnAttributes = []
        , function = Right $ globalFunctionToOperand env (Iridium.GlobalFunction global (arity - 1) $ Iridium.typeFromFunctionType $ Iridium.FunctionType (init argTypes) $ Core.TCon $ Core.TConDataType $ idFromString "Int")
        , arguments = [(toOperand env arg, []) | Right arg <- init args]
        , functionAttributes = []
        , metadata = []
        }
    ]
    ++ [toName nameRealWorld := Select (ConstantOperand $ Int 1 1) (ConstantOperand $ Undef tRealWorld) (ConstantOperand $ Undef tRealWorld) []]
    ++ compileBinds env supply'' [Iridium.Bind name (Iridium.BindTargetConstructor ioRes)
        [Left Iridium.typeInt, Right $ Iridium.VarLocal $ Iridium.Local nameValue Iridium.typeInt, Right $ Iridium.VarLocal $ Iridium.Local nameRealWorld Iridium.typeRealWorld]]
  where
    Iridium.FunctionType argTypes retType = Iridium.extractFunctionTypeWithArity (envTypeEnv env) arity tp
    EnvMethodInfo convention fakeIO = findMap global (envMethodInfo env)
    (nameValue, supply') = freshId supply
    (nameRealWorld, supply'') = freshId supply'
    ioRes = Iridium.DataTypeConstructor ioResId $ Iridium.typeFromFunctionType $ Iridium.FunctionType [Left $ Core.Quantor Nothing, Right $ Core.TVar 0, Right Iridium.typeRealWorld] Iridium.typeRealWorld
    ioResId = idFromString "IORes"
    tRealWorld = compileType env Iridium.typeRealWorld
compileExpression env supply (Iridium.Eval var) name = compileEval env supply (toOperand env var) (Iridium.variableType var) $ toName name
compileExpression env supply (Iridium.Var var) name = cast supply env (toOperand env var) (toName name) t t
  where t = Iridium.variableType var
compileExpression env supply (Iridium.Cast var toType) name = cast supply env (toOperand env var) (toName name) t toType
  where t = Iridium.variableType var
compileExpression env supply (Iridium.CastThunk var) name = cast supply env (toOperand env var) (toName name) t toType
  where
    t = Iridium.variableType var
    toType = Iridium.typeNotStrict t
compileExpression env supply expr@(Iridium.Instantiate var _) name = cast supply env (toOperand env var) (toName name) t toType
  where
    t = Iridium.variableType var
    toType = Iridium.typeOfExpr (envTypeEnv env) expr
compileExpression env supply (Iridium.Seq _ var) name = cast supply env (toOperand env var) (toName name) t t
  where t = Iridium.variableType var
compileExpression env supply expr@(Iridium.Phi branches) name = [toName name := Phi (compileType env t) (map compileBranch branches) []]
  where
    t = Iridium.typeOfExpr (envTypeEnv env) expr
    compileBranch :: Iridium.PhiBranch -> (Operand, Name)
    compileBranch (Iridium.PhiBranch blockId var) = (toOperand env var, toName blockId)
compileExpression env supply (Iridium.Undefined ty) name = [toName name := Select (ConstantOperand $ Int 1 1) (ConstantOperand $ Undef t) (ConstantOperand $ Undef t) []]
  where
    t = compileType env ty

-- Cursor expressions
compileExpression env supply (Iridium.PrimitiveExpr prim args) name
  = error "I don't like primitive expressions :("

compileExpression env supply expr@(Iridium.CallPrimFun PrimNewCursor args) name =
  [ -- namePtr := Alloca vectorType Nothing 0 []
  -- , Do $ Store False (LocalReference (pointer vectorType) namePtr) (ConstantOperand vector) Nothing 0 []
  -- Cast [n x i32]* to i32*
  -- , nameArray := BitCast (LocalReference (pointer vectorType) namePtr) voidPointer []
    toName name := Call
    { tailCallKind = Nothing
    , callingConvention = C
    , returnAttributes = []
    , function = Right $ Builtins.newCursor
    , arguments = []
    , functionAttributes = []
    , metadata = []
    }
  ]
  where
    (namePtr, supply') = freshName supply
    (nameArray, _) = freshName supply'

compileExpression env supply (Iridium.CallPrimFun (PrimWriteCtor c) [Left restList, Right cursor]) name =
  [ namePtr := Alloca vectorType Nothing 0 []
  , Do $ Store False (LocalReference (pointer vectorType) namePtr) (ConstantOperand vector) Nothing 0 []
  --, nameArray := BitCast (LocalReference (pointer vectorType) namePtr) voidPointer []
  , nameIntermediate := Call
    { tailCallKind = Nothing
    , callingConvention = C
    , returnAttributes = []
    , function = Right $ Builtins.writeCursor
    , arguments =
      [ (toOperand env cursor, [])
      , (ConstantOperand $ Int (fromIntegral $ targetWordSize $ envTarget env) $ fromIntegral $ 1, [])
      , (LocalReference voidPointer namePtr, [])
      ]
    , functionAttributes = []
    , metadata = []
    }
  , toName name := Call
    { tailCallKind = Nothing
    , callingConvention = C
    , returnAttributes = []
    , function = Right $ Builtins.reserveCursorSizes
    , arguments =
      [ (LocalReference cursorStructType nameIntermediate, [])
      -- The 1 at the end of this ConstantOperand is the amount of sizes to reserve. Make sure to base this on the amount you need! TODO FIXME
      , (ConstantOperand $ Int (fromIntegral $ targetWordSize $ envTarget env) $ fromIntegral $ 1, [])
      ]
    , functionAttributes = []
    , metadata = []
    }
  ]
  where
    (namePtr, supply') = freshName supply
    (nameArray, supply'') = freshName supply'
    (nameIntermediate, _) = freshName supply''
    vectorType = IntegerType 8
    vector = Int 8 $ fromIntegral 0

compileExpression env supply (Iridium.CallPrimFun PrimWrite [Left restList, Left resType, Left writeType, Right cursor, Right val]) name =
  -- TODO do something with the writeType. I think this should generally be a
  -- type that is primitive, i.e. an Int or a Char or something similar;
  -- assuming only PACKED_ or primitive types are allowed in PACKED_ types,
  -- this should be true?
  [ namePtr := Alloca vectorType Nothing 0 []
  , Do $ Store False (LocalReference (pointer vectorType) namePtr) (toOperand env val) Nothing 0 []
  -- Cast i64* to i8*, i.e. the int pointer into a void pointer
  , nameArray := BitCast (LocalReference (pointer vectorType) namePtr) voidPointer []
  -- The size starts in the first byte of the cursor
  , toName name := Call
    { tailCallKind = Nothing
    , callingConvention = C
    , returnAttributes = []
    , function = Right $ Builtins.writeCursor
    , arguments =
      [ (toOperand env cursor, [])
      -- This constant 8 is the size to write. Note that this should not be a
      -- constant; this is now hardcoded for 64-bit integers!
      -- TODO make sure that this takes the size of what is supposed to be
      -- written here. This would mostly be either Ints or Chars, since other
      -- data types are covered by other writes.
      , (ConstantOperand $ Int (fromIntegral $ targetWordSize $ envTarget env) $ fromIntegral $ 8, [])
      , (LocalReference voidPointer nameArray, [])
      ]
    , functionAttributes = []
    , metadata = []
    }
  ]
  where
    (namePtr, supply1) = freshName supply
    (nameArray, supply2) = freshName supply1
    (cursorSizeIndexPtr, supply3) = freshName supply2
    (cursorSizeIndex, supply4) = freshName supply3
    (cursorSizeStartPtr, supply5) = freshName supply4
    (cursorSizeStart, supply6) = freshName supply5
    -- We need a name for some instructions that I'd rather not give a name,
    -- but oh well.
    (x, supply7) = freshName supply6
    (y, _) = freshName supply7
    vectorType = IntegerType 64

-- TODO make sure that an end-pointer exists?
compileExpression env supply (Iridium.CallPrimFun PrimToEnd [Left resType, Right cursor]) name =
  [ namePtr := Alloca vectorType Nothing 0 []
  ]
  ++ cast supply env (toOperand env cursor) (toName name) t t
  where
    t = typeOfPrimFun (envTypeEnv env) PrimToEnd
    (namePtr, supply') = freshName supply
    (nameArray, _) = freshName supply'
    vectorType = IntegerType 32

compileExpression env supply (Iridium.CallPrimFun PrimFinish [Left restList, Right cursorStart, Right cursorEnd]) name =
  [ namePtr := Alloca vectorType Nothing 0 []
  , toName name := Call
    { tailCallKind = Nothing
    , callingConvention = C
    , returnAttributes = []
    , function = Right $ Builtins.finishCursor
    , arguments =
      [ (toOperand env cursorStart, [])
      , (toOperand env cursorEnd,   [])
      ]
    , functionAttributes = []
    , metadata = []
    }
  ]
  where
    (namePtr, supply') = freshName supply
    (nameArray, _) = freshName supply'
    vectorType = IntegerType 64

compileExpression env supply (Iridium.CallPrimFun PrimWriteLength [Left oldList, Left resType, Left restList, Right oldCursor, Right cursor]) name =
  [ toName name := Call
    { tailCallKind = Nothing
    , callingConvention = C
    , returnAttributes = []
    , function = Right $ Builtins.writeCursorSize
    , arguments =
      [ (toOperand env oldCursor, [])
      , (toOperand env cursor,    [])
      ]
    , functionAttributes = []
    , metadata = []
    }
  ]

compileExpression env supply e name = error $ "Cannot compile expression: " ++ show e ++ " with name " ++ show name
{-
compileExpression env supply (Iridium.PrimitiveExpr primName args) name = compile (envTarget env) supply [toOperand env arg | Right arg <- args] $ toName name
  where
    (Iridium.Primitive _ compile) = Iridium.findPrimitive primName
-}

compileEval :: Env -> NameSupply -> Operand -> Core.Type -> Name -> [Named Instruction]
compileEval env supply operand tp name
  | Core.typeIsStrict tp = copy env operand name tp
  | otherwise =
    [ namePtr := ExtractValue operand [0] []
    , nameIsWHNF := ExtractValue operand [1] []
    , nameIsWHNFExt := ZExt (LocalReference boolType nameIsWHNF) (envValueType env) []
    , nameWHNF := callEval (LocalReference voidPointer namePtr) (LocalReference (envValueType env) nameIsWHNFExt)
    ] ++ cast supply env (LocalReference voidPointer nameWHNF) name (Core.TStrict $ Core.TVar 0) (Core.typeToStrict tp) 
  where
    (namePtr, supply') = freshName supply
    (nameIsWHNF, supply'') = freshName supply'
    (nameIsWHNFExt, supply''') = freshName supply''
    (nameWHNF, _) = freshName supply'''

callEval :: Operand -> Operand -> Instruction
callEval pointer isWHNF =
  Call
  { tailCallKind = Nothing
  , callingConvention = Fast
  , returnAttributes = []
  , function = Right $ Builtins.eval
  , arguments = [(pointer, []), (isWHNF, [])]
  , functionAttributes = []
  , metadata = []
  }

data CaseAlt = CaseAlt Iridium.DataTypeConstructor ConstructorLayout Iridium.BlockName

toCaseAlt :: Env -> (Iridium.DataTypeConstructor, Iridium.BlockName) -> CaseAlt
toCaseAlt env (con@(Iridium.DataTypeConstructor conId _), block) = CaseAlt con layout block
  where
    layout = findMap conId (envConstructors env)

altIsInline :: CaseAlt -> Bool
altIsInline (CaseAlt _ (LayoutInline _) _) = True
altIsInline _ = False

compileCaseConstructorInline :: Env -> NameSupply -> Iridium.Variable -> [CaseAlt] -> Iridium.BlockName -> ([Named Instruction], Named Terminator)
compileCaseConstructorInline env supply var alts defaultBranch = ([nameInt := PtrToInt (toOperand env var) (envValueType env) []], (Do switch))
  where
    (nameInt, supply') = freshName supply
    switch :: Terminator
    switch = Switch (LocalReference (envValueType env) nameInt) (toName defaultBranch) (map altToDestination alts) []
    altToDestination :: CaseAlt -> (Constant, Name)
    altToDestination (CaseAlt (Iridium.DataTypeConstructor conId _) (LayoutInline tag) to)
      = (Int (fromIntegral $ targetWordSize $ envTarget env) (fromIntegral $ 2 * tag + 1), toName to)

compileCaseConstructorPointer :: Env -> NameSupply -> Iridium.Variable -> [CaseAlt] -> ([Named Instruction], Named Terminator)
compileCaseConstructorPointer env supply var alts = (instructions, (Do switch))
  where
    (defaultBranch, alts') = caseExtractMostFrequentBranch alts

    -- Cast the pointer to the type of the first constructor. It does not matter to which constructor we cast,
    -- as they all have the tag on the same position.
    CaseAlt _ (LayoutPointer structFirst) _ : _ = alts
    t = pointer $ structType env structFirst

    (supplyExtractTag, supply1) = splitNameSupply supply
    (nameCasted, supply2) = freshName supply1
    (nameTag, supply3) = freshName supply2

    instructions :: [Named Instruction]
    instructions =
      [ nameCasted := BitCast (toOperand env var) t [] ]
      ++ extractTag supply env (LocalReference t nameCasted) structFirst nameTag

    altToDestination :: CaseAlt -> (Constant, Name)
    altToDestination (CaseAlt (Iridium.DataTypeConstructor conId _) (LayoutPointer struct) to)
      = (Int (fromIntegral $ targetWordSize $ envTarget env) (fromIntegral $ tagValue struct), toName to)

    switch :: Terminator
    switch = Switch (LocalReference (envValueType env) nameTag) (toName defaultBranch) (map altToDestination alts) []

compileCaseConstructorCursor :: Env -> NameSupply -> Iridium.Variable -> [CaseAlt] -> ([Named Instruction], Named Terminator)
compileCaseConstructorCursor env supply var alts = (instructions, (Do switch))
  where
    (defaultBranch, alts') = caseExtractMostFrequentBranch alts

    (nameTagPtr, supply1) = freshName supply
    (nameTag,    supply2) = freshName supply1
    (nameTag64,  supply3) = freshName supply2

    instructions :: [Named Instruction]
    instructions =
      [ nameTagPtr := getElementPtr (toOperand env var) [0]
      , nameTag    := Load False (LocalReference voidPointer nameTagPtr) Nothing 0 []
      , nameTag64  := ZExt (LocalReference (IntegerType 8) nameTag) (IntegerType 64) []
      ]

    altToDestination :: CaseAlt -> (Constant, Name)
    altToDestination (CaseAlt (Iridium.DataTypeConstructor conId _) (LayoutPointer struct) to)
      = (Int (fromIntegral $ targetWordSize $ envTarget env) (fromIntegral $ tagValue struct), toName to)

    switch :: Terminator
    switch = Switch (LocalReference (envValueType env) nameTag64) (toName defaultBranch) (map altToDestination alts) []

caseExtractMostFrequentBranch :: [CaseAlt] -> (Iridium.BlockName, [CaseAlt])
caseExtractMostFrequentBranch alts = (defaultBranch, alts')
  where
     -- Find the branch that occurs most frequently
     defaultBranch = head $ maximumBy (compare `on` length) $ group $ sort $ map (\(CaseAlt _ _ block) -> block) alts
     -- Remove the default branch from the alts
     alts' = filter (\(CaseAlt _ _ block) -> defaultBranch /= block) alts
