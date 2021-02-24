module Helium.CodeGeneration.LLVM.CompileConstructor
  ( dataTypeType
  , constructorType
  , compileExtractFields
  , compileExtractCursorFields
  )
where

import qualified Data.Bits as Bits
import Data.Word(Word32)

import Lvm.Common.Id(Id, NameSupply, mapWithSupply, splitNameSupply)
import Lvm.Common.IdMap(findMap)
import Helium.CodeGeneration.LLVM.Env (Env(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.Struct
import Helium.CodeGeneration.LLVM.CompileStruct
import Helium.CodeGeneration.LLVM.CompileType
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import qualified Helium.CodeGeneration.LLVM.Builtins as Builtins
import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import LLVM.AST as AST
import LLVM.AST.CallingConvention
import LLVM.AST.Type as Type
import LLVM.AST.AddrSpace
import LLVM.AST.Operand
import qualified LLVM.AST.Constant as Constant

dataTypeType :: Env -> Iridium.Declaration Iridium.DataType -> [(Id, ConstructorLayout)] -> Type
dataTypeType env (Iridium.Declaration dataName _ _ _ _) layouts = case pointerLayouts of
  -- TODO: Use integer type for datatypes where all constructors have no arguments
  -- [] -> envValueType env
  [(conId, _)] -> pointer $ NamedTypeReference (toName conId)
  _ -> voidPointer
  where
    pointerLayouts = filter (isPointer . snd) layouts
    isPointer (LayoutPointer _) = True
    isPointer _ = False

constructorType :: Env -> ConstructorLayout -> Type
constructorType env (LayoutInline tag) = envValueType env
constructorType env (LayoutPointer struct) = structTypeNoAlias env struct
constructorType env (LayoutPacked tag) = cursorStructType

compileExtractFields :: Env -> NameSupply -> Operand -> Struct -> [Maybe Id] -> [Named Instruction]
compileExtractFields env supply reference struct vars
  = concat
    $ mapWithSupply (compileExtractField env reference struct) supply
    $ zip3 (fields struct) vars [0..]

compileExtractField :: Env -> Operand -> Struct -> NameSupply -> (StructField, Maybe Id, Int) -> [Named Instruction]
compileExtractField env reference struct supply (field, Just name, index) = extractField supply env reference struct index field $ toName name
compileExtractField _ _ _ _ (_, Nothing, _) = []

compileExtractCursorFields :: Env -> NameSupply -> Operand -> Struct -> [Maybe Id] -> [Named Instruction]
-- TODO hardcoded for fields of type i64!
compileExtractCursorFields env supply reference struct [] = [] -- Done all vars
compileExtractCursorFields env supply reference struct (v : vars) =
    varInsns ++
    [ nextVar       := getElementPtr reference [8]
    ]
    ++ compileExtractCursorFields env supply5 nextRef struct vars
  where
    (fieldIndexPtr, supply1)  = freshName supply
    (fieldIndex,    supply2)  = freshName supply1
    (fieldPtr,      supply3)  = freshName supply2
    (resPtr,        supply4)  = freshName supply3
    (nextVar,       supply5)  = freshName supply4
    (fieldsStart,   supply6)  = freshName supply5
    nextRef                   = LocalReference voidPointer nextVar
    -- The instructions needed to read this variable from the cursor. If the
    -- variable is Nothing, we assume we don't need to read it (since it is not
    -- used).
    varInsns = case v of
      Nothing   -> []
      Just var  ->
        let resName = toName var
              -- Get the pointer to the start of the field
        in  [ fieldIndexPtr := BitCast reference (pointer $ IntegerType 64) []
            , fieldIndex    := Load False (LocalReference (pointer $ IntegerType 64) fieldIndexPtr) Nothing 0 []
            -- skip over the rest of the lengths and go to the correct field from there.
            , fieldsStart   := getElementPtr reference [length vars * 8]
            , fieldPtr      := GetElementPtr False (LocalReference voidPointer fieldsStart) [LocalReference (IntegerType 64) fieldIndex] []
              -- Get the value of the field
            , resPtr        := BitCast (LocalReference voidPointer fieldPtr) (pointer $ IntegerType 64) []
            , resName       := Load False (LocalReference (pointer $ IntegerType 64) resPtr) Nothing 0 []
            ]
