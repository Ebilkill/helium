{-# LANGUAGE TupleSections #-}
{-| Module      :  Lift
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.Core.PackedToCursor (corePackedToCursor) where

import Lvm.Common.Id
import Lvm.Common.IdSet
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Core.Utils
import Helium.CodeGeneration.Core.TypeEnvironment
import Helium.CodeGeneration.Core.ReduceThunks (isCheap)

import Data.Bifunctor
import Data.List (isPrefixOf, intercalate)
import Debug.Trace (trace)

import Text.PrettyPrint.Leijen hiding ((<$>))

-- Defining some stuff that helps with the rest of the file
type FunctionTypeChanges = [FunctionTypeChange] -- A list of function IDs with their new types
type FunctionTypeChange  = (Id, Type)

showFunctionTypeChanges :: FunctionTypeChanges -> String
showFunctionTypeChanges ftcs = "[" ++ intercalate ", " (sftc' <$> ftcs) ++ "]"
  where
    sftc' :: FunctionTypeChange -> String
    sftc' (i, t) = "(" ++ show i ++ ", " ++ show (pretty t) ++ ")"

data TransformerHelper a
  = TH (   NameSupply
        -> FunctionTypeChanges
        -> (a, NameSupply, FunctionTypeChanges))

transformerResult :: NameSupply -> TransformerHelper a -> a
transformerResult supply (TH x) = case x supply [] of
  (y, _, _) -> y

instance Functor TransformerHelper where
  f `fmap` TH g = TH $ \supp ftcs ->
    let (x, supp', ftcs') = g supp ftcs
    in  (f x, supp', ftcs')

instance Applicative TransformerHelper where
  a <*> b = do
    a' <- a
    b' <- b
    return $ a' b'
  pure = return

instance Monad TransformerHelper where
  (TH x) >>= b = TH $ \supp ftcs ->
    let (a, supp', ftcs') = x supp ftcs
        (TH b') = b a
    in  b' supp' ftcs'
  return a = TH $ \supp ftcs -> (a, supp, ftcs)

thId :: TransformerHelper Id
thId = TH $ \supp ftcs ->
  let (id, supp') = freshId supp
  in  (id, supp', ftcs)

addFunctionTypeChange :: Type -> Id -> TransformerHelper ()
addFunctionTypeChange t i = TH $ \supp ftcs ->
  ((), supp, (i, t) : ftcs)

addTypeChangeIf :: (Type -> Bool) -> Type -> Id -> TransformerHelper ()
addTypeChangeIf p t i
  | p t       = addFunctionTypeChange t i
  | otherwise = return ()

getTypeChanges :: TransformerHelper FunctionTypeChanges
getTypeChanges = TH $ \supp ftcs -> (ftcs, supp, ftcs)

hasChangedType :: Id -> TransformerHelper Bool
hasChangedType i =
  do
    ftcs <- getTypeChanges
    return $ any (\x -> fst x == i) ftcs

-- Begin of Packed to Cursor conversion
corePackedToCursor :: NameSupply -> CoreModule -> CoreModule
corePackedToCursor supply mod@(Module name major minor imports decls) =
  transformerResult supply $
    do
      let env   =  typeEnvForModule mod
      ds'       <- packedToCursor env decls
      let env'  =  typeEnvForModule $ Module name major minor imports ds'
      ds''      <- mapM (fixCursorCalls env') ds'
      ftcs      <- getTypeChanges
      return $ Module name major minor imports ds''

-- Steps in this function:
--  * Descend into each declaration
--  * Find function calls to functions requiring a Needs cursor
--    * create a new variable name for this needs cursor, and remember its type
--    * When ascending back up, use this name in a new Let-bind!
--  * Probably do some stuff with calls to Has cursors as well
--    * We don't have these yet, so we can't really do anything about that.
fixCursorCalls :: TypeEnvironment -> CoreDecl -> TransformerHelper CoreDecl
fixCursorCalls env d@(DeclValue name access mod ty expr customs) =
  do
    newExpr <- fixCursorCallsInExpr env expr
    let newType = ty
    return $ DeclValue name access mod newType newExpr customs
fixCursorCalls _ d = return d

fixCursorCallsInExpr :: TypeEnvironment -> Expr -> TransformerHelper Expr
fixCursorCallsInExpr env (Lam strict v e) =
  do
    let innerEnv = typeEnvAddVariable v env
    e' <- fixCursorCallsInExpr innerEnv e
    return $ Lam strict v e'

fixCursorCallsInExpr env (Let bs@(NonRec (Bind v be)) e) =
  do
    bs' <- NonRec . uncurry Bind <$> fixCursorCallsInBind env v be
    e'  <- fixCursorCallsInExpr (typeEnvAddBinds bs' env) e
    return $ Let bs' e'

fixCursorCallsInExpr env (Let bs@(Rec [(Bind v be)]) e) =
  do
    bs' <- Rec . (:[]) . uncurry Bind <$> fixCursorCallsInBind env v be
    e'  <- fixCursorCallsInExpr (typeEnvAddBinds bs' env) e
    return $ Let bs' e'
fixCursorCallsInExpr env e = return e

fixCursorCallsInBind :: TypeEnvironment -> Variable -> Expr -> TransformerHelper (Variable, Expr)
fixCursorCallsInBind env v e
  -- | trace (show (variableName v) ++ "\n" ++ show (pretty e)) False = undefined
  | typeEqual env (typeOfCoreExpression env e) (variableType v)
    = return (v, e)
  | otherwise
    = do
      i <- thId
      let te        = typeOfCoreExpression env e
      let (TAp (TAp (TCon TConFun) _) eResT) = te
      let (innerCursorT, _) = getTupleTypes eResT
      let cursor    = ApType (Prim PrimNewCursor) $ innerCursorT
      let callRes   = Ap e cursor
      let callResT  = typeOfCoreExpression env callRes
      let cType     = typeOfCoreExpression env cursor
      let v'        = Variable i cType
      let (tl, tr)  = getTupleTypes callResT
      let fst_ = Ap (ApType (ApType (Var $ idFromString "Prelude.fst") tl) tr) callRes
      return $ (v, fst_)

-- Crashes if you don't actually give a tuple type!
getTupleTypes :: Type -> (Type, Type)
getTupleTypes (TAp (TAp (TCon (TConTuple 2)) tl) tr) = (tl, tr)

packedToCursor :: TypeEnvironment -> [CoreDecl] -> TransformerHelper [CoreDecl]
packedToCursor env = mapM (useCursorsInDecl env)

useCursorsInDecl :: TypeEnvironment -> CoreDecl -> TransformerHelper CoreDecl
useCursorsInDecl env d@(DeclValue name access mod ty expr customs) =
  do
    cExpr <- cursorfyExpr env ty expr
    let (newExpr, newType) = (cExpr, typeOfCoreExpression env cExpr)
    addTypeChangeIf (/=ty) newType name
    return $ DeclValue name access mod newType newExpr customs
useCursorsInDecl _ d = return d

cursorfyExpr :: TypeEnvironment -> Type -> Expr -> TransformerHelper Expr
cursorfyExpr env t e = cursorfy' t e
  where
    cursorfy' ty expr = case hasPackedOutput ty of
      Just xs -> addCursorsToExpr env ty expr xs
      Nothing -> return expr

functionResult :: Type -> Type
--functionResult x | trace (show $ pretty x) False = undefined
functionResult (TAp _ x) = x
functionResult x = x

addCursorsToExpr :: TypeEnvironment -> Type -> Expr -> [Type] -> TransformerHelper Expr
addCursorsToExpr env t (Lam strict v e) ts =
  do
    e' <- addCursorsToExpr env t e ts
    return $ Lam strict v e'
addCursorsToExpr env t (Let bs e) ts =
  do
    e' <- addCursorsToExpr env t e ts
    return $ Let bs e'
addCursorsToExpr env ty (Ap (Con x@(ConId _)) e) ts =
  do
    i1 <- thId
    i2 <- thId
    iNeeds <- thId
    let cFin  = ApType (Prim PrimFinish) $ TCon $ typeConFromString "TreeTest.PACKED_Int"
    let cEnd  = ApType (Prim PrimToEnd) $ TCon $ typeConFromString "TreeTest.PACKED_Int"
    let temp1 = (cFin `Ap` Var i2) `Ap` Var iNeeds
    let temp2 = cEnd `Ap` Var i2
    let e3  = Ap (Ap (ApType (ApType (Con (ConTuple 2)) (typeOfCoreExpression env temp1)) (typeOfCoreExpression env temp2)) temp1) temp2
    let e2  = Ap (Ap (ApType (ApType (ApType (Prim PrimWrite) $ TCon TConNil) $ TCon $ typeConFromString "TreeTest.PACKED_Int") $ TCon $ typeConFromString "Int") (Var i1)) e
    let t2  = typeNormalizeHead env $ typeOfCoreExpression env e2
    let l2  = Let (NonRec (Bind (Variable i2 t2) e2)) e3
    let ctorType = typeOfCoreExpression env $ Con x
    let e1  = Ap (ApType (Prim $ PrimWriteCtor x) $ typeList []) (Var iNeeds)
    let t1  = typeNormalizeHead env $ typeOfCoreExpression env e1
    let l1  = Let (NonRec (Bind (Variable i1 t1) e1)) l2
    let vNeeds  = Variable iNeeds
            $ toPackedIfIn ts
            $ functionResult
            $ ctorType
    let lam   = Lam True vNeeds l1
    return lam
  where
    toPackedIfIn ts t
      | t `elem` ts = toNeedsCursor t
      | otherwise   = t
addCursorsToExpr env ty expr ts = return . error . show $ pretty expr
{-
    ( foldr typeTransform (addHasCursor t ts) cursorTypes
    , useCursors . fst $ foldr exprTransform (e, supply) cursorTypes
    )
  where
    cursorTypes = map toNeedsCursor ts
    typeTransform next old = TAp (TAp (TCon TConFun) next) old
    exprTransform cTy (oldExp, supp) =
      let (i, supp') = first (flip Variable cTy) (freshId supp)
      in (Lam False i oldExp, supp')
-}

toCursorInDecls :: NameSupply -> [CoreDecl] -> [CoreDecl]
toCursorInDecls supply = map (toCursorInDecl supply)

toCursorInDecl :: NameSupply -> CoreDecl -> CoreDecl
toCursorInDecl supply d@(DeclValue name access mod ty expr customs)
  = DeclValue name access mod newType newExpr customs
    -- Or should we use d rather than remaking this type?
    where
      cursifiedDecl       = cursorfy supply ty expr
      (newType, newExpr)  = case cursifiedDecl of
        Just x  -> x
        Nothing -> (ty, expr)
toCursorInDecl _ d = d

-- This needs a better name. It converts a "normal" type to a type which has
-- cursor passing style.
cursorfy :: NameSupply -> Type -> Expr -> Maybe (Type, Expr)
cursorfy supply ty expr =
    let (ty', expr') = cursorfy' ty expr
    -- Only if the type exhibits cursors does the expression change
    in  if ty == ty' then Nothing else Just (ty', expr')
  where
    cursorfy' ty expr = case hasPackedOutput ty of
      Just xs -> addNeedsCursors supply ty expr xs
      Nothing -> (ty, expr)

-- Takes a type to add input cursors to, and the types for which to add cursors. Returns the transformed type.
addNeedsCursors :: NameSupply -> Type -> Expr -> [Type] -> (Type, Expr)
addNeedsCursors supply t e ts =
    ( foldr typeTransform (addHasCursor t ts) cursorTypes
    , useCursors . fst $ foldr exprTransform (e, supply) cursorTypes
    )
  where
    cursorTypes = map toNeedsCursor ts
    typeTransform next old = TAp (TAp (TCon TConFun) next) old
    exprTransform cTy (oldExp, supp) =
      let (i, supp') = first (flip Variable cTy) (freshId supp)
      in (Lam False i oldExp, supp')

-- Changes an expression that has cursors in its type to actually use the cursors, rather than the original constructors etc.
useCursors :: Expr -> Expr
useCursors (Let b e)          = Let b $ useCursors e
useCursors (Match x as)       = Match x as -- TODO: Recurse over the alts
useCursors (Ap e1 e2)         = useCursors e1 `Ap` useCursors e2
useCursors (ApType e1 t)      = error "Not sure what to do here. Should the type be changed as well?"
useCursors (Lam strict var e) = Lam strict var $ useCursors e
useCursors (Forall q k e)     = Forall q k $ useCursors e
useCursors (Con (ConId i))    =
  let conName = stringFromId i
  in  if conName == "PI"
    then Prim PrimWrite
    else Con (ConId i)
useCursors (Con c)            = Con c -- Probably a tuple constructor
useCursors (Var v)            = Var v -- Variables have changed types but I don't think we need to do anything with them
useCursors (Lit lit)          = Lit lit
useCursors (Prim p)           = Prim p -- This is what we want to create as well...

-- Transforms a packed type into a needs cursor for this type
toNeedsCursor :: Type -> Type
toNeedsCursor (TAp t1 t2) = typeApply t1  $ toNeedsCursor t2
toNeedsCursor (TStrict t) = TStrict $ toNeedsCursor t
toNeedsCursor (TCon t)    = TCursor $ tnc' t
  where
    -- This is currently a helper function so we can use it for different types
    -- later. This might be inlined later, we'll see
    tnc' t@(TConDataType id) = TCursorNeeds (typeList [TCon t]) (TCon t)

addHasCursor :: Type -> [Type] -> Type
addHasCursor t ts | t `elem` ts = toHasCursor t
addHasCursor (TAp t1 t2) ts = addHasCursor t1 ts `TAp` addHasCursor t2 ts
addHasCursor (TStrict t) ts = TStrict $ addHasCursor t ts
-- The main base case, at least for now.
-- If this hasn't triggered the first pattern, just leave it as-is.
addHasCursor (TCon t)    _  = TCon t

toHasCursor :: Type -> Type
toHasCursor (TAp t1 t2) = TAp t1  $ toHasCursor t2
toHasCursor (TStrict t) = TStrict $ toHasCursor t
toHasCursor (TCon t)    = TCursor $ thc' t
  where
    thc' t@(TConDataType id) = TCursorHas $ typeList [TCon t]

hasPackedOutput :: Type -> Maybe [Type]
hasPackedOutput (TAp _ t2) = hasPackedOutput t2
hasPackedOutput (TForall _ k t) = hasPackedOutput t -- TODO: Should we do anything with the kind?
hasPackedOutput (TStrict t) = map TStrict <$> hasPackedOutput t
hasPackedOutput (TVar x) = Nothing
hasPackedOutput t@(TCon tcon) = if hasPackedOutputTCon tcon then Just [t] else Nothing

hasPackedOutputTCon :: TypeConstant -> Bool
hasPackedOutputTCon (TConDataType id) = let name = stringFromId id
 in "PACKED_" `isPrefixOf` (last . wordsWhen (=='.') $ name)
hasPackedOutputTCon _ = False

usesPacked :: Type -> Bool
usesPacked (TAp t1 t2) = usesPacked t1 || usesPacked t2
usesPacked (TForall _ k t) = usesPacked t -- TODO: Should we do anything with the kind?
usesPacked (TStrict t) = usesPacked t
usesPacked (TVar x) = error "Should a ty var be assumed non-packed?"
usesPacked (TCon tcon) = usesPackedTCon tcon

-- This function is separate from `hasPackedOutputTCon` because the
-- implementation of both might change, but the usage of both is different.
usesPackedTCon :: TypeConstant -> Bool
usesPackedTCon (TConDataType id) = let name = stringFromId id
  in "PACKED_" `isPrefixOf` (last . wordsWhen (=='.') $ name)
usesPackedTCon _ = False

-- Taken from this stackoverflow answer:
-- https://stackoverflow.com/a/4981265
wordsWhen     :: (Char -> Bool) -> String -> [String]
wordsWhen p s =  case dropWhile p s of
                      "" -> []
                      s' -> w : wordsWhen p s''
                            where (w, s'') = break p s'

