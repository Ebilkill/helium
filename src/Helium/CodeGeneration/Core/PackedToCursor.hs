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
import Data.Maybe (maybe, fromJust)
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

getChangedType :: Id -> TransformerHelper (Maybe Type)
getChangedType i =
  do
    ftcs <- getTypeChanges
    return $ lookup i ftcs

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
    (newExpr, resCursor) <- fixCursorCallsInExpr env expr Nothing
    let newType = ty
    return $ DeclValue name access mod newType newExpr customs
fixCursorCalls _ d = return d

-- Takes the type environment, the original expression, and the current cursor
-- to use (which can be Nothing, in which case, a new cursor needs to be
-- generated).
-- It returns the new expression, as well as the cursor after calling that
-- expression. This cursor can then be `chained` into the next expression.
fixCursorCallsInExpr :: TypeEnvironment -> Expr -> Maybe Expr -> TransformerHelper (Expr, Maybe Expr)
fixCursorCallsInExpr env (Lam strict v e) inCursor =
  do
    let innerEnv = typeEnvAddVariable v env
    e' <- fixCursorCallsInExpr innerEnv e inCursor
    return $ first (Lam strict v) e'

fixCursorCallsInExpr env (Let bs@(NonRec (Bind v be)) e) inCursor =
  do
    bs' <- NonRec . uncurry Bind <$> fixCursorCallsInBind env v be
    e'  <- fixCursorCallsInExpr (typeEnvAddBinds bs' env) e inCursor
    return $ first (Let bs') e'

fixCursorCallsInExpr env (Let bs@(Rec [(Bind v be)]) e) inCursor =
  do
    bs' <- Rec . (:[]) . uncurry Bind <$> fixCursorCallsInBind env v be
    e'  <- fixCursorCallsInExpr (typeEnvAddBinds bs' env) e inCursor
    return $ first (Let bs') e'
fixCursorCallsInExpr env e@(Ap a b) inCursor = do
    (a', aCursor) <- fixCursorCallsInExpr env a inCursor
    (b', bCursor) <- fixCursorCallsInExpr env b aCursor
    (e', eCursor) <- fixApplication env bCursor $ Ap a' b'
    return (e', eCursor)
fixCursorCallsInExpr env e@(Var fn) inCursor = do
    e' <- fixApplication env inCursor e
    ct <- getChangedType fn
    return e'

fixCursorCallsInExpr env e inCursor = return (e, inCursor)

fixApplication :: TypeEnvironment -> Maybe Expr -> Expr -> TransformerHelper (Expr, Maybe Expr)
fixApplication env inCursor x = do
  let fn = getAppliedFunction x
  a <- maybe (return Nothing) getChangedType fn
  let b = trace (show . pretty $ typeOfCoreExpression env x) $ maybe (x, inCursor) (addCursorIfLastArg env inCursor x) a
  return b

getAppliedFunction :: Expr -> Maybe Id
getAppliedFunction (Ap a _)     = getAppliedFunction a
getAppliedFunction (ApType a _) = getAppliedFunction a
getAppliedFunction (Var i)      = Just i
getAppliedFunction (Prim p)     = Nothing
getAppliedFunction (Lit _)      = Nothing
getAppliedFunction (Con _)      = Nothing -- We do nothing here, since PACKED_ constructors are lifted
getAppliedFunction (Lam _ _ _)  = Nothing -- same as above, lifted to a function with a name
getAppliedFunction x = error $ "Tried getting the applied function, but got: " ++ (show . pretty $ x)

addCursorIfLastArg :: TypeEnvironment -> Maybe Expr -> Expr -> Type -> (Expr, Maybe Expr)
addCursorIfLastArg env inCursor ap (TForall _ _ t) = addCursorIfLastArg env inCursor ap t
addCursorIfLastArg env inCursor ap fn'@(TypeFun arg fn)
    -- We start with the inner function, since we added a cursor argument.
    -- That cursor argument has not been added at the `ap` side, since that's
    -- what we're taking care of here.
    | isLastArg fn ap = (ap `Ap` resCursor, Just resCursor)
    | otherwise = (ap, inCursor)
  where
    TCursor (TCursorNeeds restList resType) = typeOfCoreExpression env resCursor
    resCursor = case inCursor of
      Just cursor -> cursor
      _           -> Prim PrimNewCursor `ApType` TVar 0

isLastArg :: Type -> Expr -> Bool
isLastArg t e =
  let argc = functionArgumentCount t
      apc  = exprApCount e
  in  argc == apc

-- This exact function exists in CodeGeneration.LLVM.CompileBlock as well...
functionArgumentCount :: Type -> Int
functionArgumentCount (TypeFun fn fn') = functionArgumentCount fn' + 1
functionArgumentCount _ = 0

exprApCount :: Expr -> Int
exprApCount (Ap e _) = exprApCount e + 1
exprApCount _ = 0

fixCursorCallsInBind :: TypeEnvironment -> Variable -> Expr -> TransformerHelper (Variable, Expr)
fixCursorCallsInBind env v e
  -- | trace (show (variableName v) ++ "\n" ++ show (pretty e)) False = undefined
  | typeEqual env (typeOfCoreExpression env e) (variableType v)
    = return (v, e)
  | otherwise
    = do
      iCursor <- thId
      (e', eCursor) <- fixCursorCallsInExpr env e (Just $ Var iCursor)
      let te        = typeOfCoreExpression env e'
      let eResT     = variableType v
      --let (innerCursorT, _) = getTupleTypes eResT
      let innerCursorT = eResT
      let cursor    = ApType (Prim PrimNewCursor) $ innerCursorT
      let cFin      = (Prim PrimFinish) `ApType` eResT
      let callRes   = e' `addApTypes` [typeList [], eResT]
      let cType     = typeOfCoreExpression env cursor
      let v'        = Variable iCursor cType
      let finishedCursor = (cFin `Ap` callRes) `Ap` Var iCursor
      let res = Let (NonRec $ Bind v' cursor) finishedCursor
      return $ (v, res)
  where
    addApTypes (Ap a b) ts = addApTypes a ts `Ap` b
    addApTypes e        [] = e
    addApTypes e (t:ts)    = addApTypes (e `ApType` t) ts

-- Crashes if you don't actually give a tuple type!
getTupleTypes :: Type -> (Type, Type)
getTupleTypes (TAp (TAp (TCon (TConTuple 2)) tl) tr) = (tl, tr)

packedToCursor :: TypeEnvironment -> [CoreDecl] -> TransformerHelper [CoreDecl]
packedToCursor env = mapM (useCursorsInDecl env)

useCursorsInDecl :: TypeEnvironment -> CoreDecl -> TransformerHelper CoreDecl
useCursorsInDecl env d@(DeclValue name access mod ty expr customs) =
  do
    cExpr <- cursorfyExpr name env ty expr
    let (newExpr, newType) = cExpr
    addTypeChangeIf (/=ty) newType name
    return $ DeclValue name access mod newType newExpr customs
useCursorsInDecl _ d = return d

cursorfyExpr :: Id -> TypeEnvironment -> Type -> Expr -> TransformerHelper (Expr, Type)
cursorfyExpr name env t e = cursorfy' t e
  where
    cursorfy' ty expr = case (stringFromId name, hasPackedOutput ty) of
      -- TODO: this is hardcoded for the module TreeTest. Make sure it is not
      -- at some point.
      (n', Just xs) | "TreeTest.toPacked" `isPrefixOf` n' -> do
        x <- Forall (Quantor $ Just "restlist") KStar . Forall (Quantor $ Just "restype") KStar <$> addCursorsToExpr env ty expr xs
        let resType = typeOfCoreExpression env x
        return $ (x, resType)
      _ -> return (expr, t)

functionResult :: Type -> Type
functionResult (TypeFun _ x) = functionResult x
functionResult (TAp _ x) = functionResult x
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
-- Add cursor types to an application of a constructor (so with arguments)
addCursorsToExpr env ty e@(Ap _ _) ts =
  do
    iNeeds <- thId
    x <- addCursorsToAp env ty e ts $ Var iNeeds
    case x of
      Nothing -> return e
      Just (expr, _, ctorType, newCursorId, _, _) -> do
        -- TODO: Maybe it's a bit late to check whether we need to change the
        -- type after we change the expression...
        let vNeeds = Variable iNeeds $ toPackedIfIn ts $ ctorType
        -- The resulting expression is Expr -> Expr
        let cFin = ApType (Prim PrimFinish) ctorType
        let temp = (cFin `Ap` Var newCursorId) `Ap` Var iNeeds
        let l1 = expr $ Var iNeeds
        let lam = Lam True vNeeds l1
        return $ lam
  where
    toPackedIfIn ts t
      | t `elem` ts = toNeedsCursor t (typeList []) t
      | otherwise   = t
-- Add cursor types to a lone constructor (so without arguments)
addCursorsToExpr env ty e@(Con c@(ConId x)) ts =
  do
    iNeeds <- thId
    -- This pattern always matches, since we know `e` is a `Con (ConId _)`
    -- We need an irrefutable pattern just so that the compiler doesn't
    -- complain about any MonadFail stuff
    ~(Just (cursor, _, ctorType, newCursorId, _, _)) <- addCursorsToAp env ty e ts $ Var iNeeds
    let vNeeds = Variable iNeeds $ toNeedsCursor ctorType (TVar 1) (TVar 0)
    i1 <- thId
    let cFin = ApType (Prim PrimFinish) ctorType
    let cWriteLength = ((Prim PrimWriteLength `ApType` typeList [ctorType]) `ApType` ctorType) `ApType` typeList []
    let temp = (cFin `Ap` Var newCursorId) `Ap` Var iNeeds
    let l1 = cursor $ Var newCursorId
    let lam = Lam True vNeeds l1
    return lam
addCursorsToExpr env ty expr ts = return . error . show $ pretty expr

-- The function expects the same arguments as addCursorsToExpr, plus the
-- cursor, and one identifier. We need this cursor to keep track of the current
-- expression to form said cursor.
--
-- It returns Nothing when the application is not on a constructor; in this
-- case, nothing is supposed to change in the original expression either. If
-- the function returns Just, it returns a tuple of the current cursor building
-- expression (i.e. it adds the current constructor application to the cursor
-- argument, and returns that), and the resulting type of the cursor. The
-- latter information is required by the intended call site of this function,
-- `addCursorsToExpr`. The third value returned by this function, is the cursor
-- right after writing the constructor. This is used internally, in order to
-- make sure we can write the proper length values.
addCursorsToAp :: TypeEnvironment -> Type -> Expr -> [Type] -> Expr -> TransformerHelper (Maybe (Expr -> Expr, Type, Type, Id, Type, Id))
addCursorsToAp env ty e@(Con x@(ConId _)) ts cursor =
  do
    origCursorId <- thId
    let ctorType    = typeOfCoreExpression env e
    let ctorResT    = functionResult $ ctorType
    let exprRes     = (((Prim $ PrimWriteCtor x) `ApType` (TVar 1)) `ApType` TVar 0) `Ap` cursor
    let exprResT    = typeNormalizeHead env $ typeOfCoreExpression env exprRes
    let exprLet     = Let (NonRec $ Bind (Variable origCursorId exprResT) exprRes)
    return $ Just (exprLet, exprResT, ctorResT, origCursorId, exprResT, origCursorId)
addCursorsToAp env ty e@(Ap fn arg) ts cursor =
  do
    x <- addCursorsToAp env ty fn ts cursor
    case x of
      Nothing -> return Nothing
      -- The current cursor expression, and the resulting type of the cursor. The resulting type `t` is often used.
      Just (prevExpr, t, ctorResT, prevCursorId', origCursorT, origCursorId') -> do
        newCursorId <- thId
        let TCursor (TCursorNeeds cursorList _) = t
        let TCursor (TCursorNeeds originalList _) = origCursorT
        let TypeCons firstArg firstList@(TypeCons (TCon TConWriteLength) restList) = cursorList
        let write = ((Prim PrimWrite `ApType` firstList) `ApType` ctorResT) `ApType` firstArg
        let writeLength = ((Prim PrimWriteLength `ApType` originalList) `ApType` ctorResT) `ApType` restList
        let writtenCursor = (write `Ap` Var prevCursorId') `Ap` arg
        let lengthWrittenCursor = (writeLength `Ap` Var origCursorId') `Ap` writtenCursor
        let newCursorT = typeNormalizeHead env $ typeOfCoreExpression env lengthWrittenCursor
        let newCursorVar = Variable newCursorId newCursorT
        let resExpr = prevExpr . Let (NonRec $ Bind newCursorVar lengthWrittenCursor)
        return $ Just (resExpr, newCursorT, ctorResT, newCursorId, origCursorT, origCursorId')
addCursorsToAp _ _ _ _ cursor = return Nothing -- Not a constructor application, not a cursor.

-- Transforms a packed type into a needs cursor for this type. The resulting
-- type needs two more arguments: the type of the rest of the list, and the
-- type of the eventual result. The basic use would be to make these an empty
-- list and the same type as the first argument, respectively, but this way, it
-- is more flexible.
toNeedsCursor :: Type -> (Type -> Type -> Type)
toNeedsCursor (TAp t1 t2) = \rl rt -> typeApply t1 $ toNeedsCursor t2 rl rt
toNeedsCursor (TStrict t) = \rl rt -> TStrict $ toNeedsCursor t rl rt
toNeedsCursor (TCon t)    = \rl rt -> TCursor $ tnc' t rl rt
  where
    -- This is currently a helper function so we can use it for different types
    -- later. This might be inlined later, we'll see
    tnc' t@(TConDataType id) rl rt = TCursorNeeds (TypeCons (TCon t) rl) rt

hasPackedOutput :: Type -> Maybe [Type]
-- TVar in `hasPackedOutput`. Assuming non-packed, but need to verify whether this is correct!
hasPackedOutput (TVar _)   = Nothing
hasPackedOutput (TAp _ t2) = hasPackedOutput t2
hasPackedOutput (TForall _ k t) = hasPackedOutput t -- TODO: Should we do anything with the kind?
hasPackedOutput (TStrict t) = map TStrict <$> hasPackedOutput t
hasPackedOutput t@(TCon tcon) = if isPackedType t then Just [t] else Nothing

