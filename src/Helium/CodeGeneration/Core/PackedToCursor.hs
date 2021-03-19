{-# LANGUAGE TupleSections #-}
{-| Module      :  PackedToCursor
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
import Data.Maybe
import Debug.Trace (trace)

import Text.PrettyPrint.Leijen hiding ((<$>))

--------------------------------------------------------------------------------
-- Defining some stuff that helps with the rest of the file
--------------------------------------------------------------------------------
type TypeChanges = [TypeChange] -- A list of function IDs with their new types
type TypeChange  = (Id, Type)

showTypeChanges :: TypeChanges -> String
showTypeChanges tcs = "[" ++ intercalate ", " (stc' <$> tcs) ++ "]"
  where
    stc' :: TypeChange -> String
    stc' (i, t) = "(" ++ show i ++ ", " ++ show (pretty t) ++ ")"

data TransformerHelper a
  = TH (   NameSupply
        -> TypeChanges
        -> (a, NameSupply, TypeChanges))

transformerResult :: NameSupply -> TransformerHelper a -> a
transformerResult supply (TH x) = case x supply [] of
  (y, _, _) -> y

instance Functor TransformerHelper where
  f `fmap` TH g = TH $ \supp tcs ->
    let (x, supp', tcs') = g supp tcs
    in  (f x, supp', tcs')

instance Applicative TransformerHelper where
  a <*> b = do
    a' <- a
    b' <- b
    return $ a' b'
  pure = return

instance Monad TransformerHelper where
  (TH x) >>= b = TH $ \supp tcs ->
    let (a, supp', tcs') = x supp tcs
        (TH b') = b a
    in  b' supp' tcs'
  return a = TH $ \supp tcs -> (a, supp, tcs)

thId :: TransformerHelper Id
thId = TH $ \supp tcs ->
  let (id, supp') = freshId supp
  in  (id, supp', tcs)

addTypeChange :: Type -> Id -> TransformerHelper ()
addTypeChange t i = TH $ \supp tcs ->
  ((), supp, (i, t) : tcs)

addTypeChangeIf :: (Type -> Bool) -> Type -> Id -> TransformerHelper ()
addTypeChangeIf p t i
  | p t       = addTypeChange t i
  | otherwise = return ()

getTypeChanges :: TransformerHelper TypeChanges
getTypeChanges = TH $ \supp tcs -> (tcs, supp, tcs)

setTypeChanges :: TypeChanges -> TransformerHelper ()
setTypeChanges tcs = TH $ \supp _ -> ((), supp, tcs)

-- Performs an action in the TransformerHelper monad, but disregards any
-- changes to the TypeChanges field.
containTypeChanges :: TransformerHelper a -> TransformerHelper a
containTypeChanges action = do
  tcs <- getTypeChanges
  res <- action
  setTypeChanges tcs
  return res

hasChangedType :: Id -> TransformerHelper Bool
hasChangedType = fmap isJust . getChangedType

getChangedType :: Id -> TransformerHelper (Maybe Type)
getChangedType i =
  do
    ftcs <- getTypeChanges
    return $ lookup i ftcs

--------------------------------------------------------------------------------
-- Begin of Packed to Cursor conversion
--------------------------------------------------------------------------------
corePackedToCursor :: NameSupply -> CoreModule -> CoreModule
corePackedToCursor supply mod@(Module name major minor imports decls) =
  transformerResult supply $
    do
      let env1  =  typeEnvForModule mod
      ds1       <- packedToCursor env1 decls
      let env2  =  typeEnvForModule $ Module name major minor imports ds1
      ds2       <- mapM (fixCursorCalls env2) ds1
      let env3  =  typeEnvForModule $ Module name major minor imports ds2
      tcs       <- getTypeChanges
      ds3       <- if null tcs then return ds2 else mapM (substAndApplyLambdas env3 ds2) ds2
      let ds4   =  removeLiftedConstructors ds3
      --ds3 <- return ds2
      --let ds4 = ds3
      return $ Module name major minor imports ds4

--------------------------------------------------------------------------------
-- Start of functions to remove lifted constructors
--------------------------------------------------------------------------------
-- Removes all lifted constructors from the declaration. The lifted functions have some issues with thunk allocation that we want to remove...
-- TODO implement this using filter, it's so much better.
removeLiftedConstructors :: [CoreDecl] -> [CoreDecl]
removeLiftedConstructors [] = []
removeLiftedConstructors (d@(DeclValue name _ _ _ _ _) : ds)
  | "TreeTest.toPacked" `isPrefixOf` stringFromId name  = removeLiftedConstructors ds
  | otherwise                                           = d : removeLiftedConstructors ds
removeLiftedConstructors (d:ds) = d : removeLiftedConstructors ds

--------------------------------------------------------------------------------
-- Start of functions to substitute and apply lifted constuctors
--------------------------------------------------------------------------------
-- Steps in this function:
--  * Descend into each declaration
--  * Find calls to functions that have had their type changed
--    * Substitute these calls with the expression of the function
--    * Apply the resulting foralls and lambdas directly
-- This step is required to remove indirections and function pointers; these
-- function pointers would be saved in a thunk, and we can't have thunks
-- returning cursor values. However, these thunks _would_ return cursor values.
-- Performing this step should hopefully eliminate all occurences of this.
substAndApplyLambdas :: TypeEnvironment -> [CoreDecl] -> CoreDecl -> TransformerHelper CoreDecl
substAndApplyLambdas env decls d@(DeclValue name access mod ty expr customs) =
  (\e -> DeclValue name access mod ty e customs) . fst <$> substAndApplyLambdasInExpr env decls' expr
  where
    decls' = filter isDeclValue decls
substAndApplyLambdas _ _ d = return d

-- Returns the resultant expression, and whether the expression has been
-- changed in this context.
-- The context refers to whether the change that has been made needs to be
-- reflected in the containing expression. For instance, if a binding in a let
-- has been changed, that does not mean that any other part of the expression
-- needs to be changed, since it doesn't actually change the resulting value.
-- In this case, the Bool would be False.
substAndApplyLambdasInExpr :: TypeEnvironment -> [CoreDecl] -> Expr -> TransformerHelper (Expr, Bool)
substAndApplyLambdasInExpr env decls (Var i) =
  do
    t <- getChangedType i
    case t of
      Nothing -> return (Var i, False)
      _ -> do
        let x = fromMaybe (error $ "Can't find global value: " ++ stringFromId i) $ findIdInDecls i decls
        substX    <- substAndApplyLambdasInExpr env decls x
        newNameX  <- refreshNames $ fst substX
        return (newNameX, True)
  where
    findIdInDecls :: Id -> [CoreDecl] -> Maybe Expr
    findIdInDecls i [] = Nothing
    findIdInDecls i (DeclValue name access mod ty e customs : ds)
      | i == name = Just e
      | otherwise = findIdInDecls i ds
substAndApplyLambdasInExpr env decls (ApType fn ty) =
  do
    (fn', fnc) <- substAndApplyLambdasInExpr env decls fn
    if fnc
      then fmap (second (const True)) . substAndApplyLambdasInExpr env decls $ fromJust $ applyLambdaInExpr (ApType fn' ty)
      else return (ApType fn' ty, False)
substAndApplyLambdasInExpr env decls (Ap fn@(Let _ _) arg) =
  do
    (fn', fnc)    <- substAndApplyLambdasInExpr env decls fn
    (arg', argc)  <- substAndApplyLambdasInExpr env decls arg
    -- So... the lhs hasn't changed, but it DOES contain a static lambda. We need a better detection for the inner lambda...
    let res = Ap fn' arg'
    case applyLambdaInExpr res of
      Just x  -> substAndApplyLambdasInExpr env decls x
      _       -> return (res, False)
substAndApplyLambdasInExpr env decls (Ap fn arg) =
  do
    (fn', fnc)    <- substAndApplyLambdasInExpr env decls fn
    (arg', argc)  <- substAndApplyLambdasInExpr env decls arg
    let res = Ap fn' arg'
    case applyLambdaInExpr res of
      Just x  -> substAndApplyLambdasInExpr env decls x
      _       -> return (res, False)
substAndApplyLambdasInExpr env decls (Let bs e) =
  do
    (bs', _) <- substAndApplyLambdasInBinds env decls bs
    (e',  _) <- substAndApplyLambdasInExpr  env decls e
    --return $ (Let bs' e', False)
    let (inlinedE', ec) = inlineCursorFunctionLets env (Let bs' e')
    if ec
      then second (const True) <$> substAndApplyLambdasInExpr env decls inlinedE'
      else return (inlinedE', False)
substAndApplyLambdasInExpr env decls (Forall q k e) =
  do
    (e', ec) <- substAndApplyLambdasInExpr env decls e
    return (Forall q k e', False)
substAndApplyLambdasInExpr env decls (Lam s v e) =
  do
    (e', ec) <- substAndApplyLambdasInExpr env decls e
    return (Lam s v e', False)
substAndApplyLambdasInExpr env decls (Match i alts) = first (Match i) <$> substAndApplyLambdasInAlts env decls alts
substAndApplyLambdasInExpr _ _ p@(Prim _) = return (p, False)
substAndApplyLambdasInExpr _ _ c@(Con _) = return (c, False)
substAndApplyLambdasInExpr _ _ l@(Lit _) = return (l, False)
-- Keeping this here in case the Expr type gets extended
substAndApplyLambdasInExpr env decls e = error $ "Cannot substitute in expression: " ++ show (pretty e)

-- Takes an expression and renames all binds to a new, unique name.
refreshNames :: Expr -> TransformerHelper Expr
refreshNames e = fst <$> foldExpr
  ( ( \bs e ->    \xs -> do
        (bs', xs1) <- bs xs
        (e',  xs2) <- e  xs1
        return (Let bs' e', xs2)
    , \i as ->    \xs -> as xs >>= \(as', xs') -> return (Match i as', xs')
    , \fn arg ->  \xs -> do
        (fn',  xs1) <- fn xs
        (arg', xs2) <- arg xs1
        return (Ap fn' arg', xs2)
    , \fn ty  ->  \xs -> fn xs >>= \(fn', xs') -> return (ApType fn' ty, xs')
    , \s (Variable vId vTy) e -> \xs -> do
        i <- thId
        (e', xs') <- e $ (vId, i) : xs
        return (Lam s (Variable i vTy) e', xs')
    , \q k e ->   \xs -> e xs  >>= \(e',  xs') -> return (Forall q k e', xs')
    , \c ->       \xs -> return (Con c, xs)
    , \i ->       \xs -> return (Var $ fromMaybe i (lookup i xs), xs)
    , \l ->       \xs -> return (Lit l, xs)
    , \p ->       \xs -> return (Prim p, xs)
    )
  , ( \bs -> \xs -> first Rec <$> foldl bindsFolder (pure ([], xs)) bs -- TODO
    , \b  -> \xs -> first Strict <$> b xs
    , \b  -> \xs -> first NonRec <$> b xs
    )
  , ( \(Variable vId vTy) e -> \xs -> do
        i <- thId
        (e', xs') <- e $ (vId, i) : xs
        return (Bind (Variable i vTy) e', xs')
    )
  , ( \as  -> \xs -> foldl altsFolder (pure ([], xs)) as
    , \p e -> \xs -> e xs >>= \(e', xs') -> return (Alt p e', xs')
    )
  , ( PatCon
    , PatLit
    , PatDefault
    )
  )
  e []
  where
    bindsFolder :: TransformerHelper ([Bind], [(Id, Id)]) -> ([(Id, Id)] -> TransformerHelper (Bind, [(Id, Id)])) -> TransformerHelper ([Bind], [(Id, Id)])
    bindsFolder bs b = do
      (bs', vs) <- bs
      (b', vs') <- b vs
      return (b' : bs', vs')

    altsFolder :: TransformerHelper ([Alt], [(Id, Id)]) -> ([(Id, Id)] -> TransformerHelper (Alt, [(Id, Id)])) -> TransformerHelper ([Alt], [(Id, Id)])
    altsFolder as a = do
      (as', vs) <- as
      (a', vs') <- a vs
      return (a' : as', vs')

substAndApplyLambdasInAlts :: TypeEnvironment -> [CoreDecl] -> Alts -> TransformerHelper (Alts, Bool)
substAndApplyLambdasInAlts env decls alts = (, False) <$> mapM altFn alts
  where
    altFn :: Alt -> TransformerHelper Alt
    altFn (Alt pat e) = Alt pat . fst <$> substAndApplyLambdasInExpr env decls e

substAndApplyLambdasInBinds :: TypeEnvironment -> [CoreDecl] -> Binds -> TransformerHelper (Binds, Bool)
substAndApplyLambdasInBinds env decls (NonRec (Bind var e)) = first (NonRec . Bind var) <$> substAndApplyLambdasInExpr env decls e
substAndApplyLambdasInBinds env decls (Strict (Bind var e)) = first (Strict . Bind var) <$> substAndApplyLambdasInExpr env decls e

inlineCursorFunctionLets :: TypeEnvironment -> Expr -> (Expr, Bool)
inlineCursorFunctionLets env origExpr@(Let (NonRec (Bind v le)) e)
  | isCursorFunction env $ variableType v = (substituteIdForExpr (variableName v) le e, True)
  | otherwise = (origExpr, False)
inlineCursorFunctionLets env origExpr@(Let (Strict (Bind v le)) e)
  | isCursorFunction env $ variableType v = (substituteIdForExpr (variableName v) le e, True)
  | otherwise = (origExpr, False)

isCursorFunction :: TypeEnvironment -> Type -> Bool
isCursorFunction env t =
  let t' = typeReturnType env t
  in  typeIsCursor t' && typeIsFunction t

applyLambdaInExpr :: Expr -> Maybe Expr
applyLambdaInExpr (ApType e ty) = descendIntoForall (\q k e n -> substTy ty e n) e 0
  where
    descendIntoForall :: (Quantor -> Kind -> Expr -> Int -> Expr) -> Expr -> Int -> Maybe Expr
    descendIntoForall fn (Forall q k e) n = Just $ fn q k e n
    descendIntoForall fn (Let bs e)     n = Let bs <$> descendIntoForall fn e n
    descendIntoForall fn (Lam s v e)    n = Lam s v <$> descendIntoForall fn e n
    descendIntoForall fn _              n = Nothing

    -- Takes the type for substitution, and the expression in which to
    -- substitute, and returns a function taking an int, corresponding to the
    -- type variable index to substitute, and returning the resultant
    -- expression after substitution.
    substTy :: Type -> Expr -> (Int -> Expr)
    substTy ty = foldExpr
      ( ( \bs e   -> \x -> Let (bs x) (e x)
        , \i alts -> \x -> Match i (alts x)
        , \fn arg -> \x -> fn x `Ap` arg x
        -- Substitute any type var in this type for the type that this type var
        -- should be... Like when evaluating the ApType normally.
        , \fn ty' -> \x -> ApType (fn x) $ typeSubstitute x ty ty'
        , \s v e  -> \x -> Lam s (subVarType v x ty) $ e x
        , \q k e  -> \x -> Forall q k $ e (x + 1)
        , \c      -> \_ -> Con c
        , \i      -> \_ -> Var i
        , \l      -> \_ -> Lit l
        , \p      -> \_ -> Prim p
        )
      , ( \bs -> \x -> Rec    $ ($ x) <$> bs
        , \b  -> \x -> Strict $ b  x
        , \b  -> \x -> NonRec $ b  x
        )
      , ( \v e -> \x -> Bind (subVarType v x ty) (e x)
        )
      , ( \as -> \x -> fmap ($ x) as
        , \p e -> \x -> Alt (p x) (e x)
        )
      , ( \c ts ids -> \x -> PatCon c (typeSubstitute x ty <$> ts) ids
        , \l -> \_ -> PatLit l
        , const PatDefault
        )
      )

    subVarType :: Variable -> Int -> Type -> Variable
    subVarType (Variable i t) n newType = Variable i $ typeSubstitute n newType t
applyLambdaInExpr (Ap e arg) = descendIntoLam (\s v -> substituteIdForExpr (variableName v) arg) e
--applyLambdaInExpr (Ap (Lam s v e) arg) = subst (variableName v) arg $ e
  where
    descendIntoLam :: (Bool -> Variable -> Expr -> Expr) -> Expr -> Maybe Expr
    descendIntoLam fn (Forall q k e) = Forall q k <$> descendIntoLam fn e
    descendIntoLam fn (Let bs e)  = Let bs <$> descendIntoLam fn e
    descendIntoLam fn (Lam s v e) = Just $ fn s v e
    descendIntoLam _ _ = Nothing
applyLambdaInExpr e = error $ "Cannot apply anything other than ApType or Ap! Got:\n" ++ show (pretty e)

-- Substitute y for x in z
substituteIdForExpr :: Id -> Expr -> Expr -> Expr
substituteIdForExpr i new = foldExpr
  ( ( Let
    , Match
    , Ap
    , ApType
    , Lam
    , Forall
    , Con
    , \i' -> if i == i' then new else Var i'
    , Lit
    , Prim
    )
  , ( Rec
    , Strict
    , NonRec
    )
  , ( Bind
    )
  , ( id
    , Alt
    )
  , ( PatCon
    , PatLit
    , PatDefault
    )
  )
--------------------------------------------------------------------------------
-- Start of functions to fix calls to the changed lifted constructors
--------------------------------------------------------------------------------
-- Steps in this function:
--  * Descend into each declaration
--  * Find function calls to functions requiring a Needs cursor
--    * create a new variable name for this needs cursor, and remember its type
--    * When ascending back up, use this name in a new Let-bind!
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
    (e', eCursor) <- fixApplication env bCursor $ Ap a' b
    return (e', eCursor)
fixCursorCallsInExpr env e@(Var fn) inCursor = fixApplication env inCursor e

fixCursorCallsInExpr env e inCursor = return (e, inCursor)

fixApplication :: TypeEnvironment -> Maybe Expr -> Expr -> TransformerHelper (Expr, Maybe Expr)
fixApplication env inCursor x = do
  let fn = getAppliedFunction x
  a <- maybe (return Nothing) getChangedType fn
  --This trace is impossible now, because of some missing ApTypes in some cases. But, I'm leaving it here, just so I know that I might want to trace some stuff.
  --let b = trace (show . pretty $ typeOfCoreExpression env x) $ maybe (x, inCursor) (addCursorIfLastArg env inCursor x) a
  let b = trace (show . pretty $ a) $ maybe (x, inCursor) (addCursorIfLastArg env inCursor x) a
  return b

getAppliedFunction :: Expr -> Maybe Id
getAppliedFunction = foldExpr
  ( ( \_ _ -> Nothing
    , \_ _ -> error "We should never have to find an applied function inside a Match!"
    , \e _ -> e
    , \e _ -> e
    , \_ _ _ -> Nothing -- Lam, but we should never need this, since PACKED_ constructors are lifted to a function with a name
    , \_ _ _ -> error "We should never have to find an applied function inside a Forall!"
    , \_     -> Nothing -- Con, but PACKED_ constructors are lifted, so we don't need this
    , \i     -> Just i -- I know, this can be eta-reduced... this is just more descriptive in what's happening
    , \_     -> Nothing
    , \_     -> Nothing
    )
  , ( const Nothing
    , const Nothing
    , const Nothing
    )
  , ( \_ _ -> Nothing
    )
  , ( const Nothing
    , \_ _ -> Nothing
    )
  , ( \_ _ _ -> Nothing
    , const Nothing
    , Nothing
    )
  )

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
fixCursorCallsInBind env v e = do
    x <- maybe (return False) hasChangedType $ getAppliedFunction e
    if not x
      then return (v, e)
      else do
        iCursor <- thId
        (e', eCursor) <- trace "fixing cursor calls" $ fixCursorCallsInExpr env e (Just $ Var iCursor)
        let eResT = variableType v
        let innerCursorT = eResT
        let cursor    = ApType (Prim PrimNewCursor) $ innerCursorT
        let cFin      = (Prim PrimFinish) `ApType` eResT
        let callRes   = trace "Adding ApTypes" $ e' `addApTypes` [typeList [], eResT]
        let cType     = typeOfCoreExpression env cursor
        let v'        = Variable iCursor cType
        let fixedRes  = unifyCursorCallTypes (typeEnvAddVariable v' env) callRes
        let finishedCursor = (cFin `Ap` fixedRes) `Ap` Var iCursor
        let res = Let (NonRec $ Bind v' cursor) finishedCursor
        return $ (v, res)
  where
    addApTypes (Ap a b) ts = addApTypes a ts `Ap` b
    addApTypes e ts = foldl ApType e ts

    -- This is not a full unification algorithm! It just unifies the types that
    -- we need here, by changing the expressions around a bit; this should only
    -- be adding ApTypes, but that might change?
    unifyCursorCallTypes :: TypeEnvironment -> Expr -> Expr
    unifyCursorCallTypes env e | trace ("unifying with expr: " ++ show (pretty e)) False = undefined
    unifyCursorCallTypes env (Ap a b) =
      let a' = unifyCursorCallTypes env a
          tA = typeOfCoreExpression env a'
          TypeFun firstArg _ = tA
          b' = unifyExpressionWithType env b firstArg
          unifiedB = unifyCursorCallTypes env b'
      in  Ap a' unifiedB
    unifyCursorCallTypes _ e = e

    unifyExpressionWithType :: TypeEnvironment -> Expr -> Type -> Expr
    unifyExpressionWithType env (Ap a b) ty = unifyExpressionWithType env a ty `Ap` b
    unifyExpressionWithType env e ty
      | typeOfCoreExpression env e == ty = e
      | otherwise =
        let TypeFun _ (TCursor (TCursorNeeds args resT)) = ty
        in  (e `ApType` args) `ApType` resT

-- Crashes if you don't actually give a tuple type!
getTupleTypes :: Type -> (Type, Type)
getTupleTypes (TAp (TAp (TCon (TConTuple 2)) tl) tr) = (tl, tr)

--------------------------------------------------------------------------------
-- Start of declarations for turning a lifted constructor into a cursor function
--------------------------------------------------------------------------------
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
-- We contain the type changes here, since we don't want to pollute the global
-- scope with these changes. I think all names are globally unique, so it
-- wouldn't matter, but I'm not sure, and therefore, this is happening.
cursorfyExpr name env t e = containTypeChanges $ cursorfy' t e
  where
    cursorfy' ty expr = case (stringFromId name, hasPackedOutput ty) of
      -- TODO: this is hardcoded for the module TreeTest. Make sure it is not
      -- at some point.
      (n', Just xs) | "TreeTest.toPacked" `isPrefixOf` n' -> do
        x <- Forall (Quantor $ Just "restlist") KStar . Forall (Quantor $ Just "restype") KStar <$> addCursorsToExpr env ty expr xs
        let resType = typeOfCoreExpression env x
        return (x, resType)
      _ -> return (expr, t)

functionResult :: Type -> Type
functionResult (TypeFun _ x) = functionResult x
functionResult (TAp _ x) = functionResult x
functionResult x = x

addCursorsToExpr :: TypeEnvironment -> Type -> Expr -> [Type] -> TransformerHelper Expr
addCursorsToExpr env t (Lam strict v e) ts =
  do
    let innerEnv = typeEnvAddVariable v env
    e' <- addCursorsToExpr innerEnv t e ts
    v' <- updateVarType v
    return $ Lam strict v' e'
  where
    updateVarType v@(Variable name _) = maybe v (Variable name) <$> getChangedType name
addCursorsToExpr env t (Let bs e) ts =
  do
    let innerEnv = typeEnvAddBinds bs env
    e' <- addCursorsToExpr innerEnv t e ts
    bs' <- updateBinds bs
    return $ Let bs' e'
  where
    updateBinds (NonRec b) = NonRec <$> updateBind b
    updateBinds (Strict b) = Strict <$> updateBind b

    updateBind (Bind v e@(Var vId)) = do
      v' <- updateVarType v
      addTypeChange (variableType v') vId
      return $ Bind v' e
    updateBind b@(Bind v e) = trace ("Not updating bound expression: " ++ (show . pretty $ e)) $ do
      v' <- updateVarType v
      return $ Bind v' e

    updateVarType v@(Variable name _) = maybe v (Variable name) <$> getChangedType name
-- Add cursor types to an application of a constructor (so with arguments)
addCursorsToExpr env ty e@(Ap _ _) ts =
  do
    iNeeds <- thId
    x <- addCursorsToAp env ty e ts $ Var iNeeds
    case x of
      Nothing -> return e
      Just (expr, _, ctorType, newCursorId, _, _) -> do
        let originalOutput = functionResult ty
        let vNeeds = Variable iNeeds $ toNeedsCursor originalOutput (TVar 1) (TVar 0)
        let l1 = expr $ Var newCursorId
        let lam = Lam True vNeeds l1
        return $ lam
-- Add cursor types to a lone constructor (so without arguments)
addCursorsToExpr env ty e@(Con c@(ConId x)) ts =
  do
    iNeeds <- thId
    -- This pattern always matches, since we know `e` is a `Con (ConId _)`
    -- We need an irrefutable pattern just so that the compiler doesn't
    -- complain about any MonadFail stuff
    ~(Just (cursor, _, ctorType, newCursorId, _, _)) <- addCursorsToAp env ty e ts $ Var iNeeds
    let originalOutput = functionResult ty
    let vNeeds = Variable iNeeds $ toNeedsCursor originalOutput (TVar 1) (TVar 0)
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
-- 
-- We _could_ use the foldExpr function here, but I think it wouldn't make it any nicer.
addCursorsToAp :: TypeEnvironment -> Type -> Expr -> [Type] -> Expr -> TransformerHelper (Maybe (Expr -> Expr, Type, Type, Id, Type, Id))
addCursorsToAp env ty e@(Con x@(ConId _)) ts cursor =
  do
    origCursorId <- thId
    let cResT     = TVar 0
    let exprRes   = (((Prim $ PrimWriteCtor x) `ApType` (TVar 1)) `ApType` cResT) `Ap` cursor
    let exprResT  = typeNormalizeHead env $ typeOfCoreExpression env exprRes
    let exprLet   = Let (NonRec $ Bind (Variable origCursorId exprResT) exprRes)
    return $ Just (exprLet, exprResT, cResT, origCursorId, exprResT, origCursorId)
addCursorsToAp env ty e@(Ap fn arg) ts cursor =
  do
    x <- addCursorsToAp env ty fn ts cursor
    case x of
      Nothing -> return Nothing
      -- The current cursor expression, and the resulting type of the cursor. The resulting type `t` is often used.
      Just (prevExpr, t, cResT, prevCursorId', origCursorT, origCursorId')
        | isPackedType $ typeOfCoreExpression env arg -> do
          newCursorId <- thId
          let TCursor (TCursorNeeds cursorList _) = t
          let TCursor (TCursorNeeds originalList _) = origCursorT
          let TypeCons firstArg firstList@(TypeCons (TCon TConWriteLength) restList) = cursorList
          let writeLength   = ((Prim PrimWriteLength `ApType` originalList) `ApType` cResT) `ApType` restList
          let newCursorFn   = (writeLength `Ap` Var origCursorId') `Ap` (arg `Ap` Var prevCursorId')
          let newCursorT    = TCursor $ TCursorNeeds restList cResT
          let newCursorFnT  = TypeFun t $ TCursor $ TCursorNeeds firstList cResT
          let Var argId     = arg
          addTypeChange newCursorFnT argId
          let newCursorVar  = Variable newCursorId newCursorT
          let resExpr = prevExpr . Let (NonRec $ Bind newCursorVar newCursorFn)
          return $ Just (resExpr, newCursorT, cResT, newCursorId, origCursorT, origCursorId')
        | otherwise -> do
          newCursorId <- thId
          let TCursor (TCursorNeeds cursorList _) = t
          let TCursor (TCursorNeeds originalList _) = origCursorT
          let TypeCons firstArg firstList@(TypeCons (TCon TConWriteLength) restList) = cursorList
          let write = ((Prim PrimWrite `ApType` firstList) `ApType` cResT) `ApType` firstArg
          let writeLength = ((Prim PrimWriteLength `ApType` originalList) `ApType` cResT) `ApType` restList
          let writtenCursor = (write `Ap` Var prevCursorId') `Ap` arg
          let lengthWrittenCursor = (writeLength `Ap` Var origCursorId') `Ap` writtenCursor
          let newCursorT = typeNormalizeHead env $ typeOfCoreExpression env lengthWrittenCursor
          let newCursorVar = Variable newCursorId newCursorT
          let resExpr = prevExpr . Let (NonRec $ Bind newCursorVar lengthWrittenCursor)
          return $ Just (resExpr, newCursorT, cResT, newCursorId, origCursorT, origCursorId')
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

