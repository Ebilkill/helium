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
import Data.List (isPrefixOf)
import Debug.Trace (trace)

import Text.PrettyPrint.Leijen hiding ((<$>))

corePackedToCursor :: NameSupply -> CoreModule -> CoreModule
corePackedToCursor supply mod@(Module name major minor imports decls) = Module name major minor imports ds''
  where
    env             = typeEnvForModule mod
    -- TODO: make sure this gets the modified supply, or verify that it doesn't need the modified supply
    (ds', supply')  = (packedToCursor env supply decls, supply)
    env'            = typeEnvForModule $ Module name major minor imports ds'
    ds''            = fixCursorCalls env' supply' ds'

fixCursorCalls :: TypeEnvironment -> NameSupply -> [CoreDecl] -> [CoreDecl]
fixCursorCalls env supply ds = ds -- TODO: Do the thing

packedToCursor :: TypeEnvironment -> NameSupply -> [CoreDecl] -> [CoreDecl]
packedToCursor env supply = map (useCursorsInDecl env supply)

useCursorsInDecl :: TypeEnvironment -> NameSupply -> CoreDecl -> CoreDecl
useCursorsInDecl env supply d@(DeclValue name access mod ty expr customs)
  = DeclValue name access mod newType newExpr customs
    where
      cursifiedExpr = cursorfyExpr env supply ty expr
      (newExpr, newType) =
        (cursifiedExpr, typeOfCoreExpression env cursifiedExpr)
useCursorsInDecl _ _ d = d

cursorfyExpr :: TypeEnvironment -> NameSupply -> Type -> Expr -> Expr
cursorfyExpr env supply t e = cursorfy' t e
  where
    cursorfy' ty expr = case hasPackedOutput ty of
      Just xs -> addCursorsToExpr env supply ty expr xs
      Nothing -> expr

functionResult :: Type -> Type
--functionResult x | trace (show $ pretty x) False = undefined
functionResult (TAp _ x) = x
functionResult x = x

addCursorsToExpr :: TypeEnvironment -> NameSupply -> Type -> Expr -> [Type] -> Expr
addCursorsToExpr env s t (Lam strict v e) ts =
  Lam strict v $ addCursorsToExpr env s t e ts
addCursorsToExpr env s t (Let bs e) ts =
  let newE = addCursorsToExpr env s t e ts
  in  Let bs newE
addCursorsToExpr env supply ty (Ap (Con x@(ConId _)) e) ts =
  let
      vNeeds  = Variable iNeeds
              $ toPackedIfIn ts
              $ functionResult
              $ typeOfCoreExpression env
              $ Con x
      e1    = (Ap (Prim $ PrimWriteCtor x) (Var iNeeds))
      l1    = Let (NonRec (Bind (Variable i1 $ typeOfCoreExpression env e1) e1)) l2
      e2    = Ap (Ap (Prim PrimWrite) (Var i1)) e
      l2    = Let (NonRec (Bind (Variable i2 $ typeOfCoreExpression env e2) e2)) e3
      e3    = Ap (Ap (ApType (ApType (Con (ConTuple 2)) (typeOfCoreExpression env temp1)) (typeOfCoreExpression env temp2)) temp1) temp2
      temp1 = (Prim PrimFinish `Ap` Var i2) `Ap` Var iNeeds
      temp2 = Prim PrimToEnd `Ap` Var i2
      (i1, supp1)     = freshId supply
      (i2, supp2)     = freshId supp1
      (iNeeds, supp3) = freshId supp2
      lam   = Lam True vNeeds l1
  in  trace (show . pretty $ typeOfCoreExpression env e3) lam
  where
    toPackedIfIn ts t
      | t `elem` ts = toNeedsCursor t
      | otherwise   = t
addCursorsToExpr env supply ty expr ts = error . show $ pretty expr
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
toNeedsCursor (TCon t)    = TCon    $ tnc' t
  where
    -- This is currently a helper function so we can use it for different types
    -- later. This might be inlined later, we'll see
    tnc' t@(TConDataType id) = TConCursorNeeds [TCon t] (TCon t)

addHasCursor :: Type -> [Type] -> Type
addHasCursor t ts | t `elem` ts = toHasCursor t
addHasCursor (TAp t1 t2) ts = addHasCursor t1 ts `TAp` addHasCursor t2 ts
addHasCursor (TStrict t) ts = TStrict $ addHasCursor t ts
-- The main base case, at least for now.
-- If this hasn't triggered the first pattern, just leave it as-is.
addHasCursor (TCon t)    _  = TCon t

toHasCursor :: Type -> Type
toHasCursor (TAp t1 t2) = TAp t1 $ toHasCursor t2
toHasCursor (TStrict t) = TStrict $ toHasCursor t
toHasCursor (TCon t)    = TCon $ thc' t
  where
    thc' t@(TConDataType id) = TConCursorHas [TCon t]

hasPackedOutput :: Type -> Maybe [Type]
hasPackedOutput (TAp _ t2) = hasPackedOutput t2
hasPackedOutput (TForall _ k t) = hasPackedOutput t -- TODO: Should we do anything with the kind?
hasPackedOutput (TStrict t) = map TStrict <$> hasPackedOutput t
hasPackedOutput (TVar x) = error "Should a ty var be assumed non-packed?"
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

