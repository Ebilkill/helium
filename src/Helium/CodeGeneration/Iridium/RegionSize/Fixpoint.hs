module Helium.CodeGeneration.Iridium.RegionSize.Fixpoint
where

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Sorting
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Evaluate

-- TODO: Do a monotone-framework style iterate-when-depency chagned thing

solveFixpoints :: Annotation -> Annotation
solveFixpoints = fillTop . eval . foldAnnAlg fixAlg
    where fixAlg = idAnnAlg {
        aFix = \_ s as -> solveFixpoint s as
    }

-- | Solve a group of fixpoints
solveFixpoint :: Sort -> [Annotation] -> Annotation
solveFixpoint s fixes = 
        let bot = ABot s
        in iterate 0 bot fixes
    where iterate :: Int -> Annotation -> [Annotation] -> Annotation
          iterate 3 state fs = ATop s []
          iterate n  state fs = 
              let res = solveFix state SortUnit <$> fs
              in if ATuple res == state 
                 then ATuple res
                 else iterate (n+1) (ATuple res) fs

-- | Solve a fixpoint
solveFix :: Annotation -- ^ The state
         -> Sort       -- ^ Argument sort
         -> Annotation -- ^ The fixpoint
         -> Annotation
solveFix x s fix = 
    let isFixpoint = countFixBinds fix > 0
    in if not isFixpoint
       then annStrengthen fix -- TODO: annStrengthen May have to be moved
       else eval $ AApl (ALam s fix) x

-- | Count usages of a variable
countFixBinds :: Annotation -> Int
countFixBinds = foldAnnAlgN 0 countAlg
    where countAlg = AnnAlg {
        aVar    = \d idx -> if d == idx then 1 else 0,
        aReg    = \_ _   -> 0,
        aLam    = \_ _ a -> a,
        aApl    = \_ a b -> a + b,
        aConstr = \_ _   -> 0,
        aUnit   = \_     -> 0,
        aTuple  = \_ as  -> sum as,
        aProj   = \_ _ a -> a,
        aAdd    = \_ a b -> a + b,
        aMinus  = \_ a _ -> a,
        aJoin   = \_ a b -> a + b,
        aQuant  = \_ a   -> a,
        aInstn  = \_ a _ -> a,
        aTop    = \_ _ _ -> 0, -- TODO: Count rec references in top?
        aBot    = \_ _   -> 0,
        aFix    = \_ _ a -> sum a   
    }

-- | Fill top with local variables in scope
fillTop :: Annotation -> Annotation
fillTop = go []
    where go scope (ATop  s []) = ATop s scope
          go scope (ALam   s a) = ALam s $ go (AVar 0 : (weakenScope <$> scope)) a  
          go scope (ATuple  as) = ATuple $ go scope <$> as
          go scope (AProj  i a) = AProj i $ go scope a 
          go scope (AApl   a b) = AApl   (go scope a) (go scope b) 
          go scope (AAdd   a b) = AAdd   (go scope a) (go scope b)  
          go scope (AMinus a r) = AMinus (go scope a) r
          go scope (AJoin  a b) = AJoin  (go scope a) (go scope b)
          go scope (AQuant a  ) = AQuant (go scope a)
          go scope (AInstn a t) = AInstn (go scope a) t
          go scope (AFix   s v) = AFix s $ go scope <$> v
          go scope ann = ann

          weakenScope :: Annotation -> Annotation
          weakenScope (AVar i) = AVar $ i + 1
          weakenScope a        = a