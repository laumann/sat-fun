
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (intercalate)

import FUN

data OpenType = OTInt
              | OTBool
              | OTProduct OpenType OpenType
              | OTFunc OpenType OpenType
              | OTUniVar UnificationVariable
              deriving (Eq)

data UnificationVariable = UV Integer deriving (Eq,Ord)

instance Show OpenType where
  show (OTInt)             = "int"
  show (OTBool)            = "bool"
  show (OTProduct ot1 ot2) = (show ot1) ++ " × " ++ (show ot2)
  show (OTFunc ot1 ot2)    = (show ot1) ++ " → " ++ (show ot2)
  show (OTUniVar uv)       = show uv

instance Show UnificationVariable where
  show (UV i) = "(" ++ show i ++ ")"

univ :: Integer -> UnificationVariable
univ i = UV i

otUniv :: Integer -> OpenType -- (OTUniVar (UV i))
otUniv = OTUniVar . univ

-- | UV(t) = the set of unification variables occuring in t
uV :: OpenType -> S.Set UnificationVariable
uV t = collect t S.empty
  where collect (OTUniVar u1) uts = S.insert u1 uts
        collect (OTProduct ot1 ot2) uts = collect ot2 $ collect ot1 uts
        collect (OTFunc ot1 ot2) uts = collect ot2 $ collect ot1 uts
        collect _ uts = uts


-- A type substitution maps unification variables to (possibly open) types
type TypeSub = [(UnificationVariable, OpenType)]

showSubst sub = putStrLn $ "[" ++ showSubs sub ++ "]"
  where showSubs s = intercalate ", " $ [ show uv ++ " → " ++ show ot  | (uv, ot) <- s ]

-- | Reflects the type 
data TypeConstraint = TC OpenType OpenType

(=*=) :: OpenType -> OpenType -> TypeConstraint
ot1 =*= ot2 = TC ot1 ot2

instance Show TypeConstraint where
  show (TC ot1 ot2) = show ot1 ++ " =*= " ++ show ot2

-- | Constraint generation

type TypeEnv = M.Map Id OpenType

generateConstraints :: Term -> (OpenType, Integer, [TypeConstraint])
generateConstraints t = genCT M.empty 0 t

genCT :: TypeEnv -> Integer -> Term -> (OpenType, Integer, [TypeConstraint])
genCT tenv i (TVar id) = (tenv M.! id, i, [])
genCT tenv i (TBool _) = (OTBool, i, [])
genCT tenv i (TNum _)  = (OTInt, i, [])
genCT tenv i (TPlus t0 t1) =
  let (tau0, i'', c0) = genCT tenv i t0
      (tau1, i', c1)  = genCT tenv i'' t1
      constraints     = (tau0 =*= OTInt):(tau1 =*= OTInt):concat [c0,c1]
  in (OTInt, i', constraints)
genCT tenv i (TLeq t0 t1) =
  let (tau0, i'', c0) = genCT tenv i t0
      (tau1, i', c1)  = genCT tenv i'' t1
      constraints     = (tau0 =*= OTInt):(tau1 =*= OTInt):concat [c0,c1]
  in (OTBool, i', constraints)
genCT tenv i (TIf t0 t1 t2) =
  let (tau0, i'', c0)  = genCT tenv i t0
      (tau1, i''', c1) = genCT tenv i'' t1
      (tau2, i', c2)   = genCT tenv i''' t2
      constraints      = (tau0 =*= OTBool):(tau1 =*= tau2):concat [c0,c1,c2]
  in (tau1, i', constraints)
genCT tenv i (TPair t0 t1) =
  let (tau0, i'', c0) = genCT tenv i t0
      (tau1, i', c1)  = genCT tenv i'' t1
  in (OTProduct tau0 tau1, i', c0 ++ c1)
genCT tenv i (TFst t0) =
  let (tau0, i', c0) = genCT tenv (i+2) t0
      pairCT = OTProduct (otUniv i) (otUniv (i+1))
  in (otUniv i, i', (tau0 =*= pairCT):c0)
genCT tenv i (TSnd t0) =
  let (tau0, i', c0) = genCT tenv (i+2) t0
      pairCT = OTProduct (otUniv i) (otUniv (i+1))
  in (otUniv (i+1), i', (tau0 =*= pairCT):c0)
genCT tenv i (TLam id t0) =
  let (tau0, i', c0) = genCT (M.insert id (otUniv i) tenv) (i+1) t0
  in (OTFunc (otUniv i) tau0, i', c0)
genCT tenv i (TApp t0 t1) =
  let (tau0, i'', c0) = genCT tenv (i+1) t0
      (tau1, i', c1)  = genCT tenv i'' t1
      funCT = OTFunc tau1 (otUniv i)
      constraints = (tau0 =*= funCT):concat [c0, c1]
  in (otUniv i, i', constraints)
genCT tenv i (TLet id t0 t1) =
  let (tau0, i'', c0) = genCT tenv i t0
      (tau1, i', c1)  = genCT (M.insert id tau0 tenv) i'' t1
  in (tau1, i', c0 ++ c1)
genCT tenv i (TRec id t0) =
  let (tau0, i', c0) = genCT (M.insert id (otUniv i) tenv) (i+1) t0
  in (tau0, i', (otUniv i =*= tau0):c0)


-- | Test constructions
ctUntype = TPlus (TNum 3) (TBool True)
ctPairFst = TFst (TPair (TNum 1) (TBool True))
ctPairSnd = TSnd (TPair (TNum 1) (TBool True))

ctTermProg = TRec "f"
             (TLam "x"
              (TLam "y" (TIf (TLeq (TNum 0) (TVar "x")) (TVar "y")
                         (TApp (TApp (TVar "f") (TPlus (TVar "x") (TNum 1))) (TVar "y")))))


-- | Constraint solving
solveCT :: [TypeConstraint] -> TypeSub -- [(UnificationVariable, OpenType)]
solveCT constraints = solve constraints []
  where solve [] cs                                                  = cs
        solve (TC OTInt OTInt:cs) ts                                 = solve cs ts
        solve (TC OTBool OTBool:cs) ts                               = solve cs ts
        solve (TC (OTProduct ot1 ot2) (OTProduct ot1' ot2') : cs) ts = solve ((ot1 =*= ot1'):(ot2 =*= ot2'):cs) ts
        solve (TC (OTFunc ot1 ot2) (OTFunc ot1' ot2') : cs) ts       = solve ((ot1 =*= ot1'):(ot2 =*= ot2'):cs) ts
        
        solve (TC (OTUniVar u0) (OTUniVar u1):cs) ts =
          if u0 == u1
          then solve cs ts
          else solve (subConstraints u0 (OTUniVar u1) cs) ((u0, (OTUniVar u1)):ts)
               
        solve (TC (OTUniVar u0) tau:cs) ts = 
          let uvs = uV tau
          in if S.member u0 uvs
             then if tau == (OTUniVar u0)
                  then solve cs ts
                  else error $ show u0 ++ " occurs in UV(" ++ show tau ++ ")"
             else solve (subConstraints u0 tau cs) ((u0, tau):ts)
                  
        solve (TC tau (OTUniVar u0):cs) ts = 
          let uvs = uV tau
          in if S.member u0 uvs
             then if tau == (OTUniVar u0)
                  then solve cs ts
                  else error $ show u0 ++ " occurs in UV(" ++ show tau ++ ")"
             else solve (subConstraints u0 tau cs) ((u0, tau):ts)
        
        solve (TC ot1 ot2:cs) _ = cannotMatch (show ot1) (show ot2)
        
typeSubToTC :: TypeSub -> [TypeConstraint]
typeSubToTC []           = []
typeSubToTC ((uv,ot):ts) = TC (OTUniVar uv) ot : typeSubToTC ts

cannotMatch :: String -> String -> TypeSub
cannotMatch type1 type2 = error $ concat ["Cannot match type ", type1, " with ", type2, "."]

subConstraints :: UnificationVariable -> OpenType -> [TypeConstraint] -> [TypeConstraint]
subConstraints uv tau tcs = map (subConstraint uv tau) tcs

subConstraint :: UnificationVariable -> OpenType -> TypeConstraint -> TypeConstraint
subConstraint uv tau (TC tau0 tau1) = TC (subOpenType tau0 uv tau) (subOpenType tau1 uv tau)


subOpenType :: OpenType -> UnificationVariable -> OpenType -> OpenType
subOpenType (OTUniVar uv1) uv0 tau0        = if uv1 == uv0 then tau0 else (OTUniVar uv1)
subOpenType (OTProduct tau1 tau2) uv0 tau0 = OTProduct (subOpenType tau1 uv0 tau0) (subOpenType tau2 uv0 tau0)
subOpenType (OTFunc tau1 tau2) uv0 tau0    = OTFunc (subOpenType tau1 uv0 tau0) (subOpenType tau2 uv0 tau0)
subOpenType tau0 uv0 _                     = tau0


-- | Substituting open type variables using the given type substitution
-- 
-- There is a more generic way of applying substitutions (rather than just traversing the list)
-- We must exploit that all the unification variables in the TypeSub are distinct
applySubst :: OpenType -> TypeSub -> OpenType
applySubst t [] = t
applySubst t (ts:tss) = let (i, ot) = ts
                        in case t of
                          OTInt -> applySubst t tss
                          OTBool -> applySubst t tss
                          (OTProduct ot1 ot2) -> OTProduct (applySubst ot1 (ts:tss)) (applySubst ot2 (ts:tss))
                          (OTFunc ot1 ot2) -> OTFunc (applySubst ot1 (ts:tss)) (applySubst ot2 (ts:tss))
                          (OTUniVar j) -> if i == j
                                          then applySubst ot tss
                                          else applySubst (OTUniVar j) tss

applySubstTC :: TypeConstraint -> TypeSub -> TypeConstraint
applySubstTC (TC ot1 ot2) ts = TC (applySubst ot1 ts) (applySubst ot2 ts)


-- | TODO: Flattening; try 'applySubstTC (tType3 =*= tType4) tSubst1'
-- 
-- #=> (((1) -> bool) -> (4)) =*= ((1) -> (bool -> (4)))
-- 
-- which are identical except for the nesting.
solvesSubstTC :: TypeConstraint -> TypeSub -> Bool
solvesSubstTC tc ts = ot1 == ot2
  where (TC ot1 ot2) = applySubstTC tc ts

-- A type environment maps term variables (strings) to open types

-- | Testing
-- Try out: applySubst tType tSubst1
--          applySubst tType tSubst2
tType = OTFunc (otUniv 3) (OTProduct (otUniv 4) OTInt)

tSubst1 :: TypeSub
tSubst1 = [ (univ 2, OTBool)
          , (univ 3, (OTUniVar (univ 4)))
          ]

tSubst2 :: TypeSub
tSubst2 = [ (univ 2, OTBool)
          , (univ 3, (OTProduct OTInt OTInt))
          , (univ 4, (OTProduct OTInt OTInt))
          ]

tType1 = OTFunc (otUniv 3) OTBool
tType2 = OTFunc (otUniv 2) (otUniv 4)
tType3 = OTFunc (OTFunc (otUniv 1) (otUniv 2)) (otUniv 3)
tType4 = OTFunc (otUniv 1) (OTFunc (otUniv 2) (otUniv 3))

-- Try: uV funcy
funcy = (OTFunc (OTFunc (OTFunc (OTFunc (otUniv 1) (otUniv 2)) (otUniv 1)) (otUniv 3)) (otUniv 2))

tc = tType1 =*= tType2