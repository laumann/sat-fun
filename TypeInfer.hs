
import qualified Data.Map as Map () -- for later...
import Data.List (intercalate)

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
  show (OTProduct ot1 ot2) = (show ot1) ++ " * " ++ (show ot2)
  show (OTFunc ot1 ot2)    = "(" ++ (show ot1) ++ " -> " ++ (show ot2) ++ ")"
  show (OTUniVar uv)       = show uv

instance Show UnificationVariable where
  show (UV i) = "(" ++ show i ++ ")"

univ :: Integer -> UnificationVariable
univ i = UV i

otUniv :: Integer -> OpenType -- (OTUniVar (UV i))
otUniv = OTUniVar . univ

-- A type substitution maps unification variables to (possibly open) types
type TypeSub = [(UnificationVariable, OpenType)]

showSubst sub = putStrLn $ "[" ++ showSubs sub ++ "]"
  where showSubs s = intercalate ", " $ [ show uv ++ " +> " ++ show ot  | (uv, ot) <- s ]

-- | Reflects the type 
data TypeConstraint = TC OpenType OpenType

(=*=) :: OpenType -> OpenType -> TypeConstraint
ot1 =*= ot2 = TC ot1 ot2

instance Show TypeConstraint where
  show (TC ot1 ot2) = show ot1 ++ " =*= " ++ show ot2

type TypeEnv = [TypeConstraint]

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

-- | UV(t) = the set of unification variables occuring in t
uV :: OpenType -> [OpenType]
uV t = undefined


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


tc = TC tType1 tType2