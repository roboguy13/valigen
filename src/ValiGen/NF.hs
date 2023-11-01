-- |

module ValiGen.NF where

import Test.QuickCheck

type Name = String

data DNF a where
  DNF :: [Conj a] -> DNF a

unDNF :: DNF a -> [Conj a]
unDNF (DNF xs) = xs

data Conj a where
  Conj :: [Literal (Atom a)] -> Conj a

data CNF a where
  CNF :: [Disj a] -> CNF a

data Disj a where
  Disj :: [Literal (Atom a)] -> Disj a

data Atom a where
  -- AVar :: Name -> Atom a
  -- AGen :: Gen a -> Atom a
  APred :: (a -> Bool) -> Atom a
  ATrue :: Atom a

data Literal a where
  L :: a -> Literal a
  Neg :: a -> Literal a
  deriving (Functor)

checkDNF :: a -> DNF a -> Bool
checkDNF x (DNF xs) = any (checkConj x) xs

checkConj :: a -> Conj a -> Bool
checkConj x (Conj xs) = all (checkLiteral x) xs

checkLiteral :: a -> Literal (Atom a) -> Bool
checkLiteral _ (L ATrue) = True
checkLiteral _ (Neg ATrue) = False
checkLiteral x (L (APred p)) = p x
checkLiteral x (Neg (APred p)) = not (p x)

-- genToLiteral :: Gen a -> Literal (Atom a)
-- genToLiteral = L . AGen

boolToLiteral :: Bool -> Literal (Atom a)
boolToLiteral True = L ATrue
boolToLiteral False = Neg ATrue

dnfAnd :: DNF a -> DNF a -> DNF a
dnfAnd x y = neg (dnfOr (neg x) (neg y))

dnfOr :: DNF a -> DNF a -> DNF a
dnfOr (DNF xs) (DNF ys) = DNF (xs ++ ys)

negDNF :: DNF a -> CNF a
negDNF (DNF xs0) = CNF $ map go xs0
  where
    go (Conj ys) = Disj (map negLiteral ys)

negCNF :: CNF a -> DNF a
negCNF (CNF xs0) = DNF $ map go xs0
  where
    go (Disj ys) = Conj (map negLiteral ys)

neg :: DNF a -> DNF a
neg = negCNF . negDNF

negLiteral :: Literal a -> Literal a
negLiteral (L x) = Neg x
negLiteral (Neg x) = L x

-- instance Functor Atom where
--   fmap _ ATrue = ATrue
--   -- fmap _ (AVar x) = AVar x
--   -- fmap f (AGen x) = AGen $ fmap f x

-- mapAtom :: (a -> b) -> Atom a -> Atom b
-- mapAtom _ (AVar x) = AVar x
-- mapAtom f (AGen x) = AGen $ fmap f x

mapCnfLiterals :: (Literal (Atom a) -> Literal (Atom b)) -> CNF a -> CNF b
mapCnfLiterals f (CNF xs) = CNF $ map (mapDisjLiterals f) xs

mapDnfLiterals :: (Literal (Atom a) -> Literal (Atom b)) -> DNF a -> DNF b
mapDnfLiterals f (DNF xs) = DNF $ map (mapConjLiterals f) xs

mapDisjLiterals :: (Literal (Atom a) -> Literal (Atom b)) -> Disj a -> Disj b
mapDisjLiterals f (Disj xs) = Disj $ map f xs

mapConjLiterals :: (Literal (Atom a) -> Literal (Atom b)) -> Conj a -> Conj b
mapConjLiterals f (Conj xs) = Conj $ map f xs
