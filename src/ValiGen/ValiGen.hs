{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}

module ValiGen.ValiGen
  where

import Test.QuickCheck
import qualified Test.QuickCheck.Gen as Gen

import Data.List
import Data.Profunctor
import Data.Bifunctor
import Data.Functor.Contravariant
import Control.Monad
import Control.Monad.State
import Control.Applicative

import Data.Coerce

import ValiGen.NF
import Data.Monoid (Any)

data ValiGen' a b c = ValiGen (a -> b -> Bool) (b -> Gen c)

instance Semigroup (ValiGen' a b c) where
  ValiGen f g <> ValiGen f' g' =
    ValiGen (\x y -> f x y || f' x y) (\x -> oneof [g x, g' x])

type ValiGen a = ValiGen' a a a

-- foldrVG :: (a -> b -> ValiGen b) -> b -> [a] -> ValiGen b
-- foldrVG _ z [] = ValiGen (const True) (pure z)

lengthComp :: Predicate Int -> Predicate [a]
lengthComp = undefined

type LengthPred a = [a] -> Int -> Bool
type LengthPred' a = Predicate ([a], Int)

-- We want something like this, even though we can't *quite* have it:
lpToGen :: LengthPred a -> Int -> [a]
lpToGen = undefined

lpValiGen :: LengthPred a -> ValiGen' [a] Int [a]
lpValiGen p = ValiGen p undefined

-- length is a monotone function... Maybe combining (>) with a monotone function, in general, gives some kind of generator?

gtValiGen :: Gen a -> ValiGen' [a] Int [a]
gtValiGen gen = ValiGen (\xs i -> length xs > i) (`replicateM` gen)

data Later a = Now a | Step (Later a)

mu :: (Enum a) => (a -> Bool) -> a -> Later a
mu f x
  | f x = Now x
  | otherwise = Step $ mu f (succ x)

-- genFilter (p . length) <$> replicateM n x
--    =
-- guard (p n) *> replicateM n x

-- genFilter p <$> choose (lo, hi)
--





-- anyFoldr :: (a -> b -> Any) ->

-- f = unfoldr

-- lengthComp :: (Int -> Bool) -> [a] -> Bool
-- lengthComp f = undefined

-- length . (> 2)  -->  \case [] -> False; (x:xs) -> case xs of [] -> False; (y:ys) -> case ys of [] -> False; (z:zs) -> True


-- genList ::

-- length' :: ValiGen a -> [a] -> ValiGen [a]
-- length' = undefined

data Prim a where
  OneOf :: [a] -> Prim a
  Range :: (a, a) -> Prim a
  deriving (Show)

data Check a where
  And :: Check a -> Check a -> Check a
  Or :: Check a -> Check a -> Check a
  Not :: Check a -> Check a
  Pred :: (a -> Bool) -> Check a -- TODO: Consider (a -> Check a) -> Check a
  BoolLit :: Bool -> Check a

instance Show (Check a) where
  show (And x y) = "And(" <> show x <> ", " <> show y <> ")"
  show (Or x y) = "Or(" <> show x <> ", " <> show y <> ")"
  show (Not x) = "Not(" <> show x <> ")"
  show (Pred _) = "<Pred>"
  show (BoolLit b) = show b

data Generate a where
  Prim :: Prim a -> Generate a
  Union :: Generate a -> Generate a -> Generate a
  Filter :: Check a -> Generate a -> Generate a
  deriving Show

instance Semigroup (Generate a) where
  (<>) = Union

toDNF :: Enum a => Check a -> DNF a
toDNF (Not x) = neg $ toDNF x
toDNF (Or x y) = dnfOr (toDNF x) (toDNF y)
toDNF (And x y) = dnfAnd (toDNF x) (toDNF y)
toDNF (BoolLit b) = DNF [Conj [boolToLiteral b]]
toDNF (Pred p) = DNF [Conj [L (APred p)]]

primToGen :: Enum a => Prim a -> Gen a
primToGen (OneOf xs) = elements xs
primToGen (Range p) = chooseEnum p

toGen :: Enum a => Check a -> Generate a -> Gen a
toGen p = dnfToGen . normalizeGenerate p

normalizeGenerate :: Enum a => Check a -> Generate a -> Generate a
normalizeGenerate p = normalizeGenerate' (toDNF p)

normalizeGenerate' :: Enum a => DNF a -> Generate a -> Generate a
normalizeGenerate' p (Prim x) = Prim $ filteredPrim p x
normalizeGenerate' p (Union x y) =
  Union (normalizeGenerate' p x) (normalizeGenerate' p y)
normalizeGenerate' p (Filter q x) =
  normalizeGenerate' (dnfAnd p (toDNF q)) x

dnfToGen :: Enum a => Generate a -> Gen a
dnfToGen (Prim (OneOf xs)) = elements xs
dnfToGen (Prim (Range p)) = chooseEnum p
dnfToGen (Union x y) = oneof [dnfToGen x, dnfToGen y]
dnfToGen (Filter p x) =
  dnfToGen x `suchThat` flip checkDNF (toDNF p)

-- dnfToGen p (Prim x) = primToGen $ filteredPrim p x
-- dnfToGen p (Union x y) = Union (dnfToGen p x) (dnfToGen p y)

filteredPrim :: DNF a -> Prim a -> Prim a
filteredPrim p (OneOf xs) = OneOf $ filter (`checkDNF` p) xs

-- data Prim a where
--   OneOf :: [a] -> Prim a
--   Range :: (a, a) -> Prim a

-- data Check v a where
--   CVar :: v -> Check v a
--   Prim :: Prim a -> Check v a
--   -- Check :: (a -> Bool) -> Check v a
--   And :: Check v a -> Check v a -> Check v a
--   Or :: Check v a -> Check v a -> Check v a
--   Not :: Check v a -> Check v a
--   Implies :: Check v a -> Check v a -> Check v a
--   BoolLit :: Bool -> Check v a

-- data Generate v a b where
--   GVar :: v -> Generate v a b
--   Filter :: Check v a -> Generate v a b -> Generate v a b
--   Pure :: Gen b -> Generate v a b
--   Union :: Generate v a b -> Generate v a b -> Generate v a b
--   Basic :: Check v a -> Gen b -> Generate v a b
--   Bind :: Generate v a b -> (b -> Generate v a c) -> Generate v a c

-- instance Semigroup (Generate v a b) where
--   (<>) = Union

-- -- TODO: Make a ValiGen type that works for both "modes"
-- type ValiGen' = Generate
-- type ValiGen v a = ValiGen' v a a

-- toDNF :: Enum a => Check Name a -> DNF a
-- toDNF (Not x) = neg $ toDNF x
-- toDNF (Or x y) = dnfOr (toDNF x) (toDNF y)
-- toDNF (And x y) = dnfAnd (toDNF x) (toDNF y)
-- toDNF (Implies x y) = toDNF (Or (Not x) y)
-- toDNF (CVar x) = DNF [Conj [L (AVar x)]]
-- toDNF (BoolLit b) = DNF [Conj [boolToLiteral b]]
-- toDNF (Prim x) = DNF [Conj [genToLiteral $ primToGen x]]

-- primToGen :: Enum a => Prim a -> Gen a
-- primToGen (OneOf xs) = elements xs
-- primToGen (Range p) = chooseEnum p

-- dnfToGenerate :: DNF a -> Generate Name a a
-- dnfToGenerate (DNF []) = error "dnfToGenerate: Argument has no clauses"
-- dnfToGenerate (DNF xs) =
--   foldr1 (<>) (map conjToGenerate xs)

-- toGenerate :: Enum a => Check Name a -> Generate Name a a
-- toGenerate = dnfToGenerate . toDNF

-- conjToGenerate :: Conj a -> Generate Name a a
-- conjToGenerate (Conj []) = error "conjToGenerate: Argument has no clauses"
-- conjToGenerate (Conj xs) =
--   foldr1 (<>) (map literalToGenerate xs)

-- literalToGenerate :: Literal (Atom a) -> Generate Name a a
-- literalToGenerate (L (AGen x)) = Pure x
-- literalToGenerate (L (AVar n)) = error $ "literalToGenerate: variable " ++ show n
-- literalToGenerate (L ATrue) = error "literalToGenerate: True"
-- literalToGenerate (Neg _) = error "literalToGenerate: Neg _"
