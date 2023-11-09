-- |

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module ValiGen.Refine where

import Prelude hiding ((.), id)

import Control.Category

import Control.Lens
import Data.Data
import Control.Monad
import Control.Applicative

import Test.QuickCheck

import Data.Functor.Product
import GHC.Tc.Solver (InferMode)

-- | Adjoin a point to represent infinity and a point to represent negative infinity
data TwoPoint a
  = NegInf
  | Inf
  | TwoPoint a
  deriving (Show, Eq, Functor)

instance Ord a => Ord (TwoPoint a) where
  NegInf <= _ = True
  _ <= NegInf = False

  _ <= Inf = True
  Inf <= _ = False

  TwoPoint x <= TwoPoint y = x <= y

instance Applicative TwoPoint where
  pure = TwoPoint
  NegInf <*> _ = NegInf
  Inf <*> _ = Inf
  _ <*> NegInf = NegInf
  _ <*> Inf = Inf
  TwoPoint f <*> TwoPoint x = TwoPoint $ f x

instance Num a => Num (TwoPoint a) where
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  fromInteger = TwoPoint . fromInteger

  abs NegInf = Inf
  abs Inf = Inf
  abs (TwoPoint x) = TwoPoint $ abs x

  signum NegInf = -1
  signum Inf = 1
  signum (TwoPoint x) = TwoPoint $ signum x

  negate NegInf = Inf
  negate Inf = NegInf
  negate (TwoPoint x) = TwoPoint $ negate x

-- | Map NegInf and Inf to minBound and maxBound respectively
fromTwoPoint :: Bounded a => TwoPoint a -> a
fromTwoPoint NegInf = minBound
fromTwoPoint Inf = maxBound
fromTwoPoint (TwoPoint x) = x

-- unsafeFromTwoPoint :: TwoPoint a -> a
-- unsafeFromTwoPoint (TwoPoint x) = x
-- unsafeFromTwoPoint Inf = error $ "unsafeFromTwoPoint: Inf"
-- unsafeFromTwoPoint NegInf = error $ "unsafeFromTwoPoint: NegInf"

instance Bounded (TwoPoint a) where
  minBound = NegInf
  maxBound = Inf

data Invertible a b =
  Invertible
  { apply :: a -> b
  , applyInv :: b -> a
  }

instance Category Invertible where
  id = Invertible id id
  Invertible f1 g1 . Invertible f2 g2 =
    Invertible (f1 . f2) (g2 . g1)

data Refined domain a =
  Refined
  { refinedDomain :: domain
  , refinedMap :: Invertible a a
  }

class Refine domain a where
  refineGen :: Refined domain a -> Gen a

newtype Range a = Range (a, a)
  deriving (Show, Functor)

instance (Bounded a, Ord a) => Semigroup (Range a) where
  Range (x1, y1) <> Range (x2, y2)
    | x2 > y1 = mempty
    | otherwise = Range (max x1 x2, min y1 y2)

instance (Bounded a, Ord a) => Monoid (Range a) where
  mempty = Range (minBound, maxBound)

instance Refine (Range (TwoPoint Int)) Int where
  refineGen (Refined (Range p) f) =
    apply f
      <$> choose
           (bimap (applyInv f . fromTwoPoint) (applyInv f . fromTwoPoint) p)

refinedFromDomain :: domain -> Refined domain a
refinedFromDomain d = Refined d id

refinedFromMap :: Monoid domain => (a -> a) -> (a -> a) -> Refined domain a
refinedFromMap f g = Refined mempty $ Invertible f g

instance Semigroup domain => Semigroup (Refined domain a) where
  Refined x1 y1 <> Refined x2 y2 = Refined (x1 <> x2) (y1 . y2)

instance Monoid domain => Monoid (Refined domain a) where
  mempty = Refined mempty id

type RefinedInt = Refined (Range (TwoPoint Int)) Int
