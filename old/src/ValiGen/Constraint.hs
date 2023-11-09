-- |

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module ValiGen.Constraint where

import Control.Lens
import Data.Data
import Control.Monad
import Control.Applicative

import Test.QuickCheck

import Data.Functor.Product

data Refined domain a =
  Refined
  { refinedDomain :: domain
  , refinedMap :: a -> a
  }

class Refine domain a where
  refineGen :: Refined domain a -> Gen a

newtype Range a = Range (a, a)

instance Refine (Range Int) Int where
  refineGen (Refined (Range p) f) = f <$> choose p

refinedFromDomain :: domain -> Refined domain a
refinedFromDomain d = Refined d id

refinedFromMap :: Monoid domain => (a -> a) -> Refined domain a
refinedFromMap = Refined mempty

instance Semigroup domain => Semigroup (Refined domain a) where
  Refined x1 y1 <> Refined x2 y2 = Refined (x1 <> x2) (y1 . y2)

instance Monoid domain => Monoid (Refined domain a) where
  mempty = Refined mempty id
