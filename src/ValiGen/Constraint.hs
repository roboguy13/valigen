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

refinedFromDomain :: domain -> Refined domain a
refinedFromDomain d = Refined d id

refinedFromMap :: Monoid domain => (a -> a) -> Refined domain a
refinedFromMap = Refined mempty

instance Semigroup domain => Semigroup (Refined domain a) where
  Refined x1 y1 <> Refined x2 y2 = Refined (x1 <> x2) (y1 . y2)

instance Monoid domain => Monoid (Refined domain a) where
  mempty = Refined mempty id

-- data GenOp domain a
--    = Refine (domain -> domain) -- These are things like (<10) and (>5). They can be merged with other refinable things
--    | Mappable (a -> a) -- These are things like even or, more generally, (k `divides`). They can be implemented as a map over *any* generator of the right type

-- class Domain a b where
--   generateFromDomain :: a -> Gen b
--   mapDomain :: (a -> a) -> b -> b

-- bimapDomain :: (Bifunctor p, Domain a a', Domain b b') => (a -> b) -> p a b -> p a' b'
-- bimapDomain f = bimap undefined _

-- instance (Domain a a', Domain b b') => Domain (a, b) (a', b') where
--   generateFromDomain (x, y) = liftA2 (,) (generateFromDomain x) (generateFromDomain y)
--   mapDomain f (x, y) =
--     let (x', y') = f undefined
--     in
--     (x', y')

-- instance (Semigroup b, Domain a b) => Semigroup (GenOp a b) where
--   Refine f <> Refine g = Refine (f <> g)
--   Mappable f <> Mappable g = Mappable (f . g)
--   Mappable f <> Refine g = Refine (domainLift f . g)
--   Refine f <> Mappable g = Refine (domainLift g . f)



-- instance (Domain f f' a, Domain g g' a) => Domain (Product f g) (Product f' g') a where
--   generateFromDomain (Pair x y) = liftA2 Pair (generateFromDomain x) (generateFromDomain y)

-- instance (Domain f a a', Domain g b b') => Domain (Product f g) a (a, b) where
--   generateFromDomain (Pair x y) = _ --liftA2 (,) (generateFromDomain x) (generateFromDomain y)

-- class Functor domain => Domain f domain where
--   embed :: f a -> domain a
--   project :: domain a -> f a
--   generateFromDomain :: domain a -> Gen (f a)
--   domainLift :: (f a -> f b) -> domain a -> domain b
--   -- domainAp :: f (a -> b) -> domain a -> domain b

-- instance (Domain f domainF, Domain g domainG) => Domain (Product f g) (Product domainF domainG) where
--   embed (Pair x y) = Pair (embed x) (embed y)
--   project (Pair x y) = Pair (project x) (project y)
--   generateFromDomain (Pair x y) = liftA2 Pair (generateFromDomain x) (generateFromDomain y)
--   domainLift f (Pair x y) = _ f x y
--   -- domainAp (Pair f g) (Pair x y) = Pair (domainAp f x) (domainAp g y)

-- -- domainLift :: Domain f domain => (f a -> f b) -> domain a -> domain b
-- -- domainLift f = embed . f . project

-- instance (Semigroup (domain a), Domain f domain) => Semigroup (GenOp (domain a) (f a)) where
--   Refine f <> Refine g = Refine (f <> g)
--   Mappable f <> Mappable g = Mappable (f . g)
--   Mappable f <> Refine g = Refine (domainLift f . g)
--   Refine f <> Mappable g = Refine (domainLift g . f)




-- class Domain a domain where -- | domain -> a where
--   embed :: a -> domain
--   generateFromDomain :: domain -> Gen a
--   domainMap :: (a -> a) -> domain -> domain

-- instance (Semigroup domain, Domain a domain) => Semigroup (GenOp domain a) where
--   Refine f <> Refine g = Refine (f <> g)
--   Mappable f <> Mappable g = Mappable (f . g)
--   Mappable f <> Refine g = Refine (domainMap f . g)
--   Refine f <> Mappable g = Refine (domainMap g . f)

-- instance (Domain a domainA, Domain b domainB) => Domain (a, b) (domainA, domainB) where
--   embed (x, y) = (embed x, embed y)
--   generateFromDomain (x, y) = liftA2 (,) (generateFromDomain x) (generateFromDomain y)
--   domainMap f (x, y) = _ --(domainMap f x, domainMap f y)




-- data Dependency t a
--   = DepVar a
--   | DepApp t [Dependency t a]
--   deriving (Data)

-- instance (Data t, Data a) => Plated (Dependency t a)

-- data Ct t a b =
--   Ct
--   { _ctDependencies :: [Dependency t a]
--   , _ctVerify :: b -> Bool
--   , _ctGen :: Gen b
--   }

-- makeLenses ''Ct

-- subDependencies :: (Data t, Data a) => Dependency t a -> [Dependency t a]
-- subDependencies = universe

-- getAllDependencies :: (Data t, Data a) => Ct t a b -> [Dependency t a]
-- getAllDependencies = subDependencies <=< view ctDependencies
