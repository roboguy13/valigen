-- |

{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}

module ValiGen.Boolean
  -- (EventuallyTrue
  -- ,EventuallyFalse
  -- ,BoundedPred
  -- ,CoBoundedPred
  -- ,Alternating
  -- ,Unrestricted

  -- ,Boolean (..)

  -- ,getBoundaryET
  -- ,getBoundaryEF
  -- ,getRegion
  -- ,getCoRegion
  -- ,getNextTrue
  -- ,getNextFalse

  -- ,unrestricted
  -- ,lt, le, gt, ge, eq
  -- ,bounded
  -- ,cobounded
  -- )
  where

import Data.Functor.Contravariant
import Data.Coerce
import Control.Applicative

-- | exists n. forall x > n. p x
data EventuallyTrue a = EventuallyTrue (a -> Bool) a

-- | exists n. forall x > n. !(p x)
data EventuallyFalse a = EventuallyFalse (a -> Bool) a

-- | It's going to be False, then it will be True for a while and finally it will be False forever
-- For example: \x -> x > 2 && x < 10
-- It might also *always* be False (this is a sort of degenerate case).
--
-- exists m n. (forall m < x < n. p x) /\ (forall x <= m. !(p x)) /\ (forall x >= n. !(p x))
data BoundedPred a = BoundedPred (a -> Bool) (Maybe (a, a)) -- TODO: Should this be [] instead of Maybe?

-- | Contrast with `BoundedPred`. An example of `CoBoundedPred` is \x -> x <= 2 || x >= 10
data CoBoundedPred a = CoBoundedPred (a -> Bool) (Maybe (a, a)) -- NOTE: This has the region where it is *False*

-- | Example: \x -> x `mod` 5 == 0
-- At any point, there is always another True. Also, there is always another False.
--
-- (forall n. p n -> exists m > n. p m) /\ (forall n. !(p n) -> exists m > n. !(p m))
newtype Alternating a = Alternating (a -> Bool)
  deriving Contravariant via Predicate

newtype Unrestricted a = Unrestricted (a -> Bool)
  deriving Contravariant via Predicate

getBoundaryET :: EventuallyTrue a -> a
getBoundaryET (EventuallyTrue _ x) = x

getBoundaryEF :: EventuallyFalse a -> a
getBoundaryEF = getBoundaryET . notB

getRegion :: BoundedPred a -> Maybe (a, a)
getRegion (BoundedPred _ r) = r

getCoRegion :: CoBoundedPred a -> Maybe (a, a)
getCoRegion = getRegion . notB

getNextTrue :: Alternating a -> a -> a
getNextTrue = undefined

getNextFalse :: Alternating a -> a -> a
getNextFalse alt = getNextTrue (notB alt)

regionIntersect :: Ord a => Maybe (a, a) -> Maybe (a, a) -> Maybe (a, a)
regionIntersect _ Nothing = Nothing
regionIntersect Nothing _ = Nothing
regionIntersect (Just (px, py)) (Just (qx, qy))
  | py < qx = Nothing
  | otherwise = Just (max px qx, min py qy)

regionUnion :: Ord a => Maybe (a, a) -> Maybe (a, a) -> Maybe (a, a)
regionUnion p Nothing = p
regionUnion Nothing q = q
regionUnion (Just (px, py)) (Just (qx, qy))
  | qx > py = Nothing
  | otherwise = Just (min px qx, max py qy)

class Boolean f g | f -> g where
  (.&&) :: Ord a => f a -> f a -> f a
  (.||) :: Ord a => f a -> f a -> f a
  notB :: f a -> g a
  unrestrict :: f a -> Unrestricted a

instance Boolean EventuallyTrue EventuallyFalse where
  EventuallyTrue f x .&& EventuallyTrue g y = EventuallyTrue (liftA2 (&&) f g) (max x y)
  EventuallyTrue f x .|| EventuallyTrue g y = EventuallyTrue (liftA2 (||) f g) (min x y)
  notB (EventuallyTrue f x) = EventuallyFalse (not . f) x
  unrestrict (EventuallyTrue f _) = Unrestricted f

instance Boolean EventuallyFalse EventuallyTrue where
  EventuallyFalse f x .&& EventuallyFalse g y = EventuallyFalse (liftA2 (&&) f g) (min x y)
  EventuallyFalse f x .|| EventuallyFalse g y = EventuallyFalse (liftA2 (||) f g) (max x y)
  notB (EventuallyFalse f x) = EventuallyTrue (not . f) x
  unrestrict (EventuallyFalse f _) = Unrestricted f

instance Boolean BoundedPred CoBoundedPred where
  BoundedPred f x .&& BoundedPred g y = BoundedPred (liftA2 (&&) f g) (regionIntersect x y)
  BoundedPred f x .|| BoundedPred g y = BoundedPred (liftA2 (||) f g) (regionUnion x y)
  notB (BoundedPred f x) = CoBoundedPred (not . f) x
  unrestrict (BoundedPred f _) = Unrestricted f

instance Boolean CoBoundedPred BoundedPred where
  CoBoundedPred f x .&& CoBoundedPred g y = CoBoundedPred (liftA2 (&&) f g) (regionUnion x y)
  CoBoundedPred f x .|| CoBoundedPred g y = CoBoundedPred (liftA2 (||) f g) (regionIntersect x y)
  notB (CoBoundedPred f x) = BoundedPred (not . f) x
  unrestrict (CoBoundedPred f _) = Unrestricted f

-- instance Boolean Alternating Alternating where
--   Alternating f .&& Alternating g = Alternating (liftA2 (&&) f g)
--   Alternating f .|| Alternating g = Alternating (liftA2 (||) f g)
--   notB (Alternating f) = Alternating (not . f)
--   unrestrict = coerce

-- instance Boolean Unrestricted Unrestricted where
--   Unrestricted f .&& Unrestricted g = Unrestricted (liftA2 (&&) f g)
--   Unrestricted f .|| Unrestricted g = Unrestricted (liftA2 (||) f g)
--   notB (Unrestricted f) = Unrestricted (not . f)
--   unrestrict = id

-- unrestricted :: (a -> Bool) -> Unrestricted a
-- unrestricted = Unrestricted

-- lt :: Ord a => a -> EventuallyFalse a
-- lt x = EventuallyFalse (< x)

-- le :: Ord a => a -> EventuallyFalse a
-- le x = EventuallyFalse (<= x)

-- gt :: Ord a => a -> EventuallyTrue a
-- gt x = EventuallyTrue (> x)

-- ge :: Ord a => a -> EventuallyTrue a
-- ge x = EventuallyTrue (>= x)

-- eq :: Eq a => a -> BoundedPred a
-- eq x = BoundedPred (== x)

-- modAlt :: Integral a => a -> a -> Alternating a
-- modAlt m x = Alternating ((== x) . (`mod` m))

-- bounded :: EventuallyTrue a -> EventuallyFalse a -> BoundedPred a
-- bounded (EventuallyTrue f) (EventuallyFalse g) = BoundedPred (liftA2 (&&) f g)

-- coBounded :: EventuallyTrue a -> EventuallyFalse a -> CoBoundedPred a
-- coBounded (EventuallyTrue f) (EventuallyFalse g) = CoBoundedPred (liftA2 (||) f g)
