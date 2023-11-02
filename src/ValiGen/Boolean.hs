-- |

{-# LANGUAGE DerivingVia #-}

module ValiGen.Boolean
  (EventuallyTrue
  ,EventuallyFalse
  ,BoundedPred
  ,CoBoundedPred
  ,Alternating
  ,Unrestricted

  ,Boolean (..)

  ,getBoundaryET
  ,getBoundaryEF
  ,getRegion
  ,getCoRegion
  ,getNextTrue
  ,getNextFalse

  ,unrestricted
  ,lt, le, gt, ge, eq
  ,bounded
  ,cobounded
  )
  where

import Data.Functor.Contravariant

-- | exists n. forall x > n. p x
newtype EventuallyTrue a = EventuallyTrue (a -> Bool)
  deriving Contravariant via Predicate

-- | exists n. forall x > n. !(p x)
newtype EventuallyFalse a = EventuallyFalse (a -> Bool)
  deriving Contravariant via Predicate

-- | It's going to be False, then it will be True for a while and finally it will be False forever
-- For example: \x -> x > 2 && x < 10
-- It might also *always* be False (this is a sort of degenerate case).
--
-- exists m n. (forall m < x < n. p x) /\ (forall x <= m. !(p x)) /\ (forall x >= n. !(p x))
newtype BoundedPred a = BoundedPred (a -> Bool)
  deriving Contravariant via Predicate

-- | Contrast with `BoundedPred`. An example of `CoBoundedPred` is \x -> x <= 2 || x >= 10
newtype CoBoundedPred a = CoBoundedPred (a -> Bool)
  deriving Contravariant via Predicate

-- | Example: \x -> x `mod` 5 == 0
-- At any point, there is always another True. Also, there is always another False.
--
-- (forall n. p n -> exists m > n. p m) /\ (forall n. !(p n) -> exists m > n. !(p m))
newtype Alternating a = Alternating (a -> Bool)
  deriving Contravariant via Predicate

newtype Unrestricted a = Unrestricted (a -> Bool)
  deriving Contravariant via Predicate

getBoundaryET :: EventuallyTrue a -> a
getBoundaryET = undefined

getBoundaryEF :: EventuallyFalse a -> a
getBoundaryEF = getBoundaryET . notB

getRegion :: BoundedPred a -> (a, a)
getRegion = undefined

getCoRegion :: CoBoundedPred a -> (a, a)
getCoRegion = getRegion . notB

getNextTrue :: Alternating a -> a -> a
getNextTrue = undefined

getNextFalse :: Alternating a -> a -> a
getNextFalse alt = getNextTrue (notB alt)

class Boolean f g | f -> g where
  (.&&) :: f a -> f a -> f a
  (.||) :: f a -> f a -> f a
  notB :: f a -> g a
  unrestrict :: f a -> Unrestricted a

instance Boolean EventuallyTrue EventuallyFalse where
  EventuallyTrue f .&& EventuallyTrue g = EventuallyTrue (liftA2 (&&) f g)
  EventuallyTrue f .|| EventuallyTrue g = EventuallyTrue (liftA2 (||) f g)
  notB (EventuallyTrue f) = EventuallyFalse (not . f)
  unrestrict = coerce

instance Boolean EventuallyFalse EventuallyTrue where
  EventuallyFalse f .&& EventuallyFalse g = EventuallyFalse (liftA2 (&&) f g)
  EventuallyFalse f .|| EventuallyFalse g = EventuallyFalse (liftA2 (||) f g)
  notB (EventuallyFalse f) = EventuallyTrue (not . f)
  unrestrict = coerce

instance Boolean BoundedPred CoBoundedPred where
  BoundedPred f .&& BoundedPred g = BoundedPred (liftA2 (&&) f g)
  BoundedPred f .|| BoundedPred g = BoundedPred (liftA2 (||) f g)
  notB (BoundedPred f) = CoBoundedPred (not . f)
  unrestrict = coerce

instance Boolean CoBoundedPred BoundedPred where
  CoBoundedPred f .&& CoBoundedPred g = CoBoundedPred (liftA2 (&&) f g)
  CoBoundedPred f .|| CoBoundedPred g = CoBoundedPred (liftA2 (||) f g)
  notB (CoBoundedPred f) = BoundedPred (not . f)
  unrestrict = coerce

instance Boolean Alternating Alternating where
  Alternating f .&& Alternating g = Alternating (liftA2 (&&) f g)
  Alternating f .|| Alternating g = Alternating (liftA2 (||) f g)
  notB (Alternating f) = Alternating (not . f)
  unrestrict = coerce

instance Boolean Unrestricted Unrestricted where
  Unrestricted f .&& Unrestricted g = Unrestricted (liftA2 (&&) f g)
  Unrestricted f .|| Unrestricted g = Unrestricted (liftA2 (||) f g)
  notB (Unrestricted f) = Unrestricted (not . f)
  unrestrict = id

unrestricted :: (a -> Bool) -> Unrestricted a
unrestricted = Unrestricted

lt :: Ord a => a -> EventuallyFalse a
lt x = EventuallyFalse (< x)

le :: Ord a => a -> EventuallyFalse a
le x = EventuallyFalse (<= x)

gt :: Ord a => a -> EventuallyTrue a
gt x = EventuallyTrue (> x)

ge :: Ord a => a -> EventuallyTrue a
ge x = EventuallyTrue (>= x)

eq :: Eq a => a -> BoundedPred a
eq x = BoundedPred (== x)

modAlt :: Integral a => a -> a -> Alternating a
modAlt m x = Alternating ((== x) . (`mod` m))

bounded :: EventuallyTrue a -> EventuallyFalse a -> BoundedPred a
bounded (EventuallyTrue f) (EventuallyFalse g) = BoundedPred (liftA2 (&&) f g)

coBounded :: EventuallyTrue a -> EventuallyFalse a -> CoBoundedPred a
coBounded (EventuallyTrue f) (EventuallyFalse g) = CoBoundedPred (liftA2 (||) f g)
