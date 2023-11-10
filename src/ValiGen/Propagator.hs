-- |

{-# LANGUAGE ScopedTypeVariables #-}

module ValiGen.Propagator where

import Data.STRef
import Control.Monad.ST
import Control.Monad.ST.Class
import Control.Monad.Trans

import Control.Applicative
import Control.Monad
import Data.Functor

import Data.Coerce

import Test.QuickCheck

data Defined a
  = Inconsistent
  | Unknown
  | Known a
  deriving (Show, Functor, Foldable, Traversable)

instance Applicative Defined where
  pure = Known
  (<*>) = ap

instance Monad Defined where
  return = pure
  Inconsistent >>= _ = Inconsistent
  Unknown >>= _ = Unknown
  Known x >>= f = f x

class PartialSemigroup a where
  (<<>>) :: a -> a -> Defined a

newtype LiftedSemigroup a = LiftedSemigroup { getLiftedSemigroup :: a }
  deriving (Show, Semigroup, Monoid, Functor)

instance Semigroup a => PartialSemigroup (LiftedSemigroup a) where
  x <<>> y = Known (x <> y)

newtype Flat a = Flat { getFlat :: a }
  deriving (Show, Functor, Eq, Ord)

instance Eq a => PartialSemigroup (Flat a) where
  x <<>> y
    | x == y = Known x
    | otherwise = Inconsistent

(<<.>>) :: PartialSemigroup a => Defined a -> Defined a -> Defined a
(<<.>>) Inconsistent _ = Inconsistent
(<<.>>) _ Inconsistent = Inconsistent
(<<.>>) Unknown x = x
(<<.>>) x Unknown = x
(<<.>>) (Known x) (Known y) = x <<>> y

instance Semigroup a => Semigroup (Defined a) where
  Inconsistent <> _ = Inconsistent
  _ <> Inconsistent = Inconsistent

  Unknown <> x = x
  x <> Unknown = x

  Known x <> Known y = Known (x <> y)

instance Semigroup a => Monoid (Defined a) where
  mempty = Unknown

newtype Cell m a = Cell { getCell :: STRef (World m) (m (), Defined a) }

mkUnknown :: MonadST m =>
  m (Cell m a)
mkUnknown = Cell <$> liftST (newSTRef (pure (), Unknown))

mkKnown :: MonadST m =>
  a -> m (Cell m a)
mkKnown = fmap Cell . liftST . newSTRef . (pure () ,) . Known

writeCell :: (MonadST m, PartialSemigroup a) =>
  Cell m a -> a -> m (Maybe ())
writeCell c = writeDefinedCell c . Known

writeDefinedCell :: (MonadST m, PartialSemigroup a) =>
  Cell m a -> Defined a -> m (Maybe ())
writeDefinedCell (Cell ref) x = do
  (act, z) <- liftST $ readSTRef ref

  case x <<.>> z of
    Inconsistent -> pure Nothing
    v -> do
      liftST $ writeSTRef ref (act, v)
      act
      pure $ Just ()

writeDefinedCellSemi :: forall m a. (MonadST m, Semigroup a) =>
  Cell m a -> Defined a -> m (Maybe ())
writeDefinedCellSemi c x =
  let c' :: Cell m (LiftedSemigroup a)
      c' = coerce c

      x' :: Defined (LiftedSemigroup a)
      x' = coerce x
  in
  writeDefinedCell c' x'

writeCellSemi :: (MonadST m, Semigroup a) =>
  Cell m a -> a -> m (Maybe ())
writeCellSemi c = writeDefinedCellSemi c . Known

readCell :: MonadST m =>
  Cell m a -> m (Defined a)
readCell (Cell ref) = snd <$> liftST (readSTRef ref)

watch :: forall m a r. MonadST m =>
  Cell m a -> (Defined a -> m r) -> m r
watch (Cell ref) k = do
  (act, x) <- liftST $ readSTRef ref
  liftST $ writeSTRef ref (act *> go $> (), x)
  go
  where
    go :: m r
    go = do
      (_, z) <- liftST $ readSTRef ref
      k z

-- watchGen :: forall s a. Cell s a -> (Defined a -> Gen a) -> ST s ()
-- watchGen = undefined

unarySemi :: forall m a b. Semigroup b => (a -> b) -> Cell m a -> Cell m b -> m ()
unarySemi f cX cR =
  let cR' :: Cell m (LiftedSemigroup b)
      cR' = coerce cR

      f' :: a -> LiftedSemigroup b
      f' = coerce f
  in
  unarySemi f' cX cR'

binarySemi :: forall m a b c. Semigroup c => (a -> b -> c) -> Cell m a -> Cell m b -> Cell m c -> m ()
binarySemi f cX cY cR =
  let cR' :: Cell m (LiftedSemigroup c)
      cR' = coerce cR

      f' :: a -> b -> LiftedSemigroup c
      f' = coerce f
  in
  binarySemi f' cX cY cR'

unary :: forall m a b. (MonadST m, PartialSemigroup b) =>
  (a -> b) -> Cell m a -> Cell m b -> m ()
unary f cX cR =
  watch cX go
  where
    go :: Defined a -> m ()
    go (Known x) = do
      writeCell cR (f x)
      pure ()
    go _ = pure ()

binary :: forall m a b c. (MonadST m, PartialSemigroup c) =>
  (a -> b -> c) -> Cell m a -> Cell m b -> Cell m c -> m ()
binary f cX cY cR = do
  watch cX goX
  watch cY goY
  where
    goX :: Defined a -> m ()
    goX x = do
      y <- readCell cY
      writeDefinedCell cR (liftA2 f x y)
      pure ()

    goY :: Defined b -> m ()
    goY y = do
      x <- readCell cX
      writeDefinedCell cR (liftA2 f x y)
      pure ()

type STCell s = Cell (ST s)

-- type CellGen m a = Cell m (Either (Gen a) a)
