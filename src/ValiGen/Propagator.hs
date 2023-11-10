-- |

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ValiGen.Propagator where

import Data.STRef
import Control.Monad.ST
import Control.Monad.Trans

import Control.Applicative
import Control.Monad
import Data.Functor

import Data.Coerce

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

newtype Cell s a = Cell { getCell :: STRef s (ST s (), Defined a) }

mkUnknown :: ST s (Cell s a)
mkUnknown = Cell <$> newSTRef (pure (), Unknown)

mkKnown :: a -> ST s (Cell s a)
mkKnown = fmap Cell . newSTRef . (pure () ,) . Known

writeCell :: PartialSemigroup a => Cell s a -> a -> ST s (Maybe ())
writeCell c = writeDefinedCell c . Known

writeDefinedCell :: PartialSemigroup a => Cell s a -> Defined a -> ST s (Maybe ())
writeDefinedCell (Cell ref) x = do
  (act, z) <- readSTRef ref

  case x <<.>> z of
    Inconsistent -> pure Nothing
    v -> do
      writeSTRef ref (act, v)
      act
      pure $ Just ()

writeDefinedCellSemi :: forall s a. Semigroup a => Cell s a -> Defined a -> ST s (Maybe ())
writeDefinedCellSemi c x =
  let c' :: Cell s (LiftedSemigroup a)
      c' = coerce c

      x' :: Defined (LiftedSemigroup a)
      x' = coerce x
  in
  writeDefinedCell c' x'

writeCellSemi :: Semigroup a => Cell s a -> a -> ST s (Maybe ())
writeCellSemi c = writeDefinedCellSemi c . Known

readCell :: Cell s a -> ST s (Defined a)
readCell (Cell ref) = snd <$> readSTRef ref

watch :: forall s a. Cell s a -> (Defined a -> ST s ()) -> ST s ()
watch (Cell ref) k = do
  (act, x) <- readSTRef ref
  writeSTRef ref (act *> go, x)
  go
  where
    go :: ST s ()
    go = do
      (_, z) <- readSTRef ref
      k z

unarySemi :: forall s a b. Semigroup b => (a -> b) -> Cell s a -> Cell s b -> ST s ()
unarySemi f cX cR =
  let cR' :: Cell s (LiftedSemigroup b)
      cR' = coerce cR

      f' :: a -> LiftedSemigroup b
      f' = coerce f
  in
  unarySemi f' cX cR'

binarySemi :: forall s a b c. Semigroup c => (a -> b -> c) -> Cell s a -> Cell s b -> Cell s c -> ST s ()
binarySemi f cX cY cR =
  let cR' :: Cell s (LiftedSemigroup c)
      cR' = coerce cR

      f' :: a -> b -> LiftedSemigroup c
      f' = coerce f
  in
  binarySemi f' cX cY cR'

unary :: forall s a b. PartialSemigroup b => (a -> b) -> Cell s a -> Cell s b -> ST s ()
unary f cX cR =
  watch cX go
  where
    go :: Defined a -> ST s ()
    go (Known x) = do
      writeCell cR (f x)
      pure ()
    go _ = pure ()

binary :: forall s a b c. PartialSemigroup c => (a -> b -> c) -> Cell s a -> Cell s b -> Cell s c -> ST s ()
binary f cX cY cR = do
  watch cX goX
  watch cY goY
  where
    goX :: Defined a -> ST s ()
    goX x = do
      y <- readCell cY
      writeDefinedCell cR (liftA2 f x y)
      pure ()

    goY :: Defined b -> ST s ()
    goY y = do
      x <- readCell cX
      writeDefinedCell cR (liftA2 f x y)
      pure ()
