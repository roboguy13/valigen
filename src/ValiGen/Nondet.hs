-- | Based on "Reinventing Haskell Backtracking"

module ValiGen.Nondet where

import Control.Monad
import Control.Applicative

import Data.Pointed
import Data.Foldable
import GHC.IO.SubSystem (IoSubSystem)

newtype CPS f a = CPS { (>>-) :: forall b. (a -> f b) -> f b }

runCPS :: Pointed f => CPS f a -> f a
runCPS x = x >>- point

mkCPS :: Monad f => f a -> CPS f a
mkCPS fa = CPS (fa >>=)

instance Functor (CPS f) where
  fmap f x = x >>= (pure . f)

instance Applicative (CPS f) where
  pure x = CPS ($ x)
  (<*>) = ap

instance Monad (CPS f) where
  return = pure
  a >>= f = CPS $ \c -> a >>- \x -> f x >>- c

instance (Pointed f, Foldable f) => Foldable (CPS f) where
  foldMap f = foldMap f . runCPS

instance (Pointed f, Traversable f, Monad f) => Traversable (CPS f) where
  traverse f = fmap mkCPS . traverse f . runCPS

class Nondet n where
  failure :: n a
  choice :: n a -> n a -> n a

  choices :: [n a] -> n a
  choices = foldr choice failure


instance Nondet f => Alternative (CPS f) where
  empty  = CPS (const failure)
  a <|> b = CPS (\c -> choice (a >>- c) (b >>- c))

instance Nondet f => MonadPlus (CPS f)

-- | BFS
newtype Levels n a = Levels { levels :: [n a] }

runLevels :: Nondet n => Levels n a -> n a
runLevels = foldr choice failure . levels

newtype DiffList a = DiffList { runDiffList :: [a] -> [a] }

instance Pointed DiffList where
  point x = DiffList (x:)

instance Semigroup (DiffList a) where
  a <> b = DiffList (runDiffList a . runDiffList b)

instance Monoid (DiffList a) where
  mempty = DiffList id

instance Foldable DiffList where
  toList a = runDiffList a []
  foldr f z = foldr f z . toList

instance Nondet DiffList where
  failure = mempty
  choice = (<>)

anyOf :: MonadPlus m => [a] -> m a
anyOf [] = mzero
anyOf (x:xs) = anyOf xs `mplus` pure x

backtrack :: CPS DiffList a -> [a]
backtrack = toList . runCPS

levelSearch :: CPS (Levels DiffList) a -> [a]
levelSearch = toList . runLevels . runCPS

instance Pointed n => Pointed (Levels n) where
  point x = Levels [point x]

instance Nondet n => Nondet (Levels n) where
  failure = Levels []
  choice a b = Levels (failure : merge (levels a) (levels b))

merge :: Nondet n => [n a] -> [n a] -> [n a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) = choice x y : merge xs ys

newtype BoundedSearch n a = BoundedSearch { (!) :: Int -> n a }

instance Nondet n => Nondet (BoundedSearch n) where
  failure = BoundedSearch (const failure)
  choice a b = BoundedSearch $ \d ->
    if d == 0
    then failure
    else choice (a ! (d - 1)) (b ! (d - 1))

levelIter :: (Pointed n, Nondet n) =>
  Int -> CPS (BoundedSearch n) a -> Levels n a
levelIter step a = Levels [(a >>- yieldB) ! d | d <- [0, step..]]
  where
    yieldB x = BoundedSearch $ \d ->
      if d < step
      then point x
      else failure

iterDepth :: (Pointed n, Nondet n) =>
  Int -> CPS (BoundedSearch n) a -> n a
iterDepth step = choices . levels . levelIter step

----

data Tree a = Leaf a | Node [Tree a]
  deriving (Show, Functor)

-- instance Applicative Tree where
--   pure = Leaf
--   (<*>) = ap

-- instance Monad Tree where
--   return = pure
--   Leaf x >>= f = f x
--   Node xs >>= f = Node $ map (>>= f) xs

instance Nondet Tree where
  failure = Node []
  choice x y = Node [x, y]
  choices = Node

instance Pointed Tree where
  point = Leaf
