-- | Propagator-like cells for backtracking search. These cells allow dependencies between multiple different sub-computations

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module ValiGen.Cell where

-- import Control.Monad.Logic
import Control.Monad.Trans
import Control.Monad
import Control.Applicative
import Test.QuickCheck
import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.ST
-- import Control.Monad.Logic
import Data.STRef
import Data.Functor
import Data.Foldable
import Data.Pointed

import ValiGen.Nondet

newtype Value a = Value (Maybe a)
  deriving (Functor, Applicative, Monad)

pattern Undefined :: Value a
pattern Undefined = Value Nothing

pattern Defined :: a -> Value a
pattern Defined x = Value (Just x)

newtype Cell s a = Cell (STRef s (Value a))

type ValiGen n s a = Cell s a -> CPS (BoundedSearch n) (Backtrack n s a)

-- TODO: We need some kind of "designated parameter" that will serve as both an input and an output
validate :: Backtrack n s a -> a -> Bool
validate = undefined

generate :: (Pointed n, Foldable n, Nondet n) => ValiGen n s a -> ST s (n a)
generate f = do
  v <- newCell
  runBacktracks (f v)

-- data BacktrackState =

-- newtype Backtrack s a = Backtrack [Coroutine (Await (Cell s a)) (ST s) a]

  -- TODO: We probably need to be able to await *and* yield
newtype Backtrack n s a = Backtrack { getBacktrack :: Coroutine (Await ()) (ST s) (n a) }
  deriving (Functor)

instance (Traversable n, Monad n) => Applicative (Backtrack n s) where
  pure = Backtrack . pure . pure
  (<*>) = ap

instance (Traversable n, Monad n) => Monad (Backtrack n s) where
  return = pure
  Backtrack x >>= f = --Backtrack $ x >>= (_ f)
    let z = x >>= traverse (getBacktrack . f) in
    Backtrack $ fmap join z

-- newtype Susp x a = Susp (Either (Await x a) (Yield x a))

data QueueItem x f a
  = Done a
  | Waiting (Coroutine (Await x) f a)

type Queue x f a = [QueueItem x f a]

queueStep :: Monad f => Queue () f a -> f (Queue () f a)
queueStep (Done a:xs) = fmap (Done a :) (queueStep xs)
queueStep (Waiting x:xs) =
  resume x >>= \case
    Left (Await f) ->
      let z = f ()
      in
      fmap (Waiting z :) (queueStep xs)

    Right finalValue -> fmap (Done finalValue :) (queueStep xs)

runQueue :: Monad f => Queue () f a -> f [a]
runQueue q = go [] q
  where
    go acc [] = pure acc
    go acc (Done x:xs) = go (x:acc) xs
    go acc (Waiting x:xs) = runQueue =<< queueStep q

runBacktrackList :: Nondet n => [Backtrack n s a] -> ST s (n a)
runBacktrackList = fmap (foldr choice failure) . runQueue . map (Waiting . getBacktrack)

runBacktracks :: forall (n :: * -> *) s a.
  (Foldable n, Pointed n, Nondet n) =>
  CPS (BoundedSearch n) (Backtrack n s a) -> ST s (n a)
runBacktracks x =
  let z = toList $ iterDepth 1 x
  in
  runBacktrackList z

choices :: Nondet n => [Backtrack n s a] -> CPS (BoundedSearch n) (Backtrack n s a)
choices = anyOf

retry :: Monad f => f (Either () a) -> Coroutine (Await ()) f a
retry m =
  lift m >>= \case
    Right x -> pure x
    Left () -> await *> retry m

readCell :: (Traversable n, Monad n) => Cell s a -> Backtrack n s a
readCell cell@(Cell ref) =
  Backtrack $ retry $
    readSTRef ref >>= \case
       Undefined -> -- Block
         pure $ Left ()

       Defined x -> pure $ Right $ pure x

writeCell :: (Nondet n, Traversable n, Monad n, Eq a) => Cell s a -> a -> Backtrack n s ()
writeCell (Cell ref) x = do
  liftST (readSTRef ref) >>= \case
    Undefined -> liftST (writeSTRef ref (Defined x))
    Defined y
      | x == y -> pure ()
      | otherwise -> Backtrack $ pure failure

resetCell :: Cell s a -> ST s ()
resetCell (Cell ref) = writeSTRef ref Undefined

newCell :: ST s (Cell s a)
newCell = Cell <$> newSTRef Undefined

liftST :: Applicative n => ST s a -> Backtrack n s a
liftST = Backtrack . lift . fmap pure


-- instance Alternative (Backtrack s) where
--   empty = Backtrack $ pure empty
--   Backtrack x <|> Backtrack y = Backtrack $ liftA2 (<|>) x y

-- instance Applicative (Backtrack s) where
--   pure = Backtrack . pure . pure
--   (<*>) = ap

-- instance Monad (Backtrack s) where
--   return = pure
--   Backtrack x >>= f = Backtrack $ do
--     x' <- x
--     -- TODO: This might be the place to implement the communication between sub-expressions (by await/yield)
--     join <$> traverse (getBacktrack . f) x'

-- readCell :: Cell s a -> Backtrack s a
-- readCell cell@(Cell ref) =
--   liftST (readSTRef ref) >>= \case
--     Undefined ->
--       -- Block
--       Backtrack (await $> pure ()) *> readCell cell
--     Defined x -> pure x

-- writeCell :: Eq a => Cell s a -> a -> Backtrack s ()
-- writeCell (Cell ref) x = do
--   liftST (readSTRef ref) >>= \case
--     Undefined -> liftST (writeSTRef ref (Defined x))
--     Defined y
--       | x == y -> pure ()
--       | otherwise -> empty

-- -- data Propagate s

-- -- newtype Cell a = Cell (TVar (Maybe a))

-- -- newtype Backtrack a = Backtrack (LogicT STM a)
-- --   deriving (Functor, Applicative, Monad)

-- -- runBacktrack :: Backtrack a -> IO (Gen a)
-- -- runBacktrack (Backtrack m) = atomically $ runLogicT m (\x xs -> pure (pure x) <|> xs) (pure (oneof []))

-- -- newCell :: Backtrack (Cell a)
-- -- newCell = Backtrack $ fmap Cell $ lift $ newTVar Nothing

-- -- readCell :: Cell a -> Backtrack a
-- -- readCell (Cell v) = Backtrack $ do
-- --   lift $ readTVar v >>= \case
-- --     Nothing -> retry
-- --     Just x -> pure x

-- -- writeCell :: Eq a => Cell a -> a -> Backtrack ()
-- -- writeCell (Cell v) x = Backtrack $ do
-- --   y <- lift $ readTVar v
-- --   case y of
-- --     Nothing -> lift $ writeTVar v (Just x)
-- --     Just y' -> guard (x == y')
