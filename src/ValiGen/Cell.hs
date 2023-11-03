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
import Data.STRef
import Data.Functor

newtype Value a = Value (Maybe a)
  deriving (Functor, Applicative, Monad)

pattern Undefined :: Value a
pattern Undefined = Value Nothing

pattern Defined :: a -> Value a
pattern Defined x = Value (Just x)

newtype Cell s a = Cell (STRef s (Value a))

-- data BacktrackState =

-- newtype Backtrack s a = Backtrack [Coroutine (Await (Cell s a)) (ST s) a]
  -- TODO: We probably need to be able to await *and* yield
newtype Backtrack s a = Backtrack { getBacktrack :: Coroutine (Await ()) (ST s) [a] }
  deriving (Functor)

instance Alternative (Backtrack s) where
  empty = Backtrack $ pure []
  Backtrack x <|> Backtrack y = Backtrack $ liftA2 (++) x y

instance Applicative (Backtrack s) where
  pure = Backtrack . pure . pure
  (<*>) = ap

instance Monad (Backtrack s) where
  return = pure
  Backtrack x >>= f = Backtrack $ do
    x' <- x
    -- TODO: This might be the place to implement the communication between sub-expressions (by await/yield)
    concat <$> traverse (getBacktrack . f) x'

liftST :: ST s a -> Backtrack s a
liftST = Backtrack . lift . fmap (:[])

readCell :: Cell s a -> Backtrack s a
readCell cell@(Cell ref) =
  liftST (readSTRef ref) >>= \case
    Undefined ->
      -- Block
      Backtrack (await $> [()]) *> readCell cell
    Defined x -> pure x

writeCell :: Eq a => Cell s a -> a -> Backtrack s ()
writeCell (Cell ref) x = do
  liftST (readSTRef ref) >>= \case
    Undefined -> liftST (writeSTRef ref (Defined x))
    Defined y
      | x == y -> pure ()
      | otherwise -> empty

-- data Propagate s

-- newtype Cell a = Cell (TVar (Maybe a))

-- newtype Backtrack a = Backtrack (LogicT STM a)
--   deriving (Functor, Applicative, Monad)

-- runBacktrack :: Backtrack a -> IO (Gen a)
-- runBacktrack (Backtrack m) = atomically $ runLogicT m (\x xs -> pure (pure x) <|> xs) (pure (oneof []))

-- newCell :: Backtrack (Cell a)
-- newCell = Backtrack $ fmap Cell $ lift $ newTVar Nothing

-- readCell :: Cell a -> Backtrack a
-- readCell (Cell v) = Backtrack $ do
--   lift $ readTVar v >>= \case
--     Nothing -> retry
--     Just x -> pure x

-- writeCell :: Eq a => Cell a -> a -> Backtrack ()
-- writeCell (Cell v) x = Backtrack $ do
--   y <- lift $ readTVar v
--   case y of
--     Nothing -> lift $ writeTVar v (Just x)
--     Just y' -> guard (x == y')
