-- |

{-# LANGUAGE LambdaCase #-}

module ValiGen.Coroutine where

import Control.Monad

newtype Coroutine s m a = Coroutine { stepCoroutine :: m (Either (s (Coroutine s m a)) a) }
  -- = Done (m a)
  -- | Step (m (s a))

instance (Monad s, Monad m) => Functor (Coroutine s m) where
  fmap f x = x >>= (pure . f)

instance (Monad s, Monad m) => Applicative (Coroutine s m) where
  pure = Coroutine . pure . Right
  (<*>) = ap

instance (Monad s, Monad m) => Monad (Coroutine s m) where
  return = pure
  x >>= f =
    Coroutine (stepCoroutine x >>= apply f)
    where
      apply g (Right a) = stepCoroutine (g a)
      apply g (Left b) = pure $ Left $ fmap (>>= g) b
