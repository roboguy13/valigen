-- {-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ValiGen
  where

import Control.Monad.Free

-- newtype Verifier a = Verifier  [a]
--   deriving (Functor, Applicative, Show)

-- data Verify a
--   = One a
--   | Equal a a


-- We want something that we behave like (a -> Bool), but is a deep
-- embedding

data VerifyF b a
  = OneOf [a]

  | NotOneOf (b -> Bool) -- TODO: What is the generator interpretation of this?

  | Union a a
  | Intersect a a
  -- | Neg a
  -- | Implies a (b -> a)
  deriving (Functor)

type Verify' b = Free (VerifyF b)

type Verify a = Verify' a a

oneOf :: [a] -> Verify a
oneOf = wrap . OneOf . map pure

union :: Verify a -> Verify a -> Verify a
union x = wrap . Union x

intersect :: Verify a -> Verify a -> Verify a
intersect x = wrap . Intersect x

-- We should have:
--
--   intersect a c <= b   <--->   c <= implies a b
--
-- where <= is the sublist ordering
--
implies :: Verify a -> Verify a -> Verify a
implies a b = neg a `union` b

neg :: Verify a -> Verify a
neg = undefined
-- neg (Pure z) = wrap $ NotOneOf [pure z]
-- neg (Free (NotOneOf xs)) = wrap $ OneOf xs
-- neg (Free (Union xs ys)) = wrap $ Intersect (neg xs) (neg ys)
-- neg (Free (Intersect xs ys)) = wrap $ Union (neg xs) (neg ys)

-- neg :: Verify a -> Verify a
-- neg = wrap . Neg
-- -- neg x = implies x (const (oneOf []))

verifyWith :: forall a. (a -> a -> Bool) -> Verify a -> a -> Bool
verifyWith eq = go
  where
    go :: Verify a -> a -> Bool
    go (Pure z) x = x `eq` z
    go (Free (OneOf xs)) x = any (`go` x) xs
    go (Free (NotOneOf xs)) x = not (any (`go` x) xs)
    go (Free (Union xs ys)) x = go xs x || go ys x
    go (Free (Intersect xs ys)) x = go xs x && go ys x
    -- go (Free (Neg xs)) x = not (go xs x)

verify :: Eq a => Verify a -> a -> Bool
verify = verifyWith (==)

-- Laws:
--
-- * all (verify v) (gen v) == True
--
-- * forall x. verify v x ==> (exists n. x == (gen v !! n))
--
gen :: forall a. Verify a -> [a]
gen = undefined

genAndShrinkWith :: forall a. Subterms a => (a -> a -> Bool) -> Verify a -> [a]
genAndShrinkWith = undefined

genAndShrink :: (Subterms a, Eq a) => Verify a -> [a]
genAndShrink = genAndShrinkWith (==)

class Subterms a where
  subterms :: a -> [a]

shrinkWith :: Subterms a => (a -> a -> Bool) -> Verify a -> a -> [a]
shrinkWith eq v = filter (verifyWith eq v) . subterms

-- Laws:
-- 
-- * forall x. verify v x ==> all (verify v) (shrink x)
shrink :: (Subterms a, Eq a) => Verify a -> a -> [a]
shrink = shrinkWith (==)

-- data Verify' b a
--   = OneOf [a]
--   | Union (Verify' b a) (Verify' b a)
--   | Intersect (Verify' b a) (Verify' b a)
--   | Implies (Verify' b a) (b -> Verify' b a)
--   deriving (Functor)

-- instance Applicative (Verify' b)
--
-- instance Monad (Verify' b) where
--   OneOf xs >>= f =
--     let ys = map f xs
--     in
--     _
--
-- type Verify a = Verify' a a
--
-- neg :: Verify a -> Verify a
-- neg x = Implies x (\_ -> OneOf [])
--
-- verifyWith :: (a -> a -> Bool) -> Verify a -> a -> Bool
-- verifyWith eq = go
--   where
--     go (OneOf xs) x = any (`eq` x) xs
--     go (Union xs ys) x = go xs x || go ys x
--     go (Intersect xs ys) x = go xs x && go ys x
--     go (Implies xs f) x =
--       not (go xs x) || go (f x) x
--
-- -- A condition that should hold: verify (neg xs) x <=> not (verify xs x)
--
-- gen :: Verify a -> [a]
-- gen = undefined
--
-- verify :: Eq a => Verify a -> a -> Bool
-- verify = verifyWith (==)
--
-- -- verify (x `equal` y)
--
