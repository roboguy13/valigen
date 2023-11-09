-- |

module ValiGen.Injection where

import Prelude hiding (id, (.))

import Control.Category
import Control.Arrow

import Control.Monad
import Control.Applicative

data Injection a b = Injection (a -> b) (b -> Maybe a)

inject :: Injection a b -> a -> b
inject (Injection f _) = f

project :: Injection a b -> b -> Maybe a
project (Injection _ g) = g

instance Category Injection where
  id = Injection id Just
  Injection f g . Injection f' g' =
    Injection (f . f') (g' <=< g)

projectAlt :: Injection a b -> Injection a b -> b -> Maybe a
projectAlt i j x = project i x <|> project j x

projectAlts :: [Injection a b] -> b -> Maybe a
projectAlts injs x = foldr (\i acc -> project i x <|> acc) Nothing injs

joinInj :: Injection a x -> Injection b x -> Injection (Either a b) x
joinInj i j =
  Injection
    (inject i ||| inject j)
    (\x -> fmap Left (project i x) <|> fmap Right (project j x))

-- NOTE: We might be able to use this to deal with the product of two generators
meetInj :: Injection x a -> Injection x b -> Injection x (a, b)
meetInj i j =
  Injection
    (inject i &&& inject j)
    (\(x, y) -> project i x <|> project j y)

characteristic :: Eq a => Injection x a -> (a -> Bool)
characteristic inj x = case project inj x of
  Just _ -> True
  Nothing -> False

-- subobject :: (a -> Bool) -> Injection a a
-- subobject p =
--   Injection id (\x -> if p x then Just x else Nothing)
