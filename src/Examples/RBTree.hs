-- |

{-# LANGUAGE LambdaCase#-}

module Examples.RBTree where

import ValiGen.Refine
import ValiGen.Primitive
import ValiGen.Propagator

import Data.Semigroup

import Control.Monad.ST
import Control.Monad.ST.Class
import Data.STRef

import Data.Functor

import Test.QuickCheck

import Data.Coerce

data Tree a = Leaf | Node a (Tree a) (Tree a)
  deriving (Show, Eq)

data Color = Red | Black
  deriving (Show, Eq)

type ColorTree a = Tree (Color, a)

-- | Bidirectional black height checker/generator
blackHeightBi :: STCell s (ColorTree a) -> STCell s (Max Int) -> ST s (Gen (ColorTree ()))
blackHeightBi cellT cellH = do
  watch cellT $ \case
    Known t -> blackHeight t cellH
    _ -> pure ()

  watch cellH $ \case
    Known (Max h) -> pure $ withBlackHeight h
    _ -> pure discard

blackHeightBi1 :: ColorTree a -> Int
blackHeightBi1 t = runST $ do
  cellT <- mkKnown t
  cellH <- mkUnknown
  blackHeightBi cellT cellH
  readCell cellH >>= \case
    Known (Max n) -> pure n
    x -> error $ "blackHeightBi1: " ++ show x

blackHeightBi2 :: Int -> Gen (ColorTree ())
blackHeightBi2 h = runST $ do
  cellT <- mkUnknown
  cellH <- mkKnown (Max h)
  blackHeightBi cellT cellH

getColor :: ColorTree a -> Color
getColor Leaf = Black
getColor (Node (c, _) _ _) = c

blackHeight :: ColorTree a -> STCell s (Max Int) -> ST s ()
blackHeight t output =
  case t of
    Leaf -> writeCellSemi output (Max 1) $> ()
    Node (color, _) left right -> do
      let increment = case color of Black -> 1; Red -> 0

      -- A shared cell for the two recursive calls
      c <- mkUnknown

      -- Write the (possibly incremented) contents of c into our output cell
      watch c $ \x -> writeDefinedCellSemi output (fmap (fmap (+ increment)) x) $> ()

      blackHeight left c
      blackHeight right c

getBlackHeightCell :: ColorTree a -> Int
getBlackHeightCell t = runST $ do
  c <- mkUnknown
  blackHeight t c
  readCell c >>= \case
    Unknown -> error "getBlackHeight': Unknown"
    Inconsistent -> error "getBlackHeight': Inconsistent"
    Known (Max x) -> pure x

-- isBlackHeight :: ColorTree a -> Int -> ST s Bool
-- isBlackHeight Leaf 1 = pure True
-- isBlackHeight Leaf _ = pure False
-- isBlackHeight (Node (Black, _) left right) n =
--   undefined
--   -- n == max a
--   -- &&
--   -- isBlackHeight left a
--   -- &&
--   -- isBlackHeight right b

withBlackHeight :: Int -> Gen (ColorTree ())
withBlackHeight 1 = pure Leaf
withBlackHeight n =
  sized $ \sz ->
  let
    genRed = Node (Red, ()) <$> recApply n <*> recApply n
    genBlack = Node (Black, ()) <$> recApply (n-1) <*> recApply (n-1)

    recApply = resize (sz `div` 2) . withBlackHeight
  in
  if sz <= 1
  then genBlack
  else oneof
       [ genBlack
       , genRed
       ]

withBlackHeight'valid :: Int -> Property
withBlackHeight'valid n =
  forAll (withBlackHeight n) $ \t -> getBlackHeight t == n

getBlackHeightCell'valid :: Int -> Property
getBlackHeightCell'valid n =
  forAll (withBlackHeight n) $ \t -> getBlackHeightCell t == n

blackHeightBi1'valid :: Int -> Property
blackHeightBi1'valid n =
  forAll (withBlackHeight n) $ \t -> blackHeightBi1 t == n

getBlackHeight :: ColorTree a -> Int
getBlackHeight Leaf = 1
getBlackHeight (Node (c, _) left right) =
  increment + max (getBlackHeight left) (getBlackHeight right)
  where
    increment =
      case c of
        Black -> 1
        Red -> 0

-- getBlackHeight' :: ColorTree () --> Output (Max Int)