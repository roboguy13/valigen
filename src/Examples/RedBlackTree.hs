-- |

module Examples.RedBlackTree where

data Color = Red | Black
  deriving (Show, Eq)

data Tree a = Leaf a | Node a (Tree a) (Tree a)

type ColorTree a = Tree (Color, a)

(-->) :: Bool -> Bool -> Bool
False --> _ = True
True --> True = True
_ --> _ = False

rootColor :: ColorTree a -> Color
rootColor (Leaf (c, _)) = c
rootColor (Node (c, _) _ _) = c

blackHeightMax :: ColorTree a -> Int
blackHeightMax (Leaf (Black, _)) = 1
blackHeightMax (Leaf (Red, _)) = 0
blackHeightMax (Node (Black, _) left right) = 1 + max (blackHeightMax left) (blackHeightMax right)
blackHeightMax (Node (Red, _) left right) = max (blackHeightMax left) (blackHeightMax right)

blackHeightMin :: ColorTree a -> Int
blackHeightMin (Leaf (Black, _)) = 1
blackHeightMin (Leaf (Red, _)) = 0
blackHeightMin (Node (Black, _) left right) = 1 + min (blackHeightMin left) (blackHeightMin right)
blackHeightMin (Node (Red, _) left right) = min (blackHeightMin left) (blackHeightMin right)

isRedBlackTree :: ColorTree a -> Bool
isRedBlackTree (Leaf (Black, _)) = True
isRedBlackTree (Leaf (Red, _)) = False
isRedBlackTree (Node (color, _) left right) =
  ((color == Red) --> (rootColor left /= Red && rootColor right /= Red))
  && (blackHeightMin left == blackHeightMax left && blackHeightMin right == blackHeightMax right)
  && (blackHeightMin left == blackHeightMin right)
