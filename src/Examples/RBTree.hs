-- |

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeFamilies #-}

module Examples.RBTree where

import ValiGen.Refine
import ValiGen.Primitive
import ValiGen.Propagator

import Data.Semigroup

import Data.Constraint

import Control.Monad.ST
import Control.Monad.ST.Class
import Data.STRef

import Data.Functor

import Test.QuickCheck hiding (total)

import Data.Coerce
import Control.Lens (only, rewrite)

import Control.Applicative

import Control.Monad
import Control.Monad.State

import Data.Monoid

data Tree a = Leaf | Node a (Tree a) (Tree a)
  deriving (Show, Eq, Functor)

data Color = Red | Black
  deriving (Show, Eq)

type ColorTree a = Tree (Color, a)

data Mode = Filter | Generate
  deriving (Show)

data ModeS (mode :: Mode) where
  FilterS   :: ModeS 'Filter
  GenerateS :: ModeS 'Generate

class ModeC (mode :: Mode) where
  getMode :: ModeS mode
  mk :: ModeS mode -> a -> Output mode a

instance ModeC Filter where
  getMode = FilterS
  mk _ = id

instance ModeC Generate where
  getMode = GenerateS
  mk _ = pure

type MaybeGen a = Maybe (Gen a)

newtype ValiGen (mode :: Mode) s a = ValiGen (ST s a)
  deriving (Show, Functor, Applicative, Monad, MonadST)
  -- ValiGen :: ST s a -> ValiGen mode s ga
  -- ValidateVG :: ST s a -> ValiGen Filter s g a
  -- -- GenVG :: (STCell s (Flat (Gen g)) -> ST s a) -> ValiGen Generate s g a
  -- -- GenVG :: (ST s (MaybeGen g, a)) -> ValiGen Generate s g a
  -- GenVG :: (ST s (MaybeGen g)) -> ValiGen Generate s g a

type VGCell mode s = Cell (ValiGen mode s)

data GenOut (mode :: Mode) s a where
  GenOutG :: VGCell Generate s (Once (Gen a)) -> GenOut Generate s a
  GenOutV :: VGCell Filter s a -> GenOut Filter s a

data GenIn (mode :: Mode) s a where
  GenInG :: Gen a -> GenIn Generate s a
  GenInV :: VGCell Generate s a -> GenIn Generate s a

type family Output (mode :: Mode) a where
  Output Generate a = Gen a
  Output Filter a = a

class ReadVar f where
  readVar :: ModeC mode => f mode s a -> ValiGen mode s (Defined (Output mode a))
  watchVar :: ModeC mode => f mode s a -> (Output mode a -> ValiGen mode s ()) -> ValiGen mode s ()

class WriteVar f mode where
  writeVar :: Semigroup a => f mode s a -> Output mode a -> ValiGen mode s ()
  partialWriteVar :: PartialSemigroup a => f mode s a -> Output mode a -> ValiGen mode s ()

  lift3 ::
    (Cell (ValiGen mode s) a -> Cell (ValiGen mode s) a -> Cell (ValiGen mode s) a -> ValiGen mode s ()) ->
    f mode s a -> f mode s a -> f mode s a -> ValiGen mode s ()


instance ReadVar GenOut where
  readVar (GenOutG c) = fmap getOnce <$> readCell c
  readVar (GenOutV c) = readCell c

  watchVar (GenOutG c) f = watch c $ \case
    Known (Once x) -> f x
    _ -> pure ()

instance ReadVar GenIn where
  readVar (GenInG x) = pure $ Known x
  readVar (GenInV c) = fmap pure <$> readCell c

  watchVar (GenInG x) f = f x -- We already have the value right now
  watchVar (GenInV c) f = watch c $ \case
    Known x -> f $ pure x -- _ f x
    _ -> pure ()

instance WriteVar GenOut Generate where
  writeVar (GenOutG c) x = writeCell c (Once x) $> ()
  partialWriteVar (GenOutG c) x = writeCell c (Once x) $> ()
  -- writeVar (GenOut c) x = writeCellSemi c x $> ()
  lift3 f (GenOutG x) (GenOutG y) (GenOutG z) = do
    x' <- x
    f (coerce x') (coerce y) (coerce z)

-- -- TODO: Remove. This is for testing purposes
-- instance WriteVar GenOut Filter where
--   writeVar (GenOut c) x = writeCellSemi c x $> ()
--   partialWriteVar (GenOut c) x = writeCell c x $> ()
--   lift3 f x y z = f (coerce x) (coerce y) (coerce z)

-- instance WriteVar GenIn Filter where
--   writeVar (GenIn c) x = writeCellSemi c x $> ()
--   partialWriteVar (GenIn c) x = writeCell c x $> ()
--   lift3 f x y z = f (coerce x) (coerce y) (coerce z)

-- -- add :: forall mode s. (ModeC mode) =>
-- --   GenIn mode s (Sum Int) -> GenOut mode s (Sum Int) -> ValiGen mode s ()
-- -- add x y =
-- --   case getMode @mode of
-- --     GenerateS ->
-- --       watchVar x $ \case
-- --         Known xVal -> writeVar y xVal
-- --         _ -> pure ()

-- --     FilterS ->
-- --       watchVar y $ \case
-- --         Known yVal -> writeVar x yVal
-- --         _ -> pure ()

-- withEq :: forall mode s r g a. (Eq a, ModeC mode) =>
--   a ->
--   GenOut mode s g (Flat a) ->
--   (GenOut mode s g (Flat a) -> ValiGen mode s g ()) ->
--   ValiGen mode s g ()
-- withEq x c f =
--   case getMode @mode of
--     GenerateS -> partialWriteVar c (Flat x) *> f c
--     FilterS ->
--       watchVar c $ \case
--         Known (Flat v) | v == x -> f c
--         _ -> pure ()

-- black :: forall mode s g r. (ModeC mode) =>
--   GenOut mode s g (Flat Color) ->
--   (GenOut mode s g (Flat Color) -> ValiGen mode s g ()) ->
--   ValiGen mode s g ()
-- black = withEq Black

-- red :: forall mode s g r. (ModeC mode) =>
--   GenOut mode s g (Flat Color) ->
--   (GenOut mode s g (Flat Color) -> ValiGen mode s g ()) ->
--   ValiGen mode s g ()
-- red = withEq Red

-- leaf :: forall mode s g a. (ModeC mode, Eq a) =>
--   GenOut mode s g (Flat (Tree a)) ->
--   ValiGen mode s g () ->
--   ValiGen mode s g ()
-- leaf c act =
--   case getMode @mode of
--     GenerateS -> partialWriteVar c (Flat Leaf) *> act -- TODO: Is this right?
--     FilterS ->
--       watchVar c $ \case
--         Known (Flat Leaf) -> act
--         _ -> pure ()

-- node :: forall mode s g a. (ModeC mode, Eq a) =>
--   GenOut mode s g (Flat (Tree a)) ->
--   (GenOut mode s g a -> GenOut mode s g (Flat (Tree a)) -> GenOut mode s g (Flat (Tree a)) -> ValiGen mode s g ()) ->
--   ValiGen mode s g ()
-- node cell f =
--   case getMode @mode of
--     GenerateS -> do
--       itemCell <- GenOut <$> mkUnknown
--       leftCell <- GenOut <$> mkUnknown
--       rightCell <- GenOut <$> mkUnknown
--       _ <- f itemCell leftCell rightCell
--       pure () -- TODO: Figure out how the generating part should be here
--     FilterS ->
--       watchVar cell $ \case
--         Known (Flat (Node c left right)) -> do
--           itemCell <- GenOut <$> mkKnown c
--           leftCell <- GenOut <$> mkKnown (Flat left)
--           rightCell <- GenOut <$> mkKnown (Flat right)
--           _ <- f itemCell leftCell rightCell
--           pure ()
--         _ -> pure ()

-- getIncrement :: (ModeC mode, Num a, Ord a, WriteVar GenOut mode) =>
--   GenOut mode s g (Flat Color) -> GenOut mode s g (Max a) -> ValiGen mode s g ()
-- getIncrement color iCell =
--   black color (\_ -> writeVar iCell 1)
--     <>
--   red color (\_ -> writeVar iCell 0)

-- -- add' :: forall mode s f a. (WriteVar f mode, Eq a, Num a) =>
-- --   f mode s a -> f mode s a -> f mode s a -> ValiGen mode s ()
-- -- add' = undefined

-- instance ModeC mode =>
--   Semigroup (ValiGen mode s g a) where
--   x <> y =
--     case getMode @mode of
--       FilterS -> x *> y
--       GenerateS ->
--         case (x, y) of
--           (GenVG x', GenVG y') -> GenVG $ do
--             (xG, _) <- x'
--             (yG, yV) <- y'
--             pure (liftA2 (\a b -> oneof [a, b]) xG yG, yV)

--   -- (<>) = (*>) -- TODO: Work on this

-- run2'2 ::
--   (forall s.
--    GenOut Filter s g (Flat a) ->
--    GenOut Filter s g (Max b) ->
--    ValiGen Filter s g ()) ->
--   a ->
--   b
-- run2'2 f x = validate $ do
--   xCell <- GenOut <$> mkKnown (Flat x)
--   yCell <- GenOut <$> mkUnknown
--   f xCell yCell
--   readVar yCell >>= \case
--     Known (Max y) -> pure y

-- runGen2'2 ::
--   (forall s.
--    GenOut Generate s g (Flat a) ->
--    GenOut Generate s g (Max b) ->
--    ValiGen Generate s g ()) ->
--   b ->
--   (MaybeGen g, a)
-- runGen2'2 f y = runGen $ do
--   xCell <- GenOut <$> mkUnknown
--   yCell <- GenOut <$> mkKnown (Max y)
--   f xCell yCell
--   readVar xCell >>= \case
--     Known (Flat x) -> pure x

-- blackHeight :: (ModeC mode, WriteVar GenOut mode) =>
--   GenOut mode s (Flat (Tree (Flat Color))) (Flat (Tree (Flat Color))) ->
--   GenOut mode s (Flat (Tree (Flat Color))) (Max Int) ->
--   ValiGen mode s (Flat (Tree (Flat Color))) ()
-- blackHeight t height =
--   leaf t (writeVar height 1 *> mkGen (pure (Flat Leaf)))
--     <>
--   node t (\c left right -> do
--     i <- GenOut <$> mkUnknown
--     getIncrement c i
--     leftHeightInc <- GenOut <$> mkUnknown
--     rightHeightInc <- GenOut <$> mkUnknown

--     leftHeight <- GenOut <$> mkUnknown
--     rightHeight <- GenOut <$> mkUnknown

--     lift3 add i leftHeight leftHeightInc
--     lift3 add i rightHeight rightHeightInc

--     watchVar leftHeightInc $ \case
--       Known lh -> writeVar height lh
--       _ -> pure ()
--     watchVar rightHeightInc $ \case
--       Known rh -> writeVar height rh
--       _ -> pure ()
--     -- writeVar height leftHeightInc
--     -- writeVar height rightHeightInc

--     blackHeight left leftHeight
--     blackHeight right rightHeight

--     Known cVal <- readVar c
--     Known leftVal <- readVar left
--     Known rightVal <- readVar right
--     mkGen $ pure $ Flat $ Node cVal (getFlat leftVal) (getFlat rightVal)
--     )



-- -- data ValiGen w s t a b =
-- --   ValiGen { vgApply :: s -> t
-- --           , vgGen :: a -> Gen b
-- --           }

-- -- mkValiGen1 ::
-- --   (forall w. STCell w s -> STCell w t -> STCell w a -> STCell w (Gen b) -> ST w ()) ->
-- --   ValiGen w' s t a b
-- -- mkValiGen1 k =
-- --   ValiGen
-- --     (\x -> runST $ do
-- --         xCell <- mkKnown x
-- --         aCell <- mkUnknown
-- --         tCell <- mkUnknown
-- --         bCell <- mkUnknown
-- --         k xCell tCell aCell bCell
-- --         readCell tCell >>= \case
-- --           Known t -> pure t)

-- --     (\x -> runST $ do
-- --         xCell <- mkKnown x
-- --         sCell <- mkUnknown
-- --         tCell <- mkUnknown
-- --         bCell <- mkUnknown
-- --         k sCell tCell xCell bCell
-- --         readCell bCell >>= \case
-- --           Known b -> pure b)

-- -- blackHeight :: ValiGen w (ColorTree ()) (Max Int) (Max Int) (ColorTree ())
-- -- blackHeight = mkValiGen1 $ \s t a b ->
-- --   undefined

-- -- value :: t -> ValiGen w s t a t
-- -- value x = ValiGen (const x) (const (pure x))

-- -- type Opt = Alt Maybe

-- -- -- | Disjunction
-- -- instance Semigroup t => Semigroup (ValiGen w s t a b) where
-- --   ValiGen f g <> ValiGen f' g' =
-- --     ValiGen (f <> f') (\x -> oneof [g x, g' x])

-- -- instance Monoid t => Monoid (ValiGen w s t a b) where
-- --   mempty = ValiGen mempty (const (oneof []))

-- -- -- | Composition
-- -- (%) :: ValiGen w s t a b -> ValiGen w u s x a -> ValiGen w u t x b
-- -- (%) (ValiGen f g) (ValiGen f' g') =
-- --   ValiGen (f . f') (g <=< g')

-- -- -- -- (%.) :: ValiGen s (m t) a b -> ValiGen u s x a -> ValiGen u t x b
-- -- -- -- (%.) (ValiGen f g) (ValiGen f' g') =
-- -- -- --   ValiGen (_ f f') (g <=< g')

-- -- -- | NOTE: We need to be careful, because this is unsafe
-- -- total :: ValiGen w s (Opt t) a b -> ValiGen w s t a b
-- -- total vg =
-- --   ValiGen
-- --     (\x -> let Alt (Just z) = vgApply vg x in z)
-- --     (vgGen vg)

-- -- -- node ::
-- -- --   ValiGen w (ST w a, ST w (Tree a), ST w (Tree a)) r x (a, Tree a, Tree a) ->
-- -- --   ValiGen w (Tree a) (Opt r) x (Tree a)
-- -- -- node vg =
-- -- --   undefined

-- --   -- ValiGen
-- --   --   (\case Leaf -> Alt Nothing; Node x left right -> Alt $ Just $ vgApply vg (x, left, right))
-- --   --   (\arg -> do (x, left, right) <- vgGen vg arg; pure (Node x left right))

-- -- -- red :: r -> ValiGen Color (Opt r) x Color
-- -- -- red x =
-- -- --   ValiGen
-- -- --     (\case Red -> Alt $ Just x; Black -> Alt Nothing)
-- -- --     (\_ -> pure Red)

-- -- -- black :: r -> ValiGen Color (Opt r) x Color
-- -- -- black x =
-- -- --   ValiGen
-- -- --     (\case Red -> Alt Nothing; Black -> Alt $ Just x)
-- -- --     (\_ -> pure Black)

-- -- -- eq :: Eq a => a -> r -> r -> ValiGen a r x a
-- -- -- eq z true false =
-- -- --   ValiGen
-- -- --     (\x -> if x == z then true else false)
-- -- --     (\_ -> pure z)

-- -- -- -- -- test = (<>) (eq undefined) black

-- -- -- leaf :: r -> ValiGen (ColorTree ()) (Opt r) x (ColorTree ())
-- -- -- leaf x =
-- -- --   ValiGen
-- -- --     (\case Leaf -> Alt $ Just x ; Node {} -> Alt Nothing)
-- -- --     (\_ -> pure Leaf)

-- -- -- node ::
-- -- --   ValiGen (a, Tree a, Tree a) r x (a, Tree a, Tree a) ->
-- -- --   ValiGen (Tree a) (Opt r) x (Tree a)
-- -- -- node vg =
-- -- --   ValiGen
-- -- --     (\case Leaf -> Alt Nothing; Node x left right -> Alt $ Just $ vgApply vg (x, left, right))
-- -- --     (\arg -> do (x, left, right) <- vgGen vg arg; pure (Node x left right))

-- -- -- getIncrement :: ValiGen Color (Max Int) () Color
-- -- -- getIncrement = total $
-- -- --   black 1 <> red 0

-- -- --   -- | Add when "checking" and subtract when generating
-- -- -- add :: Num a => a -> ValiGen a a a a
-- -- -- add x =
-- -- --   ValiGen
-- -- --     (+ x)
-- -- --     (\y -> pure (y - x))

-- -- --   -- | Add to the output when "checking", subtract from the input when generating
-- -- -- add' :: Num t => t -> ValiGen s t t b -> ValiGen s t t b
-- -- -- add' x vg =
-- -- --   ValiGen
-- -- --     (\t -> (vgApply vg t) + x)
-- -- --     (\t -> vgGen vg (t - x))

-- -- -- -- add'' :: Num t => ValiGen x t y x -> ValiGen s t t b -> ValiGen x t t b
-- -- -- -- add'' xVG vg =
-- -- -- --   ValiGen
-- -- -- --     (\x -> vgApply xVG x + vgApply vg _)
-- -- -- --     undefined

-- -- -- -- valiGenRunST :: (forall w. ValiGen s (ST w t) a (forall w'. ST w' b)) -> ValiGen s t a b
-- -- -- -- valiGenRunST vg =
-- -- -- --   ValiGen
-- -- -- --     (\x -> runST (vgApply vg x))
-- -- -- --     (\x -> fmap runST (vgGen vg x))

-- -- -- matchNode :: forall t a x.
-- -- --   (forall s. STCell s a -> STCell s (Tree a) -> STCell s (Tree a) -> ST s (ValiGen () t () (a, Tree a, Tree a))) ->
-- -- --   ValiGen (Tree a) (Opt t) x (Tree a)
-- -- -- matchNode k =
-- -- --   -- valiGenRunST $
-- -- --   ValiGen
-- -- --     (\case
-- -- --         Node a left right -> runST $ do
-- -- --           aCell <- mkKnown a
-- -- --           leftCell <- mkKnown left
-- -- --           rightCell <- mkKnown right
-- -- --           f <- k aCell leftCell rightCell
-- -- --           pure $ Alt $ Just $ vgApply f ()
-- -- --         _ -> Alt Nothing
-- -- --         )
-- -- --     (\x -> runST $ do
-- -- --         aCell <- mkUnknown
-- -- --         leftCell <- mkUnknown
-- -- --         rightCell <- mkUnknown
-- -- --         f <- k aCell leftCell rightCell
-- -- --         pure $ do
-- -- --           (a, left, right) <- vgGen f ()
-- -- --           pure $ Node a left right
-- -- --         )

-- -- -- blackHeight :: ValiGen (ColorTree ()) (Max Int) (Max Int) (ColorTree ())
-- -- -- blackHeight = total $
-- -- --   leaf 1
-- -- --   <>
-- -- --   node (
-- -- --     ValiGen
-- -- --       (\((c, _), left, right) ->
-- -- --          (vgApply getIncrement c + vgApply blackHeight left)
-- -- --            <>
-- -- --          (vgApply getIncrement c + vgApply blackHeight right))
-- -- --       (\h -> do
-- -- --           c <- vgGen getIncrement ()
-- -- --           let i = vgApply getIncrement c
-- -- --           left <- vgGen blackHeight (h - i)
-- -- --           right <- vgGen blackHeight (h - i)
-- -- --           pure ((c, ()), left, right))
-- -- --     )

-- -- -- lam :: (x -> ValiGen s t a b) -> ValiGen (x, s) t (x, a) b
-- -- -- lam f =
-- -- --   ValiGen
-- -- --     (\(x, s) -> vgApply (f x) s)
-- -- --     (\(x, a) -> vgGen (f x) a)

-- -- -- app :: ValiGen s t a b -> s -> ValiGen () t a b
-- -- -- app vg s =
-- -- --   ValiGen
-- -- --     (\() -> vgApply vg s)
-- -- --     (vgGen vg)

-- -- -- blackHeight' :: ValiGen (ColorTree ()) (Max Int) (Max Int) (ColorTree ())
-- -- -- blackHeight' = total $
-- -- --   leaf 1
-- -- --   <>
-- -- --   node (
-- -- --     ValiGen
-- -- --       (\((c, _), left, right) ->
-- -- --          vgApply (add' 1 (app blackHeight left) <> add' 1 (app blackHeight right)) ())
-- -- --          -- (vgApply getIncrement c + vgApply blackHeight left)
-- -- --          --   <>
-- -- --          -- (vgApply getIncrement c + vgApply blackHeight right))
-- -- --       (\h -> do
-- -- --           c <- vgGen getIncrement ()
-- -- --           let i = vgApply getIncrement c
-- -- --           left <- vgGen blackHeight (h - i)
-- -- --           right <- vgGen blackHeight (h - i)
-- -- --           pure ((c, ()), left, right))
-- -- --     )

-- -- -- -- node :: (a -> Tree a -> Tree a -> r) ->
-- -- -- --   ValiGen (Tree a) (Maybe r) (Gen a, Gen (Tree a), Gen (Tree a)) (Tree a)
-- -- -- -- node f =
-- -- -- --   ValiGen
-- -- -- --     (\case Node x left right -> Just $ f x left right; Leaf -> Nothing)
-- -- -- --     (\(xGen, leftGen, rightGen) -> Node <$> xGen <*> leftGen <*> rightGen)

-- -- -- -- -- getIncrement =
-- -- -- -- --   -- total $
-- -- -- -- --   mconcat
-- -- -- -- --   [ red
-- -- -- -- --   ]

-- -- -- -- -- leafR :: Refine (ColorTree ())
-- -- -- -- -- leafR = undefined

-- -- -- -- -- matchColor ::
-- -- -- -- --   (Defined Color -> ST s ()) -> -- | Red
-- -- -- -- --   (Defined Color -> ST s ()) -> -- | Black
-- -- -- -- --   STCell s Color ->
-- -- -- -- --   ST s ()
-- -- -- -- -- matchColor kRed kBlack cell =
-- -- -- -- --   watch cell $ \case
-- -- -- -- --       Known Red -> kRed (Known Red)
-- -- -- -- --       Known Black -> kBlack (Known Black)
-- -- -- -- --       Unknown -> kRed Unknown *> kBlack Unknown
-- -- -- -- --       Inconsistent -> pure ()


-- -- -- -- -- matchColorTree ::
-- -- -- -- --   (Defined () -> ST s ()) -> -- | Leaf
-- -- -- -- --   (Defined (Flat (ColorTree ())) -> ST s ()) -> -- | Node
-- -- -- -- --   STCell s (Flat (ColorTree ())) ->
-- -- -- -- --   ST s ()
-- -- -- -- -- matchColorTree kLeaf kNode cell =
-- -- -- -- --   watch cell $ \case
-- -- -- -- --     Known (Flat Leaf) -> kLeaf (Known ())
-- -- -- -- --     Known (Flat t@(Node {})) -> kNode (Known (Flat t))
-- -- -- -- --     Unknown -> kLeaf Unknown *> kNode Unknown
-- -- -- -- --     Inconsistent -> pure ()

-- -- -- -- -- blackHeightBi' :: forall s. STCell s (Gen (Flat (ColorTree ()))) -> STCell s (Flat (ColorTree ())) -> STCell s (Max Int) -> ST s ()
-- -- -- -- -- blackHeightBi' cellGT cellT cellH = do
-- -- -- -- --   let theMatch = matchColorTree kLeaf kNode cellT
-- -- -- -- --   theMatch
-- -- -- -- --   -- watch cellH (const theMatch)
-- -- -- -- --   where
-- -- -- -- --     kLeaf (Known _) = writeCellSemi cellH (Max 1) $> ()
-- -- -- -- --     kLeaf _ = pure ()

-- -- -- -- --     kNode :: Defined (Flat (ColorTree ())) -> ST s ()
-- -- -- -- --     kNode (Known (Flat (Node (color, _) left right))) = do
-- -- -- -- --       let increment = case color of Red -> 0; Black -> 1

-- -- -- -- --       c <- mkUnknown

-- -- -- -- --       -- Write the (possibly incremented) contents of c into our output cell
-- -- -- -- --       watch c $ \x -> writeDefinedCellSemi cellH (fmap (fmap (+ increment)) x) $> ()

-- -- -- -- --       leftCell <- mkKnown $ Flat left
-- -- -- -- --       rightCell <- mkKnown $ Flat right

-- -- -- -- --       leftCellG <- mkUnknown
-- -- -- -- --       rightCellG <- mkUnknown

-- -- -- -- --       blackHeightBi' leftCellG leftCell c
-- -- -- -- --       blackHeightBi' rightCellG rightCell c

-- -- -- -- --       -- leftG <-
-- -- -- -- --       -- writeCellSemi cellGT (Node <$> leftCellG)
-- -- -- -- --       -- undefined

-- -- -- -- --     kNode Unknown = pure ()

-- -- -- -- -- -- | Bidirectional red-black tree black height checker/generator
-- -- -- -- -- blackHeightBi :: STCellGen s (Flat (ColorTree ())) -> STCell s (Max Int) -> ST s ()
-- -- -- -- -- blackHeightBi cellT cellH = do
-- -- -- -- --   watch cellH $ \case
-- -- -- -- --     Known (Max h) -> do
-- -- -- -- --       writeCell cellT $ GenVal $ Flat <$> withBlackHeight h
-- -- -- -- --       pure ()
-- -- -- -- --     _ -> pure ()

-- -- -- -- --   watch cellT $ \case
-- -- -- -- --     Known (RegularVal t) -> blackHeight (getFlat t) cellH
-- -- -- -- --     Known (GenVal gT) -> pure ()
-- -- -- -- --     _ -> pure ()


-- -- -- -- -- blackHeightBi1 :: ColorTree () -> Int
-- -- -- -- -- blackHeightBi1 t = runST $ do
-- -- -- -- --   cellT <- mkKnown (RegularVal (Flat t))
-- -- -- -- --   cellH <- mkUnknown
-- -- -- -- --   blackHeightBi' cellT cellH
-- -- -- -- --   readCell cellH >>= \case
-- -- -- -- --     Known (Max n) -> pure n
-- -- -- -- --     x -> error $ "blackHeightBi1: " ++ show x

-- -- -- -- -- blackHeightBi2 :: Int -> Gen (ColorTree ())
-- -- -- -- -- blackHeightBi2 h = runST $ do
-- -- -- -- --   cellT <- mkUnknown
-- -- -- -- --   cellH <- mkKnown (Max h)
-- -- -- -- --   blackHeightBi' cellT cellH
-- -- -- -- --   readCell cellT >>= \case
-- -- -- -- --     Known (GenVal g) -> pure $ fmap getFlat g
-- -- -- -- --     Unknown -> error $ "blackHeightBi2: Unknown"

-- -- -- -- -- getColor :: ColorTree a -> Color
-- -- -- -- -- getColor Leaf = Black
-- -- -- -- -- getColor (Node (c, _) _ _) = c

-- -- -- -- -- blackHeight :: ColorTree a -> STCell s (Max Int) -> ST s ()
-- -- -- -- -- blackHeight t output =
-- -- -- -- --   case t of
-- -- -- -- --     Leaf -> writeCellSemi output (Max 1) $> ()
-- -- -- -- --     Node (color, _) left right -> do
-- -- -- -- --       let increment = case color of Black -> 1; Red -> 0

-- -- -- -- --       -- A shared cell for the two recursive calls
-- -- -- -- --       c <- mkUnknown

-- -- -- -- --       -- Write the (possibly incremented) contents of c into our output cell
-- -- -- -- --       watch c $ \x -> writeDefinedCellSemi output (fmap (fmap (+ increment)) x) $> ()

-- -- -- -- --       blackHeight left c
-- -- -- -- --       blackHeight right c

-- -- -- -- -- getBlackHeightCell :: ColorTree a -> Int
-- -- -- -- -- getBlackHeightCell t = runST $ do
-- -- -- -- --   c <- mkUnknown
-- -- -- -- --   blackHeight t c
-- -- -- -- --   readCell c >>= \case
-- -- -- -- --     Unknown -> error "getBlackHeight': Unknown"
-- -- -- -- --     Inconsistent -> error "getBlackHeight': Inconsistent"
-- -- -- -- --     Known (Max x) -> pure x

-- -- -- -- -- -- isBlackHeight :: ColorTree a -> Int -> ST s Bool
-- -- -- -- -- -- isBlackHeight Leaf 1 = pure True
-- -- -- -- -- -- isBlackHeight Leaf _ = pure False
-- -- -- -- -- -- isBlackHeight (Node (Black, _) left right) n =
-- -- -- -- -- --   undefined
-- -- -- -- -- --   -- n == max a
-- -- -- -- -- --   -- &&
-- -- -- -- -- --   -- isBlackHeight left a
-- -- -- -- -- --   -- &&
-- -- -- -- -- --   -- isBlackHeight right b

-- -- -- -- -- withBlackHeight :: Int -> Gen (ColorTree ())
-- -- -- -- -- withBlackHeight 1 = pure Leaf
-- -- -- -- -- withBlackHeight n =
-- -- -- -- --   sized $ \sz ->
-- -- -- -- --   let
-- -- -- -- --     genRed = Node (Red, ()) <$> recApply n <*> recApply n
-- -- -- -- --     genBlack = Node (Black, ()) <$> recApply (n-1) <*> recApply (n-1)

-- -- -- -- --     recApply = resize (sz `div` 2) . withBlackHeight
-- -- -- -- --   in
-- -- -- -- --   if sz <= 1
-- -- -- -- --   then genBlack
-- -- -- -- --   else oneof
-- -- -- -- --        [ genBlack
-- -- -- -- --        , genRed
-- -- -- -- --        ]

-- -- -- -- -- withBlackHeight'valid :: Int -> Property
-- -- -- -- -- withBlackHeight'valid n =
-- -- -- -- --   forAll (withBlackHeight n) $ \t -> getBlackHeight t == n

-- -- -- -- -- getBlackHeightCell'valid :: Int -> Property
-- -- -- -- -- getBlackHeightCell'valid n =
-- -- -- -- --   forAll (withBlackHeight n) $ \t -> getBlackHeightCell t == n

-- -- -- -- -- blackHeightBi1'valid :: Int -> Property
-- -- -- -- -- blackHeightBi1'valid n =
-- -- -- -- --   forAll (withBlackHeight n) $ \t -> blackHeightBi1 t == n

-- -- -- -- -- getBlackHeight :: ColorTree a -> Int
-- -- -- -- -- getBlackHeight Leaf = 1
-- -- -- -- -- getBlackHeight (Node (c, _) left right) =
-- -- -- -- --   increment + max (getBlackHeight left) (getBlackHeight right)
-- -- -- -- --   where
-- -- -- -- --     increment =
-- -- -- -- --       case c of
-- -- -- -- --         Black -> 1
-- -- -- -- --         Red -> 0

-- -- -- -- -- -- getBlackHeight' :: ColorTree () --> Output (Max Int)
