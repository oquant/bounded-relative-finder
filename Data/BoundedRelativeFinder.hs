-- |Please see the README for an explanation of what is going on here.

module Data.BoundedRelativeFinder
  ( Shrink(..)
  , emptyShrink
  , shrinkStepTo
  , shrinkAt
  , shrinkOrDeleteAt
  , shrinkAll
  , shrinkOrDeleteAll
  , shrinkHead
  , shrinkOrDeleteHead
  , shrinkText
  , shrinkByteString
  , shrinkTree
  , buildShrinkDict
  , ShrinkAt(..)
  , uniqueShrinksBreadth
  , uniqueShrinksDepth
  , queryD
  , queryB
  ) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Writer.Lazy
import Control.Monad.State.Lazy
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Data.ByteString(ByteString)
import qualified Data.ByteString as ByteString
import Data.Containers.ListUtils
import Data.Foldable
import Data.Graph(Forest, Tree(..))
import qualified Data.Graph as Graph
import qualified Data.Hashable as Hashable
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.STRef
import Data.Text(Text)
import qualified Data.Text as Text
import Data.Tuple
import qualified Data.Vector.Unboxed as UV
import GHC.Generics

import Data.BoundedRelativeFinder.Internal.IntMap(IntMap)
import qualified Data.BoundedRelativeFinder.Internal.IntMap as IntMap

-- |A `Shrink a` is a way to find all of the elements that an `a` value covers.
-- For `ray :: Shrink a` to be well-behaved (see the README):
-- `elem x (shrink ray z) && elem y (shrink ray z) && y /= z` implies
-- `not (null (intersect (shrink ray x) (shrink ray y))`.
-- This is equivalent to stating that the poset defined by the covering relation
-- `x <| y = elem x (shrink ray y)` is lower-semimodular.
newtype Shrink a =
  Shrink {
    shrink :: a -> [a]
  }

-- |Generates the trivial ordering.
emptyShrink :: Shrink a
emptyShrink = Shrink (const [])

-- |Shrinking is moving by `step` toward `to`.
shrinkStepTo :: (Num a, Ord a) => a -> a -> Shrink a
shrinkStepTo step to = Shrink $ \n ->
  if n < to then [min to (n + step)]
  else if n > to then [max to (n - step)]
  else []

orIfEmpty :: [a] -> [a] -> [a]
orIfEmpty [] xs = xs
orIfEmpty xs _ = xs

-- |Triangular if the input is.
shrinkAt :: Shrink a -> Int -> Shrink [a]
shrinkAt ray n = Shrink $ \xs ->
  case splitAt n xs of
    (_, []) -> error "shrinkListAt: can't shrink at positions off the end of the list"
    (as, b:bs) -> [as ++ (p : bs) | p <- shrink ray b]

-- |Triangular if the input is.
shrinkOrDeleteAt :: Shrink a -> Int -> Shrink [a]
shrinkOrDeleteAt ray n = Shrink $ \xs ->
  case splitAt n xs of
    (_, []) -> error "shrinkOrDeleteAt: can't shrink at positions off the end of the list"
    (as, b:bs) -> [as ++ (p : bs) | p <- shrink ray b] `orIfEmpty` [as ++ bs]

-- |Try to shrink each element or delete it if we can't. Triangular if the input is.
shrinkOrDeleteAll :: Shrink a -> Shrink [a]
shrinkOrDeleteAll ray = Shrink $ \xs ->
  concat [shrink (shrinkOrDeleteAt ray n) xs | n <- [0..length xs - 1]]

-- |Try to shrink each element. Triangular if the input is.
shrinkAll :: Shrink a -> Shrink [a]
shrinkAll ray = Shrink $ \xs ->
  concat [shrink (shrinkAt ray n) xs | n <- [0..length xs - 1]]

-- |Try to shrink the head or delete it if we can't. Triangular if the input is.
shrinkHead :: Shrink a -> Shrink [a]
shrinkHead ray = Shrink $ \xs -> if null xs then [] else shrink (shrinkAt ray 0) xs

shrinkOrDeleteHead :: Shrink a -> Shrink [a]
shrinkOrDeleteHead ray = shrinkOrDeleteAt ray 0

shrinkText :: Shrink Text
shrinkText = Shrink $ \str -> [deleteAt n str | n <- [0..Text.length str - 1]]
  where
  deleteAt n str =
    let (as, bs) = Text.splitAt n str in as <> Text.tail bs

shrinkByteString :: Shrink ByteString
shrinkByteString = Shrink $ \bstr -> [deleteAt n bstr | n <- [0..ByteString.length bstr - 1]]
  where
  deleteAt n bstr =
    let (as, bs) = ByteString.splitAt n bstr in as <> ByteString.tail bs

-- |Try to shrink each forest of children recursively or delete it if we can't; try to shrink each value if we can.
shrinkTree :: Shrink a -> Shrink (Tree a)
shrinkTree ray = go
  where
  go = Shrink $ \t -> case t of
    Node x f ->
      (Node <$> shrink ray x <*> pure f) ++
      (Node x <$> shrink shrinkForest f)
  shrinkForest = shrinkAll go

data FiatHashed a = FiatHashed !Int !a
  deriving (Ord, Eq)

instance Hashable.Hashable (FiatHashed a) where
  hashWithSalt s (FiatHashed h _) = Hashable.hashWithSalt s h

fiatHashedWith :: (a -> Int) -> a -> FiatHashed a
fiatHashedWith hash a = FiatHashed (hash a) a

-- |A dictionary: the keys are the hashes of shrink results.
-- Hash collisions are possible, so the user has to double-check shrink distances after querying.
data ShrinkDict = ShrinkDict
  { dictShrinkDepth :: !Int
  , shrinkDict :: !IntMap
  }
  deriving (Show, Eq, Generic)

buildShrinkDict :: (v -> Int) -> Shrink v -> Int -> [v] -> ShrinkDict
buildShrinkDict hash ray shrinkDepth starts =
  ShrinkDict shrinkDepth $ go mempty 0 (zip starts [0..])
  where
  go !acc n _ | n > shrinkDepth = acc
  go !acc _ [] = acc
  go !acc n xs = go nextAcc (n+1) deletions
    where
    nextAcc =
      IntMap.unionWith uvMerge acc $
        IntMap.fromListWith uvMerge [(hash a, UV.singleton i) | (a, i) <- xs]
    deletions = concatMap (\(a, i) -> (,i) <$> shrink ray a) xs
    uvMerge x y = UV.fromListN (UV.length x + UV.length y) (merge (UV.toList x) (UV.toList y))
    merge (x:xs) (y:ys)
      | x == y = x : merge xs ys
      | x < y = x : merge xs (y:ys)
      | y < x = y : merge (x:xs) ys
    merge xs [] = xs
    merge [] ys = ys

-- |Helper for doing breadth-first traversal of query results.
traverseQueue' :: MonadFix m => (a -> m [a]) -> [a] -> m [a]
traverseQueue' gen start = mdo ins <- go (length start) (start ++ ins)
                               pure (start ++ ins)
  where go 0 _ = pure []
        go n (x:xs) = do ins <- gen x
                         ins' <- go (n - 1 + length ins) xs
                         pure (ins ++ ins')

allShrinksTo :: Shrink a -> Int -> a -> [a]
allShrinksTo ray depth a = a : concatMap (allShrinksTo ray (depth - 1)) (shrink ray a)

data ShrinkAt a = ShrinkAt
  { shrinkDepth :: !Int
  , shrunk :: !a
  , shrunkHash :: !Int
  }

uniqueShrinksBreadth :: (Ord a) => (a -> Int) -> Shrink a -> Int -> a -> [ShrinkAt a]
uniqueShrinksBreadth hash ray depth a =
  -- we could start with `HashSet.singleton (hashed a)`, but we're guaranteed
  -- not to ever find `a` as a result of shrinking `a`
  evalState (traverseQueue' gen [ShrinkAt 0 a (hash a)]) HashSet.empty
  where
  gen sh = do
    seen <- get
    if shrinkDepth sh == depth
    then pure []
    else do
      let shrinks = fiatHashedWith hash <$> shrink ray (shrunk sh)
      let filteredShrinks = nubOrd $ filter (not . flip HashSet.member seen) shrinks
      modify' (HashSet.union (HashSet.fromList filteredShrinks))
      pure $ (\(FiatHashed h a) -> ShrinkAt (shrinkDepth sh + 1) a h) <$> filteredShrinks

uniqueShrinksDepth :: (Eq a) => (a -> Int) -> Shrink a -> Int -> a -> [ShrinkAt a]
uniqueShrinksDepth hash ray depth x = evalState (go 0 (FiatHashed (hash x) x)) HashSet.empty
  where
  go n fh@(FiatHashed h a) = do
    seen <- get
    let announceNewShrink = modify (HashSet.insert fh)
    if HashSet.member fh seen then pure []
    else if n == depth then announceNewShrink *> pure [ShrinkAt n a h]
    else do
      let shrinks = fiatHashedWith hash <$> shrink ray a
      announceNewShrink
      (ShrinkAt n a h:) . concat <$> traverse (go (n+1)) shrinks

queryDict dict s =
  fromMaybe UV.empty (IntMap.lookup (shrunkHash s) (shrinkDict dict))

-- |Streams the matching dictionary entries ordered by query depth.
-- This is done by traversing the deletions of the query term breadth-first.
-- In practice this means that the results are ordered by how much backtracking from the query term was required.
-- The cost is a larger live set than queryD.
queryB :: (Ord a) => (a -> Int) -> Shrink a -> Int -> ShrinkDict -> a -> [(ShrinkAt a, UV.Vector Int)]
queryB hash ray shrinkDepth dict i =
  [ (s, queryDict dict s)
  | !s <- uniqueShrinksBreadth hash ray shrinkDepth i ]

-- |Streams the matching dictionary entries traversing the deletions of the query term depth-first.
-- smaller live set than `queryB`, but the results don't have much interesting order to them.
queryD :: (Eq a) => (a -> Int) -> Shrink a -> Int -> ShrinkDict -> a -> [(ShrinkAt a, UV.Vector Int)]
queryD hash ray shrinkDepth dict i =
  [ (s, queryDict dict s)
  | !s <- uniqueShrinksDepth hash ray shrinkDepth i ]

