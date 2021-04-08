-- |Please see the README for an explanation of what is going on here.

module Data.BoundedRelativeFinder
  ( Shrink(..)
  , emptyShrink
  , shrinkListEverywhere
  , shrinkListHead
  , shrinkText
  , shrinkByteString
  , buildShrinkDict
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
import Data.Hashable
import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.STRef
import Data.Text(Text)
import qualified Data.Text as Text
import Data.Tuple
import qualified Data.Vector.Unboxed as UV
import GHC.Generics

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

orIfEmpty :: [a] -> [a] -> [a]
orIfEmpty [] xs = xs
orIfEmpty xs _ = xs

-- |Try to shrink one element or delete it if we can't.
shrinkListEverywhere :: Shrink a -> Shrink [a]
shrinkListEverywhere ray = Shrink $ \xs ->
  concat [shrinkOrDeleteAt n xs | n <- [0..length xs - 1]]
  where
  shrinkOrDeleteAt n xs =
    [as ++ (p : bs) | p <- shrink ray b] `orIfEmpty` [as ++ bs]
    where (as, b:bs) = splitAt n xs

shrinkListHead :: Shrink a -> Shrink [a]
shrinkListHead ray = Shrink go
  where
  go [] = []
  go (x:xs) = ((:xs) <$> shrink ray x) `orIfEmpty` [xs]

shrinkText :: Shrink Text
shrinkText = Shrink $ \str -> [ deleteAt n str | n <- [0..Text.length str - 1] ]
  where
  deleteAt n str =
    let (as, bs) = Text.splitAt n str in as <> Text.tail bs

shrinkByteString :: Shrink ByteString
shrinkByteString = Shrink $ \bstr -> [ deleteAt n bstr | n <- [0..ByteString.length bstr - 1] ]
  where
  deleteAt n bstr =
    let (as, bs) = ByteString.splitAt n bstr in as <> ByteString.tail bs

-- |A dictionary: the keys are the hashes of shrink results.
-- Hash collisions are possible, so the user has to double-check shrink distances after querying.
newtype ShrinkDict k = ShrinkDict (IntMap [k])
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

buildShrinkDict :: (Ord k, Hashable v) => Shrink v -> Int -> [(k, v)] -> ShrinkDict k
buildShrinkDict ray shrinkDepth starts =
  ShrinkDict $ go mempty 0 (fmap swap starts)
  where
  go !acc n _ | n > shrinkDepth = acc
  go !acc _ [] = acc
  go !acc n xs = go nextAcc (n+1) deletions
    where
    nextAcc = IntMap.unionWith (\x y -> nubOrd (x <> y)) acc (IntMap.fromListWith (<>) [(hash a, [i]) | (a, i) <- xs])
    deletions = concatMap (\(a, i) -> (,i) <$> shrink ray a) xs

-- |Helper for doing breadth-first traversal of query results.
traverseQueue' :: MonadFix m => (a -> m [a]) -> [a] -> m [a]
traverseQueue' gen start = mdo ins <- go (length start) (start ++ ins)
                               pure ins
  where go 0 _ = pure []
        go n (x:xs) = do ins <- gen x
                         ins' <- go (n - 1 + length ins) xs
                         pure (ins ++ ins')

-- |Streams the matching dictionary entries ordered by query depth.
-- This is done by traversing the deletions of the query term breadth-first.
-- In practice this means that the results are ordered by how much backtracking from the query term was required.
-- The cost is a larger live set than queryD.
queryB :: (Eq a, Hashable a) => Shrink a -> Int -> ShrinkDict k -> a -> [[k]]
queryB ray shrinkDepth (ShrinkDict delDict) i = snd $ runWriter $ evalStateT (traverseQueue' gen [(i, 0)]) HashSet.empty
  where
  gen (x, n) = do
    seen <- get
    if HashSet.member h seen
    then pure []
    else do
      modify (HashSet.insert h)
      tell [entries]
      pure $ guard (n + 1 <= shrinkDepth) *> newIns
      where
      h = hashed x
      entries = fromMaybe [] (IntMap.lookup (hash h) delDict)
      newIns = fmap (,n + 1) (shrink ray x)

-- |Streams the matching dictionary entries traversing the deletions of the query term depth-first.
-- smaller live set than `queryB`, but the results don't have much interesting order to them.
queryD :: (Eq a, Hashable a) => Shrink a -> Int -> ShrinkDict k -> a -> [[k]]
queryD ray shrinkDepth (ShrinkDict delDict) i =
  evalState (go 0 i) HashSet.empty
  where
  go n x = do
    seen <- get
    if HashSet.member h seen
    then pure []
    else do
      modify' (HashSet.insert h)
      rest <-
        if n + 1 <= shrinkDepth
        then concat <$> traverse (go (n + 1)) (shrink ray x)
        else pure []
      pure $ des : rest
    where
    h = hashed x
    des = fromMaybe [] (IntMap.lookup (hash h) delDict)

