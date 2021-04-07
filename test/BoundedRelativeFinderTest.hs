{-# language OverloadedStrings #-}
{-# language BlockArguments #-}

module Main (main) where

import Data.Hashable
import Data.List
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Debug.Trace

import Data.BoundedRelativeFinder

--
zeroDistance :: (Eq a, Ord a, Hashable a, Show a) => Gen a -> Shrink a -> Property
zeroDistance g d = property $ do
  xs <- forAll (Gen.list (Range.linear 0 100) g)
  let dict = buildShrinkDict d 0 (zip [0..] xs)
  assert $ all (\x -> sort ((xs !!) . _entryReference . _resultEntry <$> concat (queryD d 0 dict x)) == sort (filter (== x) xs)) xs

main :: IO ()
main =
  () <$ checkParallel (Group "symmetric-relative-finder"
    [ ("values with zero distance are equal", zeroDistance (Gen.string (Range.linear 0 4) Gen.alpha) (shrinkListEverywhere emptyShrink))
    ])


