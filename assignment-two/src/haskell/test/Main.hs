module Main where

import Test.QuickCheck
import Euclid

prop_eucCommonDiv :: Int -> Int -> Bool
prop_eucCommonDiv a b =
  let
    c = euc a b
    cDivA = a `mod` c == 0
    cDivB = b `mod` c == 0
  in
  cDivA && cDivB

main :: IO ()
main = do
  putStrLn "Running QuickCheck tests..."
  quickCheck prop_eucCommonDiv

