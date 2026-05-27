module Main where

import Test.QuickCheck
import Euclid

prop_eucCommonDiv :: Int -> Int -> Property
prop_eucCommonDiv a b =
  let
    c = euc a b
  in
  property $ (c `divides` a) && (c `divides` b)

prop_eucGreatestDiv :: Int -> Int -> Property
prop_eucGreatestDiv a b =
  euc a b === gcd a b


main :: IO ()
main = do
  putStrLn "Testing commonDiv property"
  quickCheck prop_eucCommonDiv
  putStrLn "Testing gcd property"
  quickCheck prop_eucGreatestDiv

