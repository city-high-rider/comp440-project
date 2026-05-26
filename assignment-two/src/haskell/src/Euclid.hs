{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
module Euclid where

main :: IO ()
main = putStrLn "Hello, Haskell!"

{-@ reflect euc @-}
{-@ euc :: a:Nat -> b:Nat -> Nat / [b] @-}
euc :: Int -> Int -> Int
euc a 0 = a
euc a b = euc b (a `mod` b)

