{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
module Main (main) where

main :: IO ()
main = putStrLn "Hello, Haskell!"

{-@ test :: {i : Int | i == 2} @-}
test :: Int
test = 2

{-@ euc :: a:Nat -> b:Nat -> Nat / [b]@-}
euc :: Int -> Int -> Int
euc a 0 = a
euc a b = euc b (a `mod` b)
