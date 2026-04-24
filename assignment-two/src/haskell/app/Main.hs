{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Main (main) where

main :: IO ()
main = putStrLn "Hello, Haskell!"

{-@ test :: {i : Int | i == 1} @-}
test :: Int
test = 2
