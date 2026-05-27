{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
module Euclid where

{-@ divides :: a:Int -> b:Int -> Bool @-}
{-@ reflect divides @-}
divides :: Int -> Int -> Bool
0 `divides` 0 = True
_ `divides` 0 = True
0 `divides` _ = False
a `divides` b = b `rem` a == 0

{-@ euc :: a:Int -> b:Int -> Int / [b] @-}
euc :: Int -> Int -> Int
euc a 0 = abs a
euc a b = euc b (a `rem` b)

