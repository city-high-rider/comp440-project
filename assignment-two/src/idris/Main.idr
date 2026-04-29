module Main

import Data.Nat

%default total

Divides : Nat -> Nat -> Type
Divides a b = (k : Nat ** b = k*a)

public export total
modHelp : Nat -> Nat -> Nat -> (b : Nat) -> IsSucc b -> Nat
modHelp k rem a 0 x = absurd x
modHelp k rem 0 (S j) x = rem
modHelp k rem (S i) (S j) x =
  if rem == j
     then modHelp (S k) Z i (S j) ItIsSucc 
     else modHelp k (S rem) i (S j) ItIsSucc

public export total
mod : Nat -> (b : Nat) -> IsSucc b -> Nat
mod = modHelp 0 0

public export partial
euc : Nat -> Nat -> Nat
euc a 0 = a
euc a (S j) = euc (S j) (mod a (S j) ItIsSucc)
