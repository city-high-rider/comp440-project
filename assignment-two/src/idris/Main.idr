module Main

import Data.Nat
import Control.WellFounded
import Decidable.Equality

%default total

Divides : Nat -> Nat -> Type
Divides a b = (k : Nat ** b = k*a)

public export total
neqBump : Not (a = b) -> Not (S a = S b)
neqBump f Refl = f Refl

public export total
neqUnbump : Not (S a = S b) -> Not (a = b)
neqUnbump f Refl = f Refl

public export total
lteStrengthen : {a, b : _} -> LTE a b -> Not (a = b) -> LT a b
lteStrengthen {a = 0} {b = 0} LTEZero f = absurd (f Refl)
lteStrengthen {a = 0} {b = (S k)} LTEZero f = LTESucc LTEZero
lteStrengthen {a = (S left)} {b = (S right)} (LTESucc x) f = 
  let
    fRec = neqUnbump f
  in
  LTESucc (lteStrengthen x fRec)

public export total
modHelp : (r : Nat) -> Nat -> (b : Nat) -> IsSucc b -> (LT r b) -> (rem : Nat ** LT rem b)
modHelp r 0 b bnz rltb = (r ** rltb)
modHelp r (S k) 0 bnz rltb = absurd bnz
modHelp r (S k) (S j) bnz rltb =
  case decEq r j of
    (Yes prf) => modHelp 0 k (S j) bnz (LTESucc LTEZero)
    (No contra) =>
      let
        cbump = neqBump contra
        rltbPrime = lteStrengthen rltb cbump
      in
      modHelp (S r) k (S j) bnz rltbPrime
  

public export total
mod : Nat -> (b : Nat) -> IsSucc b -> (rem : Nat ** LT rem b)
mod a 0 bnz = absurd bnz
mod a (S k) bnz = modHelp 0 a (S k) bnz (LTESucc LTEZero)

public export total
data EucArgPair = MkEPair Nat Nat

Sized EucArgPair where
  size (MkEPair a b) = b

public export total
eucHelper : (x : EucArgPair) -> ((y : EucArgPair) -> Smaller y x -> Nat) -> Nat
eucHelper (MkEPair a 0) rec = a
eucHelper (MkEPair a (S k)) rec =
  let
    (nextRight ** isLess) = mod a (S k) ItIsSucc
  in
  rec (MkEPair (S k) nextRight) isLess

public export total
euc : Nat -> Nat -> Nat
euc a b = sizeRec (eucHelper) (MkEPair a b)
