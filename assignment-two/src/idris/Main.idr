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
modHelp :
  (q : Nat) ->
  (r : Nat) ->
  (remaining : Nat) ->
  (b : Nat) ->
  IsSucc b ->
  LT r b ->
  (q' : Nat ** r' : Nat ** ( LT r' b, q' * b + r' = q * b + r + remaining))
modHelp q r 0 b bnz rltb = (q ** r ** (rltb, rewrite (plusZeroRightNeutral (plus (mult q b) r)) in Refl))
modHelp q r (S k) 0 bnz rltb = absurd bnz
modHelp q r (S k) (S j) bnz rltb =
  case decEq r j of
       (Yes Refl) =>
          let
            (qrec ** rrec ** (rrltb, prf)) = modHelp (S q) 0 k (S j) bnz (LTESucc LTEZero)
          in
          (qrec ** rrec ** (rrltb,
          rewrite prf in
          rewrite plusZeroRightNeutral (plus r (mult q (S r))) in
          rewrite plusSuccRightSucc (plus r (mult q (S r))) k in
          rewrite plusCommutative r (mult q (S r)) in Refl))
       (No contra) =>
          let
            nextPrf = lteStrengthen rltb (neqBump contra)
            (qrec ** rrec ** (rrltb, prf)) = modHelp q (S r) k (S j) bnz nextPrf
          in
          (qrec ** rrec ** (rrltb,
          rewrite prf in
          rewrite sym (plusSuccRightSucc (mult q (S j)) r) in
          rewrite plusSuccRightSucc (plus (mult q (S j)) r) k in Refl))


public export total
mod : (a : Nat) -> (b : Nat) -> IsSucc b -> (q : Nat ** rem : Nat ** (LT rem b, a=q*b+rem))
mod a 0 bnz = absurd bnz
mod a (S k) bnz =
  let
    (q ** r ** (rltb, prf)) = modHelp 0 0 a (S k) bnz (LTESucc LTEZero)
  in
  (q ** r ** (rltb, sym prf))

{-

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

-}
