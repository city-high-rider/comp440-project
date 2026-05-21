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

public export total
divLem : {a,b,q,r,d : Nat} -> a=q*b+r -> Divides d b -> Divides d r -> Divides d a
divLem prf (k1 ** p1) (k2 ** p2) =
  rewrite prf in
  rewrite p1 in
  rewrite p2 in
  rewrite (multAssociative q k1 d) in
  rewrite sym (multDistributesOverPlusLeft (q*k1) k2 d) in
  (plus (mult q k1) k2 ** Refl)

public export total
sumZeroArgsZero : {a,b : Nat} -> a + b = 0 -> (a = 0, b = 0)
sumZeroArgsZero {a = 0} {b = 0} Refl = (Refl, Refl)
sumZeroArgsZero {a = 0} {b = (S k)} prf impossible
sumZeroArgsZero {a = (S k)} {b = 0} prf impossible
sumZeroArgsZero {a = (S k)} {b = (S j)} prf impossible

public export total
plusConstCancelLeft : (c : Nat) -> (l : Nat) -> (r : Nat) -> c+l = c+r -> l=r 
plusConstCancelLeft 0 l l Refl = Refl
plusConstCancelLeft (S k) l r prf =
  plusConstCancelLeft k l r (injective prf)

public export total
divCancelLem : 
  (k1 : Nat) ->
  (k2 : Nat) ->
  (d : Nat) ->
  (r : Nat) ->
  (k1 * d = k2 * d + r) ->
  Divides d r
divCancelLem k1 0 d r prf = (k1 ** rewrite prf in Refl)
divCancelLem 0 (S n) d r prf =
  let
    (_, rzero) = sumZeroArgsZero (sym prf)
  in
  (0 ** rzero)
divCancelLem (S m) (S n) d r prf =
  let
    prf' : (d+m*d = d+(n*d+r)) = rewrite (plusAssociative d (n*d) r) in prf
  in
  divCancelLem m n d r (rewrite (plusConstCancelLeft d (m*d) (n*d+r) prf') in Refl)

public export total
data EucArgPair = MkEPair Nat Nat

Sized EucArgPair where
  size (MkEPair a b) = b

public export total
EucProp : EucArgPair -> Type
EucProp (MkEPair l r) = (d : Nat ** (Divides d l, Divides d r))

public export total
eucHelper : (x : EucArgPair) -> ((y : EucArgPair) -> Smaller y x -> EucProp y) -> EucProp x
eucHelper (MkEPair a 0) _ =
  (a **
    ( (1 ** rewrite plusZeroRightNeutral a in Refl)
    , (0 ** Refl)
    ))
eucHelper theseArgs@(MkEPair a (S p)) rec =
  let
    (q ** r ** (rltb, prfArith)) = mod a (S p) ItIsSucc
    (dRec ** (p1, p2)) = rec (MkEPair (S p) r) rltb
    dda : Divides dRec a = divLem prfArith p1 p2
  in
  (dRec ** (dda, p1))

public export total
euc : (a : Nat) -> (b : Nat) -> (c : Nat ** (Divides c a, Divides c b))
euc a b = sizeInd {P = EucProp} (eucHelper) (MkEPair a b)

