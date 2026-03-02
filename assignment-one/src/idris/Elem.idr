module Elem

import All

%default total

public export
data Elem : a -> List a -> Type where
  Here : Elem x (x::xs)
  KeepLooking : Elem x rest -> Elem x (something :: rest)

test : Elem 2 [0,1,2,3]
test = KeepLooking (KeepLooking Here)

public export
SsEq : List a -> List a -> Type 
SsEq a b = (All (`Elem`b) a, All (`Elem`a) b) 

test1 : SsEq [1,2] [2, 1]
test1 = (KeepLooking Here :: (Here :: VacuouslyTrue), KeepLooking Here :: (Here :: VacuouslyTrue))

public export
extractPrf : x `Elem` xs -> All prop xs -> prop x
extractPrf Here (y :: _) = y
extractPrf (KeepLooking y) (_ :: w) = extractPrf y w

listContainsItsContents : {list : _} -> All (`Elem`list) list
listContainsItsContents {list = []} = VacuouslyTrue
listContainsItsContents {list = (x :: xs)} =
  let
    ind = listContainsItsContents {list = xs}
    xIsHere : x `Elem` (x::xs) = Here
    ifTheyreInHereTheyreInTheSuperset = propImplies (\_ => KeepLooking) ind
  in
  xIsHere :: ifTheyreInHereTheyreInTheSuperset

public export
ssEqRefl : {a : _} -> a `SsEq` a
ssEqRefl = (listContainsItsContents, listContainsItsContents)

public export
ssEqSym : a `SsEq` b -> b `SsEq` a
ssEqSym (x, y) = (y, x)

public export
ssEqTrans : {a,b,c : _} -> a `SsEq` b -> b `SsEq` c -> a `SsEq` c
ssEqTrans (assb, bssa) (bssc, cssb) =
  let
    assc = propImplies (\_, einb => extractPrf einb bssc) assb
    cssa = propImplies (\_, einb => extractPrf einb bssa) cssb
  in
  (assc, cssa)


