module Subset 

import Elem
import All

%default total

public export
Subset : List a -> List a -> Type
Subset xs ys = All (`Elem`ys) xs

public export
SsEq : List a -> List a -> Type 
SsEq a b = (a `Subset` b, b `Subset` a) 

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


