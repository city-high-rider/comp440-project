module Subset 

import Elem
import All

%default total

public export total
Subset : List a -> List a -> Type
Subset xs ys = All (`Elem`ys) xs

public export total
SsEq : List a -> List a -> Type 
SsEq a b = (a `Subset` b, b `Subset` a) 

public export total
extractPrf : x `Elem` xs -> All prop xs -> prop x
extractPrf Here (y :: _) = y
extractPrf (KeepLooking y) (_ :: w) = extractPrf y w

total
listContainsItsContents : {list : _} -> All (`Elem`list) list
listContainsItsContents {list = []} = VacuouslyTrue
listContainsItsContents {list = (x :: xs)} =
  let
    ind = listContainsItsContents {list = xs}
    xIsHere : x `Elem` (x::xs) = Here
    ifTheyreInHereTheyreInTheSuperset = propImplies (\_ => KeepLooking) ind
  in
  xIsHere :: ifTheyreInHereTheyreInTheSuperset

public export total
ssEqRefl : {a : _} -> a `SsEq` a
ssEqRefl = (listContainsItsContents, listContainsItsContents)

public export total
ssEqSym : a `SsEq` b -> b `SsEq` a
ssEqSym (x, y) = (y, x)

public export total
ssEqTrans : {a,b,c : _} -> a `SsEq` b -> b `SsEq` c -> a `SsEq` c
ssEqTrans (assb, bssa) (bssc, cssb) =
  let
    assc = propImplies (\_, einb => extractPrf einb bssc) assb
    cssa = propImplies (\_, einb => extractPrf einb bssa) cssb
  in
  (assc, cssa)

public export
data One : (pred : a -> Type) -> List a -> Type where
  ThisOne : (x : a) -> pred x -> One pred (x::rest) 
  Further : One pred xs -> One pred (x::xs)

public export total
Cover : List (List a) -> List a -> Type
xs `Cover` y = All (\elem => One (\subset => elem `Elem` subset) xs ) y

total
coverTest : [[1, 2], [2]] `Cover` [1, 2]
coverTest = ThisOne [1, 2] Here :: (ThisOne [1, 2] (KeepLooking Here) :: VacuouslyTrue)
