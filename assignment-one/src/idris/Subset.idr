module Subset 

import Elem
import All

%default total

public export total
Subset : List a -> List a -> Type
Subset xs ys = All (`Elem`ys) xs

public export total
smallerSubsetIsSubset : (x :: xs) `Subset` ys -> xs `Subset` ys
smallerSubsetIsSubset (_ :: z) = z

public export total
SsEq : List a -> List a -> Type 
SsEq a b = (a `Subset` b, b `Subset` a) 

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

public export total
Disjoint : List a -> List a -> Type
Disjoint as bs = All (\thing => Not (thing`Elem`bs)) as

public export total
disjointNotInBoth : Disjoint xs ys -> Not (x ** (x`Elem`xs, x`Elem`ys))
disjointNotInBoth disjPrf (something ** (inXs, inYs)) =
  let
    somethingNotInYs : Not (something `Elem` ys) = extractPrf inXs disjPrf
  in
  somethingNotInYs inYs

public export total
notInBothSym : {xs,ys : List a} -> Not (x ** (x`Elem`xs, x`Elem`ys)) -> Not (x ** (x`Elem`ys, x`Elem`xs))
notInBothSym contra (x ** (inYs, inXs)) = contra (x ** (inXs, inYs))

public export total
growDj : All (\thing => Elem thing oldSet -> Void) ys -> (Elem newThing ys -> Void) -> All (\thing => Elem thing (newThing :: oldSet) -> Void) ys

public export total
disjointSym : {xs, ys : List a} -> Disjoint xs ys -> Disjoint ys xs
disjointSym VacuouslyTrue = forAllForSome (\_, prf => elemInEmptyImpossible prf Refl)
disjointSym (firstNotInYs :: restNotInYs) =
  let
    ind = disjointSym restNotInYs
  in
  growDj ind firstNotInYs
   
public export total
shrinkDj : Disjoint xs (y::ys) -> Disjoint xs ys
shrinkDj VacuouslyTrue = VacuouslyTrue
shrinkDj (fstDj :: restDj) =
  let
    ind = shrinkDj restDj
  in
  (notInListNotFurther fstDj) :: ind


