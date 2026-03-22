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
subsetShrink : {aHead, aTail, someList : _} ->  someList `Subset` (aHead :: aTail) -> Not (aHead `Elem` someList) -> someList `Subset` aTail
subsetShrink VacuouslyTrue headNotInList = VacuouslyTrue
subsetShrink (Here :: restHere) headNotInList = absurd (headNotInList Here)
subsetShrink ((KeepLooking firstFurther) :: restHere) headNotInList =
  let
    ind = subsetShrink restHere (notInListNotFurther headNotInList)
  in
  firstFurther :: ind

public export total
extractFurtherLemma : {x, aHead : a} -> {aTail, someList : List a} -> {ssTail : All (\arg => arg `Elem` aTail) someList} -> {elemInList : x `Elem` someList} -> {somePrf : x `Elem` aTail} -> {ssHeadTail : All (\arg => arg `Elem` (aHead::aTail)) someList} -> (somePrf = extractPrf {prop = \arg => arg `Elem` aTail} elemInList ssTail) -> (KeepLooking somePrf = (extractPrf {prop = \arg => arg `Elem` (aHead::aTail)} elemInList ssHeadTail))
