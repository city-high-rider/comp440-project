module Elem

%default total

public export
data Elem : a -> List a -> Type where
  Here : Elem x (x::xs)
  KeepLooking : Elem x rest -> Elem x (something :: rest)

test : Elem 2 [0,1,2,3]
test = KeepLooking (KeepLooking Here)

public export total
elemInEmptyImpossible : Elem _ list -> list = [] -> Void
elemInEmptyImpossible Here Refl impossible
elemInEmptyImpossible (KeepLooking x) Refl impossible

public export total
notInListNotFurther : Not (thing `Elem` (aHead::aTail)) -> Not (thing `Elem` aTail)
notInListNotFurther f Here = f (KeepLooking Here)
notInListNotFurther f (KeepLooking x) = f (KeepLooking (KeepLooking x))

public export total
notEqByMembership : Not (a `Elem` someList) -> b `Elem` someList -> Not (a = b)
notEqByMembership {someList = b :: restList} aInXsContra Here aIsB =
  let
    hereIsContra = replace {p = \lhs => lhs `Elem` (b :: restList) -> Void} aIsB aInXsContra
  in
  hereIsContra Here
notEqByMembership {someList = something :: restList} aInXsContra (KeepLooking bFurther) aIsB =
  let
    aFurther = replace {p = \lhs => lhs`Elem`restList} (sym aIsB) bFurther
    aHere : a `Elem` (something::restList) = KeepLooking aFurther
  in
  aInXsContra aHere
