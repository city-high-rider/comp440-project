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
notInListNotFirst : Not (thing `Elem` (aHead::aTail)) -> Not (thing `Elem` [aHead])
notInListNotFirst f Here = f Here
notInListNotFirst f (KeepLooking x) = elemInEmptyImpossible x Refl

public export total
notInHeadInTail : (notHead : Not (elem = first)) -> (inList : elem `Elem` (first::rest)) -> elem `Elem` rest
notInHeadInTail notHead Here = absurd (notHead Refl)
notInHeadInTail _ (KeepLooking x) = x

public export total
notInHeadNotInTailNotInList : Not (thing = head) -> Not (thing `Elem` tail) -> Not (thing `Elem` (head::tail))
notInHeadNotInTailNotInList notHead _ Here = notHead Refl
notInHeadNotInTailNotInList _ notInTail (KeepLooking further) = notInTail further

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

public export total
elemSingletonEq : a `Elem` [b] -> a = b
elemSingletonEq Here = Refl
elemSingletonEq (KeepLooking x) = absurd (elemInEmptyImpossible x Refl)

public export total
notElemSingletonNotEq : Not (a `Elem` [b]) -> Not (a = b)
notElemSingletonNotEq f Refl = f Here
