module Remove

import Elem

public export total
remove : (xs : List a) -> x `Elem` xs -> List a
remove (x :: rest) Here = rest
remove (something :: rest) (KeepLooking y) = something :: remove rest y

public export total
notRemovedStillThere : {a : Type} -> {list : List a} -> {elem,removeThis : a} -> elem `Elem` list -> (prf : removeThis `Elem` list) -> Not (elem = removeThis) -> elem `Elem` (remove list prf)
notRemovedStillThere Here Here contra = absurd (contra Refl)
notRemovedStillThere Here (KeepLooking x) _ = Here
notRemovedStillThere (KeepLooking x) Here _ = x
notRemovedStillThere (KeepLooking x) (KeepLooking y) contra =
  let
    ind = notRemovedStillThere x y contra
  in
  KeepLooking ind
