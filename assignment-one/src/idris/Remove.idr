module Remove

import Elem
import Subset
import All

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

public export total
removeFromSubsetStillSubset : {xs, ys : List a} -> {prf : e `Elem` xs} -> xs `Subset` ys -> (remove xs prf) `Subset` ys
removeFromSubsetStillSubset {prf = Here} (_ :: y) = y
removeFromSubsetStillSubset {prf = (KeepLooking y)} (x :: z) =
  let
    ind = removeFromSubsetStillSubset {prf = y} z
  in
  x :: ind

public export total
shrinkDjArb : {prf : something`Elem`xs} -> Disjoint xs ys -> Disjoint (remove xs prf) ys
shrinkDjArb {prf = Here} (_ :: rest) = rest
shrinkDjArb {prf = (KeepLooking further)} (firstNotHere :: rest) = firstNotHere :: shrinkDjArb {prf = further} rest
