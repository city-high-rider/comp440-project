module Remove

import Elem
import Subset
import All
import Unique

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

public export total
removeUniqueNotThere : {prf : Elem thing xs} -> Unique xs -> Not (thing `Elem` (remove xs prf))
removeUniqueNotThere {prf = Here} (ConsUnique f x) Here = f Here
removeUniqueNotThere {prf = Here} (ConsUnique f _) (KeepLooking y) = f (KeepLooking y)
removeUniqueNotThere {prf = (KeepLooking further)} (ConsUnique f _) Here = f further
removeUniqueNotThere {prf = (KeepLooking further)} (ConsUnique f x) (KeepLooking y) = removeUniqueNotThere {prf = further} x y

public export total
notHereNotInRemoved : {prf : Elem something xs} -> Not (thing`Elem`xs) -> Not (Elem thing (remove xs prf)) 
notHereNotInRemoved {prf = Here} f x = f (KeepLooking x)
notHereNotInRemoved {prf = (KeepLooking y)} f Here = f Here
notHereNotInRemoved {prf = (KeepLooking y)} f (KeepLooking x) =
  notHereNotInRemoved {prf = y} (notInListNotFurther f) x

public export total
removeUniqueStillUnique : {prf : Elem thing xs} -> Unique xs -> Unique (remove xs prf)
removeUniqueStillUnique {prf = Here} (ConsUnique _ x) = x
removeUniqueStillUnique {prf = (KeepLooking further)} (ConsUnique f x) =
  let
    ind = removeUniqueStillUnique {prf = further} x
  in
  ConsUnique (notHereNotInRemoved f) ind

public export total
removeShrinkLen : {xs : List a} -> {prf : Elem x xs} -> S (length (remove xs prf)) = length xs
removeShrinkLen {xs = []} = absurd (elemInEmptyImpossible prf Refl)
removeShrinkLen {xs = (_ :: _)} {prf = Here} = Refl
removeShrinkLen {xs = (_ :: rest)} {prf = (KeepLooking z)} =
  let
    ind = removeShrinkLen {xs = rest, prf = z}
  in
  rewrite ind in Refl
