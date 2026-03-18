module All

import Elem

%default total

public export
data All : (pred : a -> Type) -> List a -> Type where
  VacuouslyTrue : All pred []
  (::) : {x: a} -> pred x -> All pred xs -> All pred (x :: xs)

export
propImplies : {prem1, prem2 : a -> Type} -> ((e : a) -> prem1 e -> prem2 e) -> All prem1 es -> All prem2 es
propImplies f VacuouslyTrue = VacuouslyTrue
propImplies f (cur :: rest) = f _ cur :: propImplies f rest

public export total
extractPrf : x `Elem` xs -> All prop xs -> prop x
extractPrf Here (y :: _) = y
extractPrf (KeepLooking y) (_ :: w) = extractPrf y w

