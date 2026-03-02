module All

%default total

public export
data All : (pred : a -> Type) -> List a -> Type where
  VacuouslyTrue : All pred []
  (::) : {x: a} -> pred x -> All pred xs -> All pred (x :: xs)
