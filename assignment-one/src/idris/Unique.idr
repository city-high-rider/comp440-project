module Unique

import Elem

%default total

public export
data Unique : List a -> Type where
  EmptyUnique : Unique []
  ConsUnique : Not (new `Elem` rest) -> Unique rest -> Unique (new::rest)
