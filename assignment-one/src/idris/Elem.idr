module Elem

import All

%default total

public export
data Elem : a -> List a -> Type where
  Here : Elem x (x::xs)
  KeepLooking : Elem x rest -> Elem x (something :: rest)

test : Elem 2 [0,1,2,3]
test = KeepLooking (KeepLooking Here)

SsEq : List a -> List a -> Type 
SsEq a b = (All (`Elem`b) a, All (`Elem`a) b) 

test1 : SsEq [1,2] [2, 1]
test1 = (KeepLooking Here :: (Here :: VacuouslyTrue), KeepLooking Here :: (Here :: VacuouslyTrue))

