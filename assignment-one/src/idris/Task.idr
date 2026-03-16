module Task

import All
import Elem
import Subset

%default total

export
data Task : Type where
  MkTask : Nat -> Task

export
Eq Task where
  (MkTask a) == (MkTask b) = a == b

public export
data DAG : List Task -> Type where
  Empty : DAG []
  AddTask : (t : Task) -> (deps : List Task) -> deps `Subset` tasks -> DAG tasks -> DAG (t :: tasks)

public export
deps : DAG ts -> (t : Task) -> t `Elem` ts -> List Task 
deps (AddTask t xs _ _) t Here = xs
deps (AddTask _ _ _ rest) t (KeepLooking prf) = deps rest t prf
