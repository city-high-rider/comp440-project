module Task

import All
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
