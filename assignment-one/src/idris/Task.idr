module Task

import All
import Elem
import Decidable.Equality
import Data.Nat
import Subset

%default total

public export
Task : Type
Task = Nat

public export
data DAG : List Task -> Type where
  Empty : DAG []
  AddTask : (t : Task) -> (deps : List Task) -> Not (t `Elem` tasks) -> deps `Subset` tasks -> DAG tasks -> DAG (t :: tasks)

public export total
deps : {ts : List Task} -> DAG ts -> (t : Task) -> t `Elem` ts -> List Task
deps (AddTask t ds _ _ _) t Here = ds
deps (AddTask _ _ _ _ subGraph) t (KeepLooking further) = deps subGraph t further
