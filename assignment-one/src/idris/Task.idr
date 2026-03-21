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
deps : {ts : List Task} -> DAG ts -> (t : Task) -> t `Elem` ts -> (deps : List Task ** All (`Elem`ts) deps)
deps (AddTask t ds _ ssPrf _) t Here = (ds ** propImplies (\_ => KeepLooking) ssPrf)
deps (AddTask _ _ _ _ subGraph) t (KeepLooking y) =
  let
    (deps ** prf) = deps subGraph t y
  in
  (deps ** propImplies (\_ => KeepLooking) prf)
