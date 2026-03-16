module Task

import All
import Elem
import Subset

%default total

export
Task : Type
Task = Nat

public export
data TaskStatus
  = Pending
  | Ready
  | Running
  | Finished

public export
data DAG : List Task -> Type where
  Empty : DAG []
  AddTask : (t : Task) -> (deps : List Task) -> deps `Subset` tasks -> DAG tasks -> DAG (t :: tasks)

public export
data WhatsRunning : List Task -> List TaskStatus -> Maybe Task -> Type where
  Base : WhatsRunning [] [] Nothing
  ConsIdle : Not (s = Running) -> WhatsRunning ts ss x -> WhatsRunning (t::ts) (s::ss) x 
  ConsRunning : WhatsRunning ts ss Nothing -> WhatsRunning (t::ts) (Running::ss) (Just t)
 

