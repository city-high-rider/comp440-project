module State

import Task

%default total

public export
record State (deps : DAG ts) (running : Maybe Task) where
  constructor MkState
  statuses : List TaskStatus
  prf : WhatsRunning ts statuses running

finishedIsNotRunning : Not (Finished = Running)
finishedIsNotRunning Refl impossible

updateRunning : {ss : _} -> WhatsRunning ts ss (Just t) -> (ss' : List TaskStatus ** WhatsRunning ts ss' Nothing)
updateRunning {ss = (s :: rest)} (ConsIdle f x) = 
  let
    (newStatuses ** prf) = updateRunning x
  in
  (s :: newStatuses ** ConsIdle f prf)
updateRunning {ss = (Running :: rest)} (ConsRunning x) = (Finished :: rest ** ConsIdle finishedIsNotRunning x)

public export
complete : {task, tasks : _} -> State tasks (Just task) -> State tasks Nothing
complete (MkState statuses prf) = 
  let
    (ss' ** newPrf) = updateRunning prf
  in
  MkState ss' newPrf
