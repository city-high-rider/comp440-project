module PrfStatusPartitions

import Task
import Trace
import Elem
import Data.List

%default total

{-
Want to prove that:
The tasks involved with the scheduler do not change, i.e.
for any trace, for any two states mentioned in the trace, the set of involved tasks in both states are equivalent.
(Where the set of involved tasks is the union between running tasks, ready tasks, pending tasks, and finished tasks.)
-}

involvedTasks : Scheduler -> List Task
involvedTasks (MkScheduler pending ready running finished) =
  case running of
       Nothing => ready ++ pending ++ finished
       Just r => r :: ready ++ pending ++ finished

tasksConstant : Trace deps start end -> (involvedTasks start) `SsEq` (involvedTasks end)
tasksConstant (StartHere end) = ssEqRefl
tasksConstant (WithStep (Start start doThis prfReady prfIdle) y) =
  let
    ind = tasksConstant y
  in
  ssEqTrans ?hole ind
tasksConstant (WithStep (Complete start finishThis prfRun) y) = ?tasksConstant_rhs_3
tasksConstant (WithStep (Enqueue start queueThis prfPending prfDeps) y) = ?tasksConstant_rhs_4


