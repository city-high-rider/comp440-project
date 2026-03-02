module PrfStatusPartitions

import Task
import Trace
import Elem
import Data.List

%default total

{-
Want to prove that:
The total number of tasks in the scheduler does not change; i.e. it is consistent throughout 
the whole trace.
-}

involvedTasks : Scheduler -> List Task
involvedTasks (MkScheduler pending ready running finished) =
  case running of
       Nothing => ready ++ pending ++ finished
       Just r => r :: ready ++ pending ++ finished

tasksConstant : Trace deps start end -> (involvedTasks start) = (involvedTasks end)
tasksConstant (StartHere end) = Refl
tasksConstant (WithStep (Start start doThis prfReady prfIdle) y) = ?tasksConstant_rhs_2
tasksConstant (WithStep (Complete start finishThis prfRun) y) = ?tasksConstant_rhs_3
tasksConstant (WithStep (Enqueue start queueThis prfPending prfDeps) y) = ?tasksConstant_rhs_4


