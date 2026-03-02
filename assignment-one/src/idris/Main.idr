module Main

import Task
import Elem
import All
import Data.List

-- Compiler should complain if any of our functions are not provably total.
%default total

record Scheduler where
  constructor MkScheduler
  pending : List Task
  ready : List Task
  running : Maybe Task
  finished : List Task

data Step : Graph -> Scheduler -> Scheduler -> Type where
  Start :
    {depGraph : Graph} ->
    (current : Scheduler) ->
    (doThis : Task) ->
    (prfReady : doThis `Elem` current.ready) ->
    (prfIdle : current.running = Nothing) ->
    let next = MkScheduler
          current.pending
          (delete doThis current.ready)
          (Just doThis)
          current.finished
    in Step depGraph current next

  Complete :
    {depGraph : Graph} ->
    (current : Scheduler) ->
    (finishThis : Task) ->
    (prfRun : current.running = Just finishThis) ->
    let next = MkScheduler
          current.pending
          current.ready
          Nothing
          (finishThis :: current.finished)
    in Step depGraph current next

  Enqueue :
    {depGraph : Graph} ->
    (current : Scheduler) ->
    (queueThis : Task) ->
    (prfPending : Elem queueThis current.pending) ->
    (prfDeps : All (\d => Elem d current.finished) (deps depGraph queueThis)) ->
    let next = MkScheduler
          (delete queueThis current.pending)
          (queueThis :: current.ready)
          current.running
          current.finished
    in Step depGraph current next
          

