module Main

import Task
import Elem
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
    {deps : Graph} ->
    (current : Scheduler) ->
    (doThis : Task) ->
    (prfReady : doThis `Elem` current.ready) ->
    (prfIdle : current.running = Nothing) ->
    let next = MkScheduler
          current.pending
          (delete doThis current.ready)
          (Just doThis)
          current.finished
    in Step deps current next

  Complete :
    {deps : Graph} ->
    (current : Scheduler) ->
    (finishThis : Task) ->
    (prfRun : current.running = Just finishThis) ->
    let next = MkScheduler
          current.pending
          current.ready
          Nothing
          (finishThis :: current.finished)
    in Step deps current next

  Enqueue :
    {deps : Graph} ->
    (current : Scheduler) ->
    (queueThis : Task) ->
    (prfPending : Elem queueThis current.pending) ->
    let next = MkScheduler
          (delete queueThis current.pending)
          (queueThis :: current.ready)
          current.running
          current.finished
    in Step deps current next
          

