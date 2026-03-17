module Trace

import All
import Data.List
import Elem
import Subset
import Task

%default total

public export
record Scheduler (dg : DAG ts) where
  constructor MkScheduler
  pending : List Task
  ready : List Task
  running : Maybe Task
  finished : List Task

Finished : {ts : _} -> {dg : DAG ts} -> Scheduler dg -> Type
Finished s = (s.pending = [], s.ready = [], s.running = Nothing, s.finished `SsEq` ts)  

public export
data Step : Scheduler dg -> Scheduler dg -> Type where
  Start :
    (current : Scheduler dg) ->
    (doThis : Task) ->
    (prfReady : doThis `Elem` current.ready) ->
    (prfIdle : current.running = Nothing) ->
    let next = MkScheduler
          current.pending
          (delete doThis current.ready)
          (Just doThis)
          current.finished
    in Step current next

  Complete :
    (current : Scheduler dg) ->
    (finishThis : Task) ->
    (prfRun : current.running = Just finishThis) ->
    let next = MkScheduler
          current.pending
          current.ready
          Nothing
          (finishThis :: current.finished)
    in Step current next

  Enqueue :
    {dg : DAG ts} ->
    (current : Scheduler dg) ->
    (readyThis : Task) ->
    (inGraph : readyThis `Elem` ts) ->
    (pending : readyThis `Elem` current.pending) ->
    (depsFinished : All (`Elem` current.finished) (deps dg readyThis inGraph)) -> 
    let next = MkScheduler
          (delete readyThis current.pending)
          (readyThis :: current.ready)
          current.running
          current.finished
    in Step current next

Terminal : {dg : _} -> Scheduler dg -> Type
Terminal state = {s : Scheduler dg} -> Not (Step state s)

public export
data Trace : Scheduler dg -> Scheduler dg -> Type where
  StartHere : (initialState : Scheduler dg) -> Trace initialState initialState
  WithStep : Step a b -> Trace b c -> Trace a c

total
elemInEmptyImpossible : Elem _ list -> list = [] -> Void
elemInEmptyImpossible Here Refl impossible
elemInEmptyImpossible (KeepLooking x) Refl impossible

total
nothingNotJust : Nothing = Just _ -> Void
nothingNotJust Refl impossible

total
finishedIsTerminal : (fs : Scheduler dg) -> Finished fs -> Terminal fs
finishedIsTerminal _ (_, readyEmpty, _, _) (Start _ _ elemReady _) = elemInEmptyImpossible elemReady readyEmpty
finishedIsTerminal _ (_, _, runningEmpty, _) (Complete _ _ runningFull) =
  let
    nothingIsSomething = trans (sym runningEmpty) runningFull
  in
  nothingNotJust nothingIsSomething
finishedIsTerminal fs (pendingEmpty, _, _, _) (Enqueue fs _ _ elemPending _) = elemInEmptyImpossible elemPending pendingEmpty

total
terminalMeansNoRunning : (ts : Scheduler dg) -> Terminal ts -> ts.running = Nothing
terminalMeansNoRunning (MkScheduler _ _ Nothing _) _ = Refl
terminalMeansNoRunning ts@(MkScheduler _ _ (Just x) _) stepToVoid =
  let
    stepComplete = Complete ts x Refl 
    void = stepToVoid stepComplete
  in
  absurd void

total
terminalMeansNotReady : (ts : Scheduler dg) -> Terminal ts -> ts.ready = []
terminalMeansNotReady (MkScheduler _ [] _ _) _ = Refl
terminalMeansNotReady ts@(MkScheduler _ (x :: xs) _ _) stepToVoid =
  let
    notRunning = terminalMeansNoRunning ts stepToVoid
    stepStart = Start ts x Here notRunning 
  in
  absurd (stepToVoid stepStart)

total
terminalMeansNoPending : {dg : DAG ds} -> (ts : Scheduler dg) -> Terminal ts -> ts.pending = []
terminalMeansNoPending (MkScheduler [] _ _ _) _ = Refl
terminalMeansNoPending ts@(MkScheduler (x :: xs) ready running finished) stepToVoid = 
  let
    stepEnqueue = Enqueue ts x ?a Here ?b
  in
  absurd (stepToVoid stepEnqueue)
