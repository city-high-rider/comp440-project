module Trace

import All
import Data.List
import Elem
import Subset
import Task

%default total

public export total
maybeToList : Maybe a -> List a
maybeToList Nothing = []
maybeToList (Just x) = [x]

public export
record Scheduler (dg : DAG ts) where
  constructor MkScheduler
  pending : List Task
  ready : List Task
  running : Maybe Task
  finished : List Task
  cover : [pending, ready, maybeToList running, finished] `Cover` ts

total
Finished : {ts : _} -> {dg : DAG ts} -> Scheduler dg -> Type
Finished s = (s.pending = [], s.ready = [], s.running = Nothing, s.finished `SsEq` ts)  

{-
public export
data One : (pred : a -> Type) -> List a -> Type where
  ThisOne : (x : a) -> pred x -> One pred (x::rest)
  Further : One pred xs -> One pred (x::xs)
-}

total
elemSingletonEq : a `Elem` [b] -> a = b
elemSingletonEq Here = Refl
elemSingletonEq (KeepLooking _) impossible

total
completeCoverHelper : (fThis : Task) -> (s : Scheduler dg) -> (notIdle : s.running = Just fThis) -> (e : Task) -> One (\subset => Elem e subset) [s .pending, s .ready, maybeToList (s .running), s .finished] -> One (\subset => Elem e subset) [s .pending, s .ready, [], (fThis :: s .finished)]
completeCoverHelper _ _ _ _ (ThisOne s.pending prf) = ThisOne s.pending prf
completeCoverHelper _ _ _ _ (Further (ThisOne s.ready prf)) = Further (ThisOne s.ready prf)
completeCoverHelper fThis s notIdle e (Further (Further (ThisOne (maybeToList s.running) prf))) =
  let
    prf' = replace notIdle {p = Elem e . maybeToList} prf
    eIsFThis = elemSingletonEq prf'
  in
  rewrite (sym eIsFThis) in Further (Further (Further (ThisOne (e :: s.finished) Here)))
completeCoverHelper fThis s _ _ (Further (Further (Further (ThisOne s.finished prf)))) = Further (Further (Further (ThisOne (fThis :: s.finished) (KeepLooking prf))))

total
coverMaintainOnComplete : {ts : List Task} -> {dg : DAG ts} -> {fThis : Task} -> (s : Scheduler dg) -> (notIdlePrf : s.running = Just fThis) -> [s.pending, s.ready, [], fThis :: s.finished] `Cover` ts 
coverMaintainOnComplete s prf = propImplies (\e => completeCoverHelper fThis s prf e) s.cover

public export
data Step : Scheduler dg -> Scheduler dg -> Type where
  Complete :
  (current : Scheduler dg) ->
  (finishThis : Task) ->
  (prfRun : current.running = Just finishThis) ->
  Step current (MkScheduler
    current.pending
    current.ready
    Nothing
    (finishThis :: current.finished)
    (coverMaintainOnComplete current prfRun))

{-

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
-}
