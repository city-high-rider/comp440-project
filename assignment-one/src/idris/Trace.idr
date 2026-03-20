module Trace

import All
import Data.List
import Elem
import Decidable.Equality
import Remove
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
  pendingAreDeps : pending `Subset` ts

total
Finished : {ts : _} -> {dg : DAG ts} -> Scheduler dg -> Type
Finished s = (s.pending = [], s.ready = [], s.running = Nothing, s.finished `SsEq` ts)  

total
EnabledIn : {ts : List Task} -> {dg : DAG ts} -> Task -> Scheduler dg -> Type
EnabledIn task s = (inPending : task `Elem` s.pending ** case deps dg task (extractPrf inPending s.pendingAreDeps) of
  (ds ** _) => All (`Elem`s.finished) ds
  )

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

total
notInHeadInTail : (notHead : Not (elem = first)) -> (inList : elem `Elem` (first::rest)) -> elem `Elem` rest
notInHeadInTail notHead Here = absurd (notHead Refl)
notInHeadInTail _ (KeepLooking x) = x

total
startCoverHelper : {runThis : Task} -> {rest : List Task} -> (s : Scheduler dg) -> s .ready = runThis :: rest -> s .running = Nothing -> (e : Task) -> One (\subset => Elem e subset) [s .pending, s .ready, maybeToList (s .running), s .finished] -> One (\subset => Elem e subset) [s .pending, rest, [runThis], s .finished]
startCoverHelper s _ _ _ (ThisOne s.pending prf) = (ThisOne s.pending prf)
startCoverHelper s prfReady _ e (Further (ThisOne s.ready prf)) =
  case e `decEq` runThis of
       (Yes Refl) => Further (Further (ThisOne [e] Here))
       (No contra) =>
        let
          prf' = replace prfReady {p = Elem e} prf
        in
        Further (ThisOne rest (notInHeadInTail contra prf'))
startCoverHelper _ _ prfIdle e (Further (Further (ThisOne (maybeToList s.running) prf))) =
  let
    elemOfEmpty = replace prfIdle {p = Elem e . maybeToList} prf
  in
  absurd (elemInEmptyImpossible elemOfEmpty Refl)
startCoverHelper s prfReady prfIdle e (Further (Further (Further (ThisOne s.finished prf)))) = Further (Further (Further (ThisOne s.finished prf)))

total
coverMaintainOnStart : {ts, rest : List Task} -> {runThis : Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> (idlePrf : s.running = Nothing) -> (readyPrf : s.ready = runThis::rest) -> [s.pending, rest, maybeToList (Just runThis), s.finished] `Cover` ts
coverMaintainOnStart s idlePrf readyPrf = propImplies (\e => startCoverHelper s readyPrf idlePrf e) s.cover

total
enqueueCoverHelper : {readyThis : Task} -> (s : Scheduler dg) -> (pending : Elem readyThis (s.pending)) -> (e : Task) -> One (\subset => Elem e subset) [s .pending, s .ready, maybeToList (s .running), s .finished] -> One (\subset => Elem e subset) [remove (s .pending) pending, (readyThis :: s .ready), maybeToList (s .running), s .finished]
enqueueCoverHelper s pending e (ThisOne s.pending prf) =
  case e `decEq` readyThis of
       (Yes Refl) => Further (ThisOne (e :: s.ready) Here)
       (No contra) => ThisOne (remove s.pending pending) (notRemovedStillThere prf pending contra)
enqueueCoverHelper s _ _ (Further (ThisOne s.ready prf)) = Further (ThisOne (readyThis :: s.ready) (KeepLooking prf))
enqueueCoverHelper s _ _ (Further (Further (ThisOne (maybeToList s.running) prf))) = Further (Further (ThisOne (maybeToList s.running) prf))
enqueueCoverHelper s _ _ (Further (Further (Further (ThisOne s.finished prf)))) = Further (Further (Further (ThisOne s.finished prf)))

total
coverMaintainOnEnqueue : {ts : List Task} -> {readyThis : Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> (pending : readyThis `Elem` s.pending) -> [(remove s.pending pending), (readyThis :: s.ready), (maybeToList s.running), s.finished] `Cover` ts
coverMaintainOnEnqueue s pending = propImplies (\e => enqueueCoverHelper s pending e) s.cover

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
    (coverMaintainOnComplete current prfRun)
    current.pendingAreDeps)

  Start :
    (current : Scheduler dg) ->
    (prfReady : current.ready = first :: rest) ->
    (prfIdle : current.running = Nothing) ->
    Step current (MkScheduler
      current.pending
      (rest)
      (Just first)
      current.finished
      (coverMaintainOnStart current prfIdle prfReady)
      current.pendingAreDeps)

  Enqueue :
    {dg : DAG ts} ->
    (current : Scheduler dg) ->
    (readyThis : Task) ->
    (pending : readyThis `Elem` current.pending) ->
    (depsFinished : case deps dg readyThis (extractPrf pending current.pendingAreDeps) of
                         (ds ** _) => All (`Elem`current.finished) ds) -> 
    Step current (MkScheduler
      (remove current.pending pending)
      (readyThis :: current.ready)
      current.running
      current.finished
      (coverMaintainOnEnqueue current pending)
      (removeFromSubsetStillSubset {prf = pending} current.pendingAreDeps))

public export
data Trace : Scheduler dg -> Scheduler dg -> Type where
  StartHere : (initialState : Scheduler dg) -> Trace initialState initialState
  WithStep : Step a b -> Trace b c -> Trace a c

total
pendingOrFinishedHelper : (s : Scheduler dg) -> s .ready = [] -> s .running = Nothing -> (e : Task) -> One (\subset => Elem e subset) [s .pending, s .ready, maybeToList (s .running), s .finished] -> Either (Elem e (s .pending)) (Elem e (s .finished))
pendingOrFinishedHelper _ _ _ _ (ThisOne s.pending inPending) = Left inPending
pendingOrFinishedHelper s notReady _ e (Further (ThisOne s.ready inReady)) =
  absurd (elemInEmptyImpossible inReady notReady)
pendingOrFinishedHelper s _ notRunning e (Further (Further (ThisOne (maybeToList s.running) inRunning))) =
  let
    inEmpty : e `Elem` [] = replace notRunning {p = Elem e . maybeToList} inRunning
  in
  absurd (elemInEmptyImpossible inEmpty Refl)
pendingOrFinishedHelper s _ _ _ (Further (Further (Further (ThisOne s.finished inFinished)))) = Right inFinished


total
pendingOrFinished : {ts : List Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> (idle : s.running = Nothing) -> (notReady : s.ready = []) -> All (\task => Either (task`Elem`s.pending) (task`Elem`s.finished)) ts
pendingOrFinished s idle notReady = propImplies (\e => pendingOrFinishedHelper s notReady idle e) s.cover

total
onlyFinishedElemAllFinished : {ts : List Task} -> (e : Task) -> One (e`Elem`) [[], [], [], finish] -> e `Elem` finish
onlyFinishedElemAllFinished e (ThisOne [] prf) = absurd (elemInEmptyImpossible prf Refl)
onlyFinishedElemAllFinished e (Further (ThisOne [] prf)) = absurd (elemInEmptyImpossible prf Refl)
onlyFinishedElemAllFinished e (Further (Further (ThisOne [] prf))) = absurd (elemInEmptyImpossible prf Refl)
onlyFinishedElemAllFinished e (Further (Further (Further (ThisOne finish prf)))) = prf

partial
traceToFinished : {ts : List Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> (fs : Scheduler dg ** (Finished fs, Trace s fs))
traceToFinished (MkScheduler pending ready (Just x) finished cover pendingAreDeps) =
  let
    stepComplete = Complete (MkScheduler pending ready (Just x) finished cover pendingAreDeps) x Refl
    (fs ** (finishedPrf, restTrace)) = traceToFinished (MkScheduler pending ready Nothing (x::finished) (coverMaintainOnComplete (MkScheduler pending ready (Just x) finished cover pendingAreDeps) Refl) pendingAreDeps) 
  in
  (fs ** (finishedPrf, WithStep stepComplete restTrace))
traceToFinished (MkScheduler pending (x :: xs) Nothing finished cover pendingAreDeps) =
  let
    stepStart = Start (MkScheduler pending (x::xs) Nothing finished cover pendingAreDeps) Refl Refl 
    (fs ** (finishedPrf, restTrace)) = traceToFinished (MkScheduler pending xs (Just x) finished (coverMaintainOnStart (MkScheduler pending (x::xs) Nothing finished cover pendingAreDeps) Refl Refl) pendingAreDeps)
  in
  (fs ** (finishedPrf, WithStep stepStart restTrace))
traceToFinished (MkScheduler (x :: xs) [] Nothing finished cover pendingAreDeps) = ?traceToFinished_rhs_4
traceToFinished (MkScheduler [] [] Nothing finished cover pendingAreDeps) =
  let
    noPending : ((MkScheduler [] [] Nothing finished cover pendingAreDeps).pending = []) = Refl
    noReady : ((MkScheduler [] [] Nothing finished cover pendingAreDeps).ready = []) = Refl
    noRunning : ((MkScheduler [] [] Nothing finished cover pendingAreDeps).running = Nothing) = Refl
    finishedPrf : Finished (MkScheduler [] [] Nothing finished cover pendingAreDeps) =
      (noPending, noReady, noRunning, ?a, propImplies onlyFinishedElemAllFinished cover)
  in
  (MkScheduler [] [] Nothing finished cover pendingAreDeps ** (finishedPrf, StartHere (MkScheduler [] [] Nothing finished cover pendingAreDeps))) 
