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

{-

total
depInDag : (pending = first :: rest) -> pending `Subset` ts -> first `Elem` ts
depInDag prf ss =
  let
    ss' = replace prf {p = All (\arg => Elem arg ts)} ss
  in
  extractPrf Here ss'

total
removePendingStillSubset : (pending = first :: rest) -> pending `Subset` ts -> rest `Subset` ts
removePendingStillSubset Refl x = smallerSubsetIsSubset x

total
enqueueCoverHelper : {readyThis : Task} -> {rest : List Task} -> (s : Scheduler dg) -> s .pending = readyThis :: rest -> (e : Task) -> One (\subset => Elem e subset) [s .pending, s .ready, maybeToList (s .running), s .finished] -> One (\subset => Elem e subset) [rest, (readyThis :: s .ready), maybeToList (s .running), s .finished]
enqueueCoverHelper s prf e (ThisOne s.pending prf') =
  case e `decEq` readyThis of
       (Yes Refl) => Further (ThisOne (e :: s .ready) Here)
       (No contra) =>
          let
            prf'' = replace prf {p = Elem e} prf'
          in
          ThisOne rest (notInHeadInTail contra prf'')
enqueueCoverHelper s _ _ (Further (ThisOne s.ready inReady)) = Further (ThisOne (readyThis :: s.ready) (KeepLooking inReady))
enqueueCoverHelper s _ _ (Further (Further (ThisOne (maybeToList s.running) inRunning))) = Further (Further (ThisOne (maybeToList s.running) inRunning))
enqueueCoverHelper s _ _ (Further (Further (Further (ThisOne s.finished inFinished)))) = Further (Further (Further (ThisOne s.finished inFinished)))

total
coverMaintainOnEnqueue : {ts, rest : List Task} -> {readyThis : Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> (pendingPrf : s.pending = readyThis :: rest) -> [rest, (readyThis :: s.ready), (maybeToList s.running), s.finished] `Cover` ts
coverMaintainOnEnqueue s pendingPrf = propImplies (\e => enqueueCoverHelper s pendingPrf e) s.cover

-}

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
    (depsFinished : All (`Elem` current.finished) (deps' dg readyThis (extractPrf pending current.pendingAreDeps))) -> 
    Step current (MkScheduler
      (remove current.pending pending)
      (readyThis :: current.ready)
      current.running
      current.finished
      ?cover
      ?subset)

{-

Terminal : {dg : _} -> Scheduler dg -> Type
Terminal state = {s : Scheduler dg} -> Not (Step state s)

public export
data Trace : Scheduler dg -> Scheduler dg -> Type where
  StartHere : (initialState : Scheduler dg) -> Trace initialState initialState
  WithStep : Step a b -> Trace b c -> Trace a c

total
finishedIsTerminal : {ts : List Task} -> {dg : DAG ts} -> (fs : Scheduler dg) -> Finished fs -> Terminal fs
finishedIsTerminal fs (_, _, noRunning, _) (Complete fs _ isRunning) =
  let
    nothingIsSomething = trans (sym noRunning) isRunning
  in
  uninhabited nothingIsSomething
finishedIsTerminal fs (_, noReady, _, _) (Start fs ready _) =
  let
    emptyEqNonempty = trans (sym noReady) ready
  in
  uninhabited emptyEqNonempty
finishedIsTerminal fs (noPending, _, _, _) (Enqueue fs hasPending _) =
  let
    emptyEqNonempty = trans (sym noPending) hasPending
  in
  uninhabited emptyEqNonempty

total
terminalMeansNoRunning : {ts : List Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> Terminal s -> s.running = Nothing
terminalMeansNoRunning (MkScheduler _ _ Nothing _ _ _) _ = Refl
terminalMeansNoRunning ts@(MkScheduler _ _ (Just x) _ _ _) stepToVoid =
  let
    stepComplete = Complete ts x Refl 
    void = stepToVoid stepComplete
  in
  absurd void

total
terminalMeansNotReady : {ts : List Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> Terminal s -> s.ready = []
terminalMeansNotReady (MkScheduler _ [] _ _ _ _) stepToVoid = Refl
terminalMeansNotReady s@(MkScheduler pending (oneReady :: rest) running finished _ _) stepToVoid =
  let
    noRunning = terminalMeansNoRunning s stepToVoid
    oneReady : (s.ready = oneReady :: rest) = Refl
    step = Start s oneReady noRunning
  in
  absurd (stepToVoid step)

total
terminalMeansNoPending : {ds : List Task} -> {dg : DAG ds} -> (ts : Scheduler dg) -> Terminal ts -> ts.pending = []
terminalMeansNoPending (MkScheduler [] _ _ _ _ _) _ = Refl
terminalMeansNoPending ts@(MkScheduler (onePending :: rest) ready running finished cover pendingInDag) stepToVoid =
  let
    noRunning = terminalMeansNoRunning ts stepToVoid
    notReady = terminalMeansNotReady ts stepToVoid
    hasPending : (ts.pending = (onePending :: rest)) = Refl
    step = Enqueue ts hasPending ?depsFinished
  in
  absurd (stepToVoid step)

total
terminalMeansAllFinished : {ds : List Task} -> {dg : DAG ds} -> (ts : Scheduler dg) -> Terminal ts -> ts.finished `SsEq` ds
terminalMeansAllFinished ts stepToVoid =
  let
    noRunning = terminalMeansNoRunning ts stepToVoid
    notReady = terminalMeansNotReady ts stepToVoid
    noPending = terminalMeansNoPending ts stepToVoid
  in
  ?terminalMeansAllFinished_rhs

-}
