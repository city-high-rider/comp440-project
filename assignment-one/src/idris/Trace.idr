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
Finished s = (s.pending = [], s.ready = [], s.running = Nothing, ts `Subset` s.finished)  

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
    (pendingInDag : readyThis `Elem` ts) ->
    (ds : List Task) ->
    (depsAreDeps : ds = (deps dg readyThis pendingInDag)) ->
    (depsAreFinished : ds `Subset` current.finished) ->
    Step current (MkScheduler
      (remove current.pending pending)
      (readyThis :: current.ready)
      current.running
      current.finished
      (coverMaintainOnEnqueue current pending)
      (removeFromSubsetStillSubset {prf = pending} current.pendingAreDeps))

total
measure : (s : Scheduler dg) -> Nat
measure (MkScheduler pending ready running _ _ _) = length (maybeToList running) + 2*(length ready) + 3*(length pending)

total
stepDecreasesMeasure : {a, b : Scheduler dg} -> a `Step` b -> measure a = S (measure b)

public export
data Trace : Scheduler dg -> Scheduler dg -> Type where
  StartHere : (initialState : Scheduler dg) -> Trace initialState initialState
  WithStep : Step a b -> Trace b c -> Trace a c

total
pendingOrFinishedHelper : (s : Scheduler dg) -> s .ready = [] -> s .running = Nothing -> (e : Task) -> One (\subset => Elem e subset) [s .pending, s .ready, maybeToList (s .running), s .finished] -> Either (Elem e (s.finished)) (Elem e (s.pending))
pendingOrFinishedHelper _ _ _ _ (ThisOne s.pending inPending) = Right inPending
pendingOrFinishedHelper s notReady _ e (Further (ThisOne s.ready inReady)) =
  absurd (elemInEmptyImpossible inReady notReady)
pendingOrFinishedHelper s _ notRunning e (Further (Further (ThisOne (maybeToList s.running) inRunning))) =
  let
    inEmpty : e `Elem` [] = replace notRunning {p = Elem e . maybeToList} inRunning
  in
  absurd (elemInEmptyImpossible inEmpty Refl)
pendingOrFinishedHelper s _ _ _ (Further (Further (Further (ThisOne s.finished inFinished)))) = Left inFinished


total
pendingOrFinished : {ts : List Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> (idle : s.running = Nothing) -> (notReady : s.ready = []) -> All (\task => Either (task`Elem`s.finished) (task`Elem`s.pending)) ts
pendingOrFinished s idle notReady = propImplies (\e => pendingOrFinishedHelper s notReady idle e) s.cover

total
symNotEq : Not (a = b) -> Not (b = a)
symNotEq aebContra bea = aebContra (sym bea)

total
findEnabled : (currentTasks : List Task) -> (currentDag : DAG currentTasks) -> (s : Scheduler initialDag) -> (somePending : Task ** (somePending `Elem` s.pending, somePending `Elem` currentTasks)) -> All (\t => Either (t`Elem`s.finished) (t`Elem`s.pending)) currentTasks -> (enabledTask : Task ** (depsOfEnabled : List Task ** (enabledIsPending : enabledTask `Elem` s.pending ** (enabledInCurrentDag : enabledTask `Elem` currentTasks ** (All (\t => t`Elem`s.finished) depsOfEnabled, depsOfEnabled = deps currentDag enabledTask enabledInCurrentDag)))))
findEnabled [] Empty _ (_ ** (_, hasPendingInDag)) _ = absurd (elemInEmptyImpossible hasPendingInDag Refl)
findEnabled (t :: restTasks) (AddTask t tDeps tNotInRest depsSSRest restDag) s (somePending ** (itsPending, itsInTheDag)) (porfT :: porfRest) =
  case porfT of
       (Left itsFinished) =>
        let
          pendingAndFinishedDisjoint : Not (thing ** (thing`Elem`s.pending,thing`Elem`s.finished)) = ?todo_implement_me
          somethingPendingInRestTasks : somePending `Elem` restTasks =
            case decEq somePending t of
                 Yes Refl => absurd (pendingAndFinishedDisjoint (somePending ** (itsPending, itsFinished)))
                 No notEq => notInHeadInTail notEq itsInTheDag
          (en ** enDeps ** enPending ** enInRestDag ** (enDepsFinished, enDepsGood)) = findEnabled restTasks restDag s (somePending ** (itsPending, somethingPendingInRestTasks)) porfRest
        in
        (en ** enDeps ** enPending ** KeepLooking enInRestDag ** (enDepsFinished, enDepsGood))
       (Right itsPending) =>
        let
          porfDeps : All (\tDep => Either (tDep`Elem`s.finished) (tDep`Elem`s.pending)) tDeps =
            propImplies (\tDep, inRest => extractPrf inRest porfRest) depsSSRest
        in
        case allAOrBMeansAllAOrOneB porfDeps of
             (Left allDepsFinished) =>
              (t ** tDeps ** itsPending ** Here ** (allDepsFinished, Refl))
             (Right (pendingDep ** (inRest, inTdeps))) =>
              let
                (en ** enDeps ** enPending ** enInNextDag ** (enDepsFinished, enDepsGood)) = findEnabled restTasks restDag s (pendingDep ** (inRest, extractPrf inTdeps depsSSRest)) porfRest
              in
              (en ** enDeps ** enPending ** KeepLooking enInNextDag ** (enDepsFinished, enDepsGood))

total
onlyFinishedElemAllFinished : {ts : List Task} -> (e : Task) -> One (e`Elem`) [[], [], [], finish] -> e `Elem` finish
onlyFinishedElemAllFinished e (ThisOne [] prf) = absurd (elemInEmptyImpossible prf Refl)
onlyFinishedElemAllFinished e (Further (ThisOne [] prf)) = absurd (elemInEmptyImpossible prf Refl)
onlyFinishedElemAllFinished e (Further (Further (ThisOne [] prf))) = absurd (elemInEmptyImpossible prf Refl)
onlyFinishedElemAllFinished e (Further (Further (Further (ThisOne finish prf)))) = prf

total
findStep : {ts : List Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> Either (Finished s) (next ** s `Step` next)
findStep s@(MkScheduler pending ready (Just x) finished cover pendingAreDeps) =
  Right ((MkScheduler pending ready Nothing (x :: finished) (coverMaintainOnComplete s Refl) pendingAreDeps) ** Complete s x Refl)
findStep s@(MkScheduler pending (x :: xs) Nothing finished cover pendingAreDeps) =
  Right ((MkScheduler pending xs (Just x) finished (coverMaintainOnStart s Refl Refl) pendingAreDeps) ** Start s Refl Refl)
findStep (MkScheduler (x :: xs) [] Nothing finished cover pendingAreDeps) =
  let
    porf = pendingOrFinished {dg = dg} (MkScheduler (x::xs) [] Nothing finished cover pendingAreDeps) Refl Refl
    (en ** enDeps ** enIsPending ** enInDag ** (enDepsFinished, enDepsAreDeps)) = findEnabled {initialDag = dg} ts dg (MkScheduler (x :: xs) [] Nothing finished cover pendingAreDeps) (x ** (Here, extractPrf Here pendingAreDeps)) porf
  in
  Right ((MkScheduler (remove (x::xs) enIsPending) (en :: []) Nothing finished (coverMaintainOnEnqueue (MkScheduler (x::xs) [] Nothing finished cover pendingAreDeps) enIsPending) (removeFromSubsetStillSubset {prf = enIsPending} pendingAreDeps)) ** Enqueue (MkScheduler (x::xs) [] Nothing finished cover pendingAreDeps) en enIsPending enInDag enDeps enDepsAreDeps enDepsFinished)
findStep (MkScheduler [] [] Nothing finished cover pendingAreDeps) =
  Left (Refl, Refl, Refl, propImplies (onlyFinishedElemAllFinished {ts = ts}) cover)

partial
findTrace : {ts : List Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> (finish : Scheduler dg ** (Finished finish, Trace s finish))
findTrace s =
  case findStep s of
       Left finishPrf => (s ** (finishPrf, StartHere s))
       Right (next ** step) =>
          let
            (finishedState ** (finishPrf, restOfTrace)) = findTrace next
          in
          (finishedState ** (finishPrf, WithStep step restOfTrace))

