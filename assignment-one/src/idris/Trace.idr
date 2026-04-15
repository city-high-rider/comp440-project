module Trace

import All
import Control.WellFounded
import Data.List
import Data.Nat
import Elem
import Decidable.Equality
import Remove
import Subset
import Task
import Unique

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
  pdjr : Disjoint pending ready
  pdje : Disjoint pending (maybeToList running)
  pdjf : Disjoint pending finished
  pUnique : Unique pending


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

total
pdjfOnComplete : {finishThis : Task} -> (s : Scheduler dg) -> s.running = Just finishThis -> Disjoint s.pending (finishThis :: s.finished) 
pdjfOnComplete (MkScheduler pending _ (Just finishThis) finished _ _ _ pdje pdjf _) Refl =
  let
    nothingPendingIsFinishThis : All (\thing => Not (thing = finishThis)) pending
      = propImplies (\_ => notElemSingletonNotEq) pdje
    finishThisNotPending : Not (finishThis `Elem` pending)
      = nothingEqNotElem nothingPendingIsFinishThis
  in
  growDj pdjf finishThisNotPending

total
pdjrOnStart : {something : Task} -> (s : Scheduler dg) -> s.ready = something::rest -> Disjoint s.pending rest
pdjrOnStart (MkScheduler pending (something :: rest) _ _ _ _ pdjr _ _ _) Refl = shrinkDj pdjr

total
pdjeOnStart : {startThis : Task} -> {0 rest : List Task} -> (s : Scheduler dg) -> s.ready = startThis::rest -> Disjoint s.pending [startThis]
pdjeOnStart (MkScheduler pending (startThis :: rest) running _ _ _ pdjr _ _ _) Refl =
  propImplies (\_ => notInListNotFirst) pdjr

-- For some reason, even though pUnique is contained in the scheduler record,
-- we have to pass it separately for the unifier to be happy...
-- otherwise it treats it as a (rec : Scheduler ?dg) -> Unique rec.pending
-- even though the LSP reports it as a Unique pending.
total
pdjrOnEnqueue : {readyThis : Task} -> (s : Scheduler dg) -> (prf : readyThis `Elem` s.pending) -> Unique s.pending -> Disjoint (remove s.pending prf) (readyThis::s.ready)
pdjrOnEnqueue (MkScheduler pending ready _ _ _ _ pdjr _ _ _) prf pUnique =
  let
    shrinkPendingDjReady : Disjoint (remove pending prf) ready
      = shrinkDjArb {prf = prf} pdjr
    removedSoNotInPending : Not (readyThis `Elem` (remove pending prf))
      = removeUniqueNotThere {prf = prf} pUnique
  in
  growDj shrinkPendingDjReady removedSoNotInPending

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
    current.pendingAreDeps
    current.pdjr
    (forAllForSome (\_, inEmpty => elemInEmptyImpossible inEmpty Refl))
    (pdjfOnComplete current prfRun)
    current.pUnique)

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
      current.pendingAreDeps
      (pdjrOnStart {something = first} current prfReady)
      (pdjeOnStart {startThis = first} current prfReady)
      current.pdjf
      current.pUnique)

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
      (removeFromSubsetStillSubset {prf = pending} current.pendingAreDeps)
      (pdjrOnEnqueue current pending current.pUnique)
      (shrinkDjArb {prf = pending} current.pdje)
      (shrinkDjArb {prf = pending} current.pdjf)
      (removeUniqueStillUnique {prf = pending} current.pUnique))


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
          pendingAndFinishedDisjoint : Not (thing ** (thing`Elem`s.pending,thing`Elem`s.finished)) = disjointNotInBoth s.pdjf
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
findStep s@(MkScheduler pending ready (Just x) finished cover pendingAreDeps pdjr pdje pdjf pUnique) =
  Right ((MkScheduler pending ready Nothing (x :: finished) (coverMaintainOnComplete s Refl) pendingAreDeps pdjr (forAllForSome (\_, inEmpty => elemInEmptyImpossible inEmpty Refl)) (pdjfOnComplete s Refl) pUnique) ** Complete s x Refl)
findStep s@(MkScheduler pending (x :: xs) Nothing finished cover pendingAreDeps pdjr pdje pdjf pUnique) =
  Right ((MkScheduler pending xs (Just x) finished (coverMaintainOnStart s Refl Refl) pendingAreDeps (pdjrOnStart {something = x} s Refl) (pdjeOnStart {startThis = x} s Refl) pdjf pUnique) ** Start s Refl Refl)
findStep s@(MkScheduler (x :: xs) [] Nothing finished cover pendingAreDeps pdjr pdje pdjf pUnique) =
  let
    porf = pendingOrFinished {dg = dg} s Refl Refl
    (en ** enDeps ** enIsPending ** enInDag ** (enDepsFinished, enDepsAreDeps)) = findEnabled {initialDag = dg} ts dg s (x ** (Here, extractPrf Here pendingAreDeps)) porf
  in
  Right ((MkScheduler (remove (x::xs) enIsPending) (en :: []) Nothing finished (coverMaintainOnEnqueue (MkScheduler (x::xs) [] Nothing finished cover pendingAreDeps pdjr pdje pdjf pUnique) enIsPending) (removeFromSubsetStillSubset {prf = enIsPending} pendingAreDeps) (pdjrOnEnqueue {dg=dg} (MkScheduler (x :: xs) [] Nothing finished cover pendingAreDeps pdjr pdje pdjf pUnique) enIsPending pUnique) (shrinkDjArb pdje) (shrinkDjArb pdjf) (removeUniqueStillUnique pUnique)) ** Enqueue (MkScheduler (x::xs) [] Nothing finished cover pendingAreDeps pdjr pdje pdjf pUnique) en enIsPending enInDag enDeps enDepsAreDeps enDepsFinished)
findStep (MkScheduler [] [] Nothing finished cover pendingAreDeps _ _ _ _) =
  Left (Refl, Refl, Refl, propImplies (onlyFinishedElemAllFinished {ts = ts}) cover)

total
measure : (s : Scheduler dg) -> Nat
measure (MkScheduler pending ready running _ _ _ _ _ _ _) = length (maybeToList running) + 2*(length ready) + 3*(length pending)

total
justToListLenOne : m = Just x -> length (maybeToList m) = 1
justToListLenOne Refl = Refl

total
nothingToListLenZero : m = Nothing -> length (maybeToList m) = 0
nothingToListLenZero Refl = Refl

total
lengthNe : {0 someList, aTail : List a} -> someList = aHead::aTail -> length someList = S (length aTail)
lengthNe Refl = Refl

total
weirdLem : {0 aHead : a} -> {someList : List a} -> someList = aHead::aTail -> (theTail ** theTail = aTail)
weirdLem {someList = (_ :: aTail)} Refl = (aTail ** Refl)

total
stepDecreasesMeasure : {ts : List Task} -> {dg : DAG ts} -> {a, b : Scheduler dg} -> a `Step` b -> measure a = S (measure b)
stepDecreasesMeasure (Complete (MkScheduler pending ready running finished _ _ _ _ _ _) finishThis prfRun) =
  rewrite justToListLenOne prfRun in Refl
stepDecreasesMeasure (Start (MkScheduler pending ready running finished _ _ _ _ _ _) prfReady prfIdle) =
  rewrite nothingToListLenZero prfIdle in
  rewrite lengthNe prfReady in
  let
    -- we need this because the totality checker freaks out if we expand ready.
    -- also adding any let or case block introduces a dependency on ts for some reason.
    (tl ** prfTl) = weirdLem prfReady
  in
  rewrite sym prfTl in
  rewrite sym (plusSuccRightSucc (length tl) (plus (length tl) 0)) in
  Refl
stepDecreasesMeasure (Enqueue (MkScheduler pending ready running finished _ _ _ _ _ _) readyThis pendingPrf _ _ _ _) =
  rewrite sym (removeShrinkLen {xs = pending, prf = pendingPrf}) in
  rewrite sym (plusSuccRightSucc (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0)) in
  rewrite sym (plusSuccRightSucc (length (remove pending pendingPrf)) (S (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0)))) in
  rewrite sym (plusSuccRightSucc (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0))) in
  rewrite sym (plusSuccRightSucc (plus (length (maybeToList running)) (plus (length ready) (plus (length ready) 0))) (S (S ((plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0))))))) in
  rewrite sym (plusSuccRightSucc (plus (length (maybeToList running)) (plus (length ready) (plus (length ready) 0))) (S ((plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0)))))) in
  rewrite sym (plusSuccRightSucc (plus (length (maybeToList running)) (plus (length ready) (plus (length ready) 0))) ((plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) (plus (length (remove pending pendingPrf)) 0))))) in
  rewrite sym (plusSuccRightSucc (length ready) (plus (length ready) 0)) in
  rewrite sym (plusSuccRightSucc (length (maybeToList running)) (S (plus (length ready) (plus (length ready) 0)))) in
  rewrite sym (plusSuccRightSucc (length (maybeToList running)) (plus (length ready) (plus (length ready) 0))) in
  Refl

Sized (Scheduler dg) where
  size = measure

total
findTraceHelper : {ts : List Task} -> {dg : DAG ts} -> (cur : Scheduler dg) -> (rec : (next : Scheduler dg) -> Smaller next cur -> (finish : Scheduler dg ** (Finished finish, Trace next finish))) -> (finish : Scheduler dg ** (Finished finish, Trace cur finish))
findTraceHelper cur rec =
  case findStep cur of
       Left isDone => (cur ** (isDone, StartHere cur))
       Right (nextOne ** step) =>
        let
          measureDec = stepDecreasesMeasure step
          (last ** (lastFinished, restTrace)) = rec nextOne (rewrite measureDec in reflexive {ty = Nat, rel = LTE})
        in
        (last ** (lastFinished, WithStep step restTrace))

total
findTrace : {ts : List Task} -> {dg : DAG ts} -> (s : Scheduler dg) -> (finish : Scheduler dg ** (Finished finish, Trace s finish))
findTrace = sizeInd {P = \sched => (finish : Scheduler dg ** (Finished finish, Trace sched finish))} findTraceHelper

