# Verifying a Simple DAG Scheduler

###### (TODO: My ID here) - COMP440 Assignment One

---

## Aims and Objectives
The objective of this report is to model and prove the termination of a directed acyclic graph (DAG) scheduler in Idris2 and Coq (the precise theorem will be stated at the end of the next section). The proof will then be used as a vehicle to compare both languages by considering their available tooling (specifically interactive editing features, content of the standard library, and package managers), approaches to encoding propositions and proofs, as well as their methods for judging these propositions. Finally, a subjective account of both languages' developer experience will be given.

## Preliminary Models, Definitions, and Proofs

### Definition 1
A "Scheduler state" over a directed graph `G = (V, E)` is comprised of four sets of tasks that partition `V`:
  1. The set of finished tasks
  2. The set of ready tasks
  3. The set of pending tasks
  4. The set of running tasks, which may contain at most one element.

For brevity, this construct may ocasionally referred to as a "scheduler."

### Definition 2
A scheduler state over `G = (V, E)` is "well formed" if for every task `t` in the "finished" set, every element `d` such that `dEt` holds is in the "finished" set.

### Definition 3
A task `t` is enabled in a scheduler state `S` over a directed graph `G = (T,E)` if `t` is in the "pending" set of `S`, and for all `d` in `T` such that `dEt` holds, `d` is in the "finished" set of `S`.

### Definiton 4
A "step" or "state transition" is a 2-tuple of scheduler states `(S1, S2)` over a directed graph `G = (T, E)` such that exactly one of the following conditions hold:
  1. The set of "running" tasks in `S1` is empty, and there exists a task `t` such that `t` is in the "ready" set of `S1` and the "running" set of `S2`.
  2. There exists a task `t` such that `t` is in the "running" set of `S1`, `t` is in the "finished" set of `S2`, and the "running" set of `S2` is empty.
  3. There exists a task `t` such that `t` is enabled in `S1` and `t` is in the "ready" set of `S2`.

### Definition 5
A "trace" between two scheduler states `S1` and `S2` is a witness of `S1 Step* S2`, where `Step*` is the transitive-reflexive closure of the step relation.

### Definition 6
a scheduler state `S` is "reachable" from a starting scheduler state `S0` if there is a trace from `S0` to `S`. The set `Reach(S0)` are all states that are reachable from `S0`.

### Definition 7
A scheduler state `S` is "terminal" if there does not exist an `S'` such that `S Step S'` holds.

