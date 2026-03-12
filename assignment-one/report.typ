= Verifying a Simple DAG Scheduler

== (TODO: My ID here) - COMP440 Assignment One

---

== Aims and Objectives
The objective of this report is to model and prove the termination of a directed acyclic graph (DAG) scheduler in Idris2 and Coq (the precise theorem will be stated at the end of the next section). The proof will then be used as a vehicle to compare both languages by considering their available tooling (specifically interactive editing features, content of the standard library, and package managers), approaches to encoding propositions and proofs, as well as their methods for judging these propositions. Finally, a subjective account of both languages' developer experience will be given.

== Preliminary Models, Definitions, and Proofs

=== Definition 1
A _Scheduler state_ over a directed acyclic graph $G = (V, E)$ is comprised of four sets of tasks that are pairwise disjoint and cover `V`:
  1. The set of finished tasks, $F$
  2. The set of ready tasks, $R$
  3. The set of pending tasks, $P$
  4. The set of running tasks, $E$, which may contain at most one element.

=== Definition 2
A scheduler state over $G = (V, E)$ is _well formed_ if $forall t in F [forall d in V [d E t -> d in F]]$

=== Definition 3
A task $t$ is _enabled_ in a scheduler state $S$ over a directed acyclic graph $G = (T,E)$ if $t in P and forall d in T [d E t -> d in F]$ 

=== Definiton 4
A _step_ is a binary relation on states $S_1, S_2$ over a directed acyclic graph $G = (T, E)$ which holds iff exactly one of the following conditions are true: 
  + $E_1 = emptyset and exists t in T [t in R_1 and t in E_2]$
  + $E_2 = emptyset and exists t in T [t in E_1 and t in F_2] $
  + $exists t in T [t in R_2 and t "is enabled in" S_1]$

=== Definition 5
A "trace" between two scheduler states $S_1$ and $S_2$ is a witness of $S_1 "Step"^* S_2$, where $"Step"^*$ is the transitive-reflexive closure of the step relation.

=== Definition 6
a scheduler state $S$ is "reachable" from a starting scheduler state $S_0$ if there is a trace from $S_0$ to $S$. The set $"Reach"(S_0)$ are all states that are reachable from $S_0$.

=== Definition 7
A scheduler state $S$ is "terminal" if there does not exist an $S'$ such that $S "Step" S'$ holds.

=== Definition 8
The measure $mu$ of a state $S$ is a function $mu : SS -> NN$ where $mu(S) = |E| + 2|R| +3|P|$


=== Theorem (Termination)
For any well-founded scheduler state $S_0$ there exists a finite trace to some terminal state $S$. 
