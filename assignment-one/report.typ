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

=== Definition 9
A scheduler state $S$ over a directed acyclic graph $G = (T, E)$ is _finished_ if $forall t in T [t in F]$

=== Lemma 1
If every node in a directed graph $G = (V,E)$ has an outgoing edge, the graph must be cyclic.

==== Proof of lemma 1
Pick any $v in V$. Because each node has an outgoing edge, it is possible to cross $|V|$ edges starting from $v$. Every time you cross an edge to an adjacent node, one of the following must be true:
  + You have visited the adjacent node before
  + You have not visited the adjacent node before.
  In the first case, this means there must be a cycle. If, after $|V|$ steps, you have not found a cycle, this means you have visited $|V| + 1$ unique nodes, which is not possible. Therefore, the graph must be cyclic. $qed$
=== Lemma 2
For a state $S = (F, P, R, E)$ over a directed acyclic dependency graph $G = (V, E)$, if $P != emptyset and R = emptyset and E = emptyset$ then there is always an enabled task in $P$.

==== Proof of lemma 2
The proof is by contradiction. Suppose that we cannot find an enabled task in $P$. This means that each pending task depends on an unfinished task. Since $P, R, E, F$ are pairwise disjoint and cover $V$, and $R$ and $E$ are empty, this means that these unfinished tasks must be in the pending set also. Therefore, each node in the subgraph $G_s = (P, {u->v in E | u in P and v in P})$ must have at least one outgoing edge. By lemma 1, this implies $G_s$ is cyclic. Since $G_s$ is cyclic, $G$ must be cyclic. $arrow.r.double arrow.l.double$

=== Theorem 1 (Terminal and finished states)
A state is finished iff it is terminal.

==== Proof of theorem 1
===== $->$ direction (if a state is finished, then it is terminal.)
In a finished state $S$ over $G = (T, E)$, every $t$ in $T$ is in $F$. Since $P, R, E, F$ are pairwise disjoint and cover $T$, this means that the sets $P, R, E$ are all empty. Therefore, no steps are possible, and thus the finished state is terminal.
===== $<-$ direction (if a state is terminal, then it is finished.)
We will do the contrapositive proof: if a state is not finished, then it is not terminal. Consider a non-finished state $S$. Then, one of the following must hold:
  + $E != emptyset$
  + $R != emptyset$
  + $P != emptyset$
If $E != emptyset$, then there is some $e in E$. Therefore, a step to $S' = (F union {e}, R, P, emptyset)$ is possible, and $S$ is non-terminal.
If $R != emptyset and E = emptyset$, then there is some $r in R$. Therefore, a step to $S' = (F, R - {r}, P, {r})$ is possible, thus $S$ is non-terminal.
If $P != emptyset and R = emptyset and E = emptyset$, there must be some enabled $p in P$ by lemma 2. Therefore, a step to $S' = (F, {p}, P - {p}, emptyset)$ is possible, thus $S$ is non-terminal. $qed$

=== Lemma 3
$mu(S) = 0$ iff $S$ is finished. 

==== Proof of lemma 3
===== $<-$ direction (if a state is finished, then the measure is zero)
By definition, if $S = (F, P, R, E)$ over $G = (T, E)$ is finished, every task is finished. Because $F, P, R, E$ are pairwise disjoint and cover $T$, $P, R, E$ must all be empty. Therefore, $mu(S) = |E| + 2|R| +3|P| = 0$.
===== $->$ direction (if the measure is zero, then the state is finished)
if $mu(S) = |E| + 2|R| +3|P| = 0$, this means all the cardinalities must be zero, as cardinalities are non-negative. Since $|E| = 0, |R| = 0, |P| = 0$, this means $E = R = P = emptyset$. Because $F, P, R, E$ are pairwise disjoint and cover $T$, this means $forall t in T [t in F]$. Therefore, $S$ is finished. $qed$

=== Lemma 4
If $S_0 "step" S_1$ holds, $mu(S_0) = mu(S_1) + 1$

==== Proof of lemma 4
Since $S_0 "step" S_1$ holds, one of the following must be true:
  + $E_1 = emptyset and exists t in T [t in R_1 and t in E_2]$
  + $E_2 = emptyset and exists t in T [t in E_1 and t in F_2] $
  + $exists t in T [t in R_2 and t "is enabled in" S_1]$
- In case 1, $mu(S_1) - mu(S_0) = 1 + 2*(|R| - 1) + 3|P| - [0 + 2*(|R|) + 3|P|] = -1$ 
- In case 2, $mu(S_1) - mu(S_0) = 0 + 2|R| + 3|P| - [1 + 2|R| + 3|P|] = -1$
- In case 3, $mu(S_1) - mu(S_0) = |E| + 2*(|R| + 1) + 3*(|P| - 1) - [|E| + 2|R| + 3|P|] = -1$
In each case, $mu(S_1) - mu(S_0) = -1$. Therefore, in each case, $mu(S_0) = mu(S_1) + 1 qed$

=== Theorem 2 (Termination)
For every scheduler state $S_0$ there exists a finite trace to a finished state $S$.

==== Proof of theorem 2
The proof is by induction on $mu(S_0)$.
===== Base case
Suppose $mu(S_0) = 1$. By lemma 3, $S_0$ is not finished, and by theorem 1 it is therefore non-terminal. Thus, there exists some $S_1$ such that $S_0 "step" S_1$ holds. By lemma 4, $mu(S_1) = 0$. By lemma 3, $S_1$ must be finished. Therefore, the trace is the step from $S_0$ to $S_1$.
===== Inductive step
Suppose that for every scheduler state whose measure is equal to $n$ there exists a finite trace to a finished state. Suppose that $mu(S_0) = n + 1$. By lemma 3, $S_0$ is not finished, thus by theorem 1, $S_0$ is non-terminal. So, there exists some $S_1$ such that $S_0 "step" S_1$ holds. By lemma 4, $mu(S_1) = n$. By the inductive hypothesis, there is a finite trace $t$ from $S_1$ to a finished state $S$. Therefore, a finite trace from $S_0$ to $S$ is obtained by combining the step from $S_0$ to $S_1$ with $t$. 

We have shown that for every non-terminal scheduler state with an arbitrarily large measure, there is a finite trace to a finished state. Now consider a starting state. It is either terminal, or non-terminal. If it is terminal, then we have a trivial trace to a finished state, that is, itself. If it is non-terminal, then by the induction proof above, we can find a finite trace to a finished state. $qed$ 

== Writing the Proofs in Idris2

One complication with encoding the above proofs in Idris2 is the absence of a `Set` type in the standard library which is useful for theorem proving. The provided sets (found in `Data.SortedSet`) are instead intended for use in general programming, and thus do not expose any set-related propositions, like membership, equality, or a subset relation. We will first have to define this ourselves.

The simplest set-like structure available to us is the inductively defined `List` type. We will use this as a base and define the following types:
```idris
-- Proof that x is in xs
data Elem : a -> List a -> Type where
  Here : Elem x (x :: xs)
  KeepLooking : Elem x rest -> Elem x (something::rest)

-- Proof that a predicate is true of all the elements in a list
data All : (pred : a -> Type) -> List a -> Type where
  VacuouslyTrue : All pred []
  (::) : {x : a} -> pred x -> All pred xs -> All pred (x::xs)

-- If p is true of every element in es, and for any e, p of e implies p' of e, then p' is true of every element in es.
propImplies : {prem1, prem2 : a -> Type} -> ((e : a) -> prem1 e -> prem2 e) -> All prem1 es -> All prem2 es
propImplies f VacuouslyTrue = VacuouslyTrue
propImplies f (cur :: rest) = f _ cur :: propImplies f rest
```
We can then use these to define a subset equality relation between two lists, and prove that it is indeed an equivalence relation.
```idris
Subset : List a -> List a -> Type
Subset xs ys = All (`Elem`ys) xs

SsEq : List a -> List a -> Type 
SsEq a b = (a `Subset` b, b `Subset` a) 

extractPrf : x `Elem` xs -> All prop xs -> prop x
extractPrf Here (y :: _) = y
extractPrf (KeepLooking y) (_ :: w) = extractPrf y w

-- Subset reflexivity
listContainsItsContents : {list : _} -> All (`Elem`list) list
listContainsItsContents {list = []} = VacuouslyTrue
listContainsItsContents {list = (x :: xs)} =
  let
    ind = listContainsItsContents {list = xs}
    xIsHere : x `Elem` (x::xs) = Here
    ifTheyreInHereTheyreInTheSuperset = propImplies (\_ => KeepLooking) ind
  in
  xIsHere :: ifTheyreInHereTheyreInTheSuperset

ssEqRefl : {a : _} -> a `SsEq` a
ssEqRefl = (listContainsItsContents, listContainsItsContents)

ssEqSym : a `SsEq` b -> b `SsEq` a
ssEqSym (x, y) = (y, x)

ssEqTrans : {a,b,c : _} -> a `SsEq` b -> b `SsEq` c -> a `SsEq` c
ssEqTrans (assb, bssa) (bssc, cssb) =
  let
    assc = propImplies (\_, einb => extractPrf einb bssc) assb
    cssa = propImplies (\_, einb => extractPrf einb bssa) cssb
  in
  (assc, cssa)
```
Next, we will need to model a directed acyclic graph. Traditional graphs (that is, a set of vertices and an adjacency relation) are difficult to model ergonomically in Idris because of the aforementioned lack of sets, and also because they are not inductively defined. Instead, we can use the fact that our dependency graph must be acyclic to construct it inductively by starting with an empty graph and adding sources (nodes with no incoming edges.) Not needing to prove acyclicity will make the code easier to work with.
```idris
data DAG : List Task -> Type where
  Empty : DAG []
  AddTask : (t : Task) -> (deps : List Task) -> deps `Subset` tasks -> DAG tasks -> DAG (t :: tasks)
```
