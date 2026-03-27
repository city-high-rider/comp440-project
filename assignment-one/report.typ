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

== What does it mean for a program to "prove" something?
Logic is a tool for deriving new facts from existing ones while ensuring that the truth of these facts is preserved. A particular school of logic called constructivism asserts that to show a proposition is true, you must be able to find evidence to support it; it is not sufficient to assume the proposition does not hold and derive a contradiction.

So, under constructivist logic, you can think of a proposition as not just an assertion that something is true, but also evidence about why it must be true. Furthermore, that evidence is more than the absence of falsehood; it too is an object with structure that can be manipulated. This idea naturally extends to proofs, which now can be viewed as functions which transform valid evidence for one fact into valid evidence for another fact while preserving the truth and this constructive property.

Constructivist philosophy makes the relationship between proofs and computer programs much easier to see. Specifically, this connection is called the _Curry-Howard_ correspondence, which shows that propositions are interchangable with types, and proofs are interchangable with programs.

Since a proposition is a type, then evidence for that proposition must be a value of that type. Propositions that are true should have evidence for their truth, while it should be impossible to provide evidence for a false proposition. Even though that view is simple, it is already a practical mindset to have when encoding propositions as type definitions. For instance, here's how it can help us write a type that encodes a proposition that $a <= b$ for natural numbers.

Firstly, the proposition "$a$ is less than or equal to $b$" mentions two natural numbers, $a$ and $b$. Therefore, we must actually define a family of types for all the combinations of two natural numbers:
```idris
data LTE : Nat -> Nat -> Type
```
With this definition, all of the following are now valid _propositions_:
 - `LTE 0 0` ($0 <= 0$)
 - `LTE 51 9` ($51 <= 9$)
 - `LTE 2 10` ($2 <= 10$)
But not all of these propositions are necessarily true. The next step is to define what kind of _evidence_ we can use to justify this proposition. For instance, zero should be less than or equal to any other natural number:
```idris
ZLTEAnything : {someNumber : Nat} -> LTE 0 someNumber
```
Notice that by adding `someNumber` as a parameter to `ZLTEAnything`, we have quantified it as _any_ natural number, because there are absolutely no restrictions to the number we can pass to that constructor. This means that `ZLTEAnything` encodes the axiom $forall "someNumber" in NN [0 <= "someNumber"]$.

Next, if we know that $a <= b$, then $(a+1) <= (b+1)$ should be true as well. This gives the second axiom/type constructor:
```idris
Bump : {a,b : Nat} -> LTE a b -> LTE (S a) (S b)
```
Or, in first-order logic notation: $forall a in NN. forall b in NN. [a <= b -> (a+1) <= (b+1)]$.

Finally, putting these two axioms together gives the complete definition for the $<=$ proposition. For readability, the explicit quantification of variables will also be omitted, as Idris will automatically add them as implicit arguments for us.
```idris
data LTE : Nat -> Nat -> Type where
  ZLTEAnything : LTE 0 someNumber
  Bump : LTE a b -> LTE (S a) (S b)
```
Now it's possible to check whether or not the previous three propositions are true or not by attempting to construct evidence for them with these two axioms:
 - `LTE 0 0` ($0 <= 0$) is trivially true. Since the lefthand number is a zero, `ZLTEAnything {someNumber = 0}` is valid evidence for this proposition. 
 - `LTE 51 9` ($51 <= 9$) is false. Observe that the lefthand number is $51$, not zero, meaning that evidence for this must be constructed by applying the `Bump` axiom to evidence that $50 <= 8$. Repeating the same reasoning, we may eventually conclude that in order to construct evidence that $51 <= 9$, it is necessary to construct evidence that $42 <= 0$. However, by again analysing the axioms, we may deduce that this is not possible. There are only two we can apply: `ZLTEAnything`, which is evidence for $0 <= x$, and `Bump`, which is evidence for $S(a) <= S(b)$. The first axiom could not be used to prove this, because the left-hand number is $42$, not zero. The second axiom could also not be used to prove this, because the right-most number is zero.
 - `LTE 2 10` ($2 <= 10$) is true. Neither the left nor right-hand numbers are zero, so it is necessary to `Bump` a proof that $1 <= 9$. Once again, neither one nor nine are zero, so to get this subproof, it is necessary to `Bump` a proof that $0 <= 8$. This sub-subproof can finally be constructed with the `ZLTEAnything` axiom applied to the number eight. Putting this together, the _evidence_ that $2 <= 10$ is `Bump (Bump (ZLTEAnything {someNumber = 8}))`.

Now that we've seen how to encode a proposition as a type, what remains is to see how a program can encode a proof. Can we show that our `LTE` relation is transitive?

The starting point is the _type signature_ of the proof-function. Suppose we have evidence that $a <= b$ and $b <= c$. Can we use that to construct evidence that $a <= c$?
```idris
lteTrans : LTE a b -> LTE b c -> LTE a c
```
This proof can be done with cases. Each piece of evidence was either constructed with `ZLTEAnything` or `Bump`. This makes four combinations:
1. `LTE a b` and `LTE b c` were both constructed with `ZLTEAnything`. This means `a` and `b` are both zero, while `c` is some other number. Therefore, the goal may be updated with this information: now we are trying to provide evidence for `LTE 0 c`, which can be done with `ZLTEAnything {someNumber = c}`.
2. `LTE a b` was constructed with `ZLTEAnything`, while `LTE b c` was constructed with `Bump`. Much like the last case, knowing that the first constructor is `ZLTEAnything` tells us that `a = 0`, which reduces the goal to `LTE 0 c`. Therefore, `ZLTEAnything {someNumber = c}` is sufficient evidence.
3. `LTE a b` was constructed with `Bump`, while `LTE b c` was constructed with `ZLTEAnything`. If this is the case, we gather some information: `a` and `b` are both successors of some natural number, and `b` is zero. This is a contradiction, because `b` cannot both be zero and nonzero at the same time. Therefore, we have no obligation to prove anything in this case, since it's impossible to provide this combination of evidence.
4. `LTE a b` and `LTE b c` were both constructed by `Bump`ing a subproof. Thus, we can gather that:
  - `a = S x` for some `x`
  - `b = S y` for some `y` 
  - `c = S z` for some `z`
  - There is evidence that `LTE x y` and `LTE y z` from the subproofs that were `Bump`ed.
  Here, we can call the proof-function recursively to get evidence that `LTE x z` from the evidence that `LTE x y` and `LTE y z`. Because `x, y, z` are all strictly smaller than `a, b, c`, eventually this function must reach one of its base cases. We may then apply `Bump` to this result to obtain `LTE (S x) (S z)`, which is the goal.

And here is the Idris2 implementation of the function:
```idris
total
lteTrans : LTE a b -> LTE b c -> LTE a c
lteTrans ZLTEAnything ZLTEAnything = ZLTEAnything
lteTrans ZLTEAnything (Bump subprf) = ZLTEAnything
lteTrans (Bump subprf) ZLTEAnything impossible
lteTrans (Bump subprfA) (Bump subprfB) = Bump (lteTrans subprfA subprfB)
```
There are a few notable things about this function. Firstly, it is substantially more terse than the preceding written proof. Secondly, there is a `total` annotation at the top.

The `total` annotation forces the compiler to verify that the function is _covering_, meaning it should be defined for all inputs, and that it eventually terminates. Termination is a notable property: it is not trivial to verify in general, and if a function which computes evidence does not terminate, it means the proof is not sound.

Consider the following function. The type signature can be interpreted as "for any proposition, return evidence of that proposition," and the implementation goes into an endless recursive loop:
```idris
anyProof : {a : Type} -> a
anyProof = anyProof
```
Thus, `anyProof {a = LTE 1 0}` is valid evidence that $1 < 0$ as far as the type checker is concerned, although in practice asking the program to actually _provide_ this evidence will cause it to loop forever. Clearly, this is not desirable, but unfortunately, there is no way to verify whether or not an arbitrary program will terminate. Thus, the totality checker in Idris works conservatively: any program it verifies to be total is actually total, but it will not accept every total program. In particular, all of the following must be true for a function to be verified as total:
1. It is covering
2. Every function the implementation calls is also total
3. In a recursive call, one argument must be _syntactially smaller_. That is, it must be a sub-term of the current argument. 
The totality checker is clever enough that usually, no manual intervention by the programmer is required. However, for proofs that instead use a strictly decreasing measure function to justify termination, some more work is required, which will be discussed in more detail at the end of the idris section.

Finally, it is worth mentioning why the idris2 proof is so terse, as it will provide a bit of context when we later discuss the languages' tooling and compare it to tactic-based theorem proving like Rocq. The compactness is mostly because the type checker is only concerned with verifying that the provided values are well-formed and that they are evidence for the relevant proposition, not some other one. Much of what was done in the written transitivity proof is deducing information based on the constructors of the input evidence, using it to refine a goal, or justifying that the information is contradictiory. The idris type checker does this all automatically through a process called unification; We did not have to mention parameters like `someNumber` at all because the unification process found an assignment which made the expression type check. We also did not have to justify why the second case was impossible, as the type checker could already see the contradiction, although sometimes it does need a bit of help. Finally, we didn't need to justify that the recursive call would terminate, because the totality checker could see that its arguments were syntactically smaller.



== Writing the Proofs in Idris2
