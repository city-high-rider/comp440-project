Require Import List.
Require Import Arith.
Require Import Relations.

Import ListNotations.

Section Scheduler.

Definition Task := nat.

Record Scheduler  := {
    F : list Task;
    R : list Task;
    P : list Task;
    D : list Task;
}.

Definition mu (S : Scheduler) : nat :=
    length (D S) + 2*length(R S) + 3*length (P S).

(*A quick test*)
Compute mu {| F := []; R := [1]; P := [2;3]; D := [] |}.

Variable E : Task -> Task -> Prop.

Definition acyclic :=
    forall t, ~ clos_trans Task E t t.

Hypothesis E_acyclic : acyclic.

Definition enabled (S : Scheduler) (t : Task) : Prop :=
    In t (P S) /\
    forall d, E d t -> In d (F S).

Inductive step : Scheduler -> Scheduler -> Prop :=
    | start :
        forall S t,
            D S = [] ->
            In t (R S) ->
            step S
                {| F := F S;
                    R := remove Nat.eq_dec t  (R S);
                    P := P S;
                    D := [t] 
                |}

    | complete :
        forall S t,
            In t (D S) ->
            step S
                {| F := t :: F S;
                    R := R S;
                    P := P S;
                    D := [];
                |}

    | enqueue :
        forall S t,
            enabled S t ->
            step S
                {| F := F S;
                    R := t :: R S;
                    P := remove Nat.eq_dec t (P S);
                    D := D S;
                |}.

Variable allTasks : list Task.

Definition covers (S : Scheduler) : Prop :=
    forall t, In t allTasks -> In t (F S) \/ In t (R S) \/ In t (P S) \/ In t (D S).

Definition disjoint (S : Scheduler) : Prop :=
  (forall x, In x (F S) -> ~ In x (R S) /\ ~ In x (P S) /\ ~ In x (D S)) /\
  (forall x, In x (R S) -> ~ In x (P S) /\ ~ In x (D S)) /\
  (forall x, In x (P S) -> ~ In x (D S)).

Definition wfState (S : Scheduler) : Prop :=
    covers S /\ disjoint S.

Lemma inRemove :
    forall x y l, In x (remove Nat.eq_dec y l) -> In x l /\ x <> y.
Proof.
    intros x y l.
    induction l; simpl; intros H.
    - contradiction.
    - destruct (Nat.eq_dec y a).
        + subst. apply IHl in H. tauto.
        + simpl in H. destruct H.
            * subst. split; auto.
            * apply IHl in H. destruct H. split; auto.
Qed.

Lemma inRemoveInv :
    forall x y l, In x l -> x <> y -> In x (remove Nat.eq_dec y l).
Proof.
    intros x y l.
    induction l; simpl; intros H Hin.
        - contradiction.
        - destruct (Nat.eq_dec y a).
            + subst. simpl in H. destruct H.
                * symmetry in H. contradiction.
                * apply IHl in H; assumption.
            + destruct H as [Heq | Hinl].
                * left. assumption.
                * right. apply IHl; assumption.
Qed.



End Scheduler.