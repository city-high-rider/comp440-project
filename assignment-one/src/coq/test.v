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

Definition maxOneRun (S : Scheduler) : Prop :=
    length (D S) = 0 \/ length (D S) = 1.

Definition wfState (S : Scheduler) : Prop :=
    maxOneRun S /\ covers S /\ disjoint S.

Lemma oneRunStep :
    forall S S', maxOneRun S -> step S S' -> maxOneRun S'.
Proof.
    intros S S' fstOR Hstep.
    destruct Hstep.
        - right. auto.
        - left. auto.
        - destruct fstOR.
            + left. assumption.
            + right. assumption.
Qed.

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

Lemma lengthOneUnique :
    forall (a : Type) (l : list a) (x y : a),
    length l = 1 -> In x l -> In y l -> x = y.
Proof.
    intros a l x y Hlen Hinx Hiny.
    destruct l as [| z zs].
        - contradiction.
        - destruct zs as [| z' zs'].
            + destruct Hinx as [Hx | []].
                destruct Hiny as [Hy | []].
                subst.
                reflexivity.
            + simpl in Hlen. congruence.
Qed.

Lemma coverStep :
    forall S S', covers S -> maxOneRun S -> step S S' -> covers S'.
Proof.
    intros S S' fstCvr fstOR HStep.
    destruct HStep.
        - intros x Hx.
          destruct (fstCvr x Hx) as [HF | [HR | [HP | HD]]].
            + simpl. left. assumption.
            + simpl. destruct (Nat.eq_dec x t).
                * subst. right. right. right. left. reflexivity.
                * right. left. apply inRemoveInv; auto.
            + simpl. right. right. left. assumption.
            + rewrite H in HD. contradiction.
        - intros x Hx.
          destruct (fstCvr x Hx) as [HF | [HR | [HP | HD]]].
            + simpl. left. right. assumption.
            + simpl. right. left. assumption.
            + simpl. right. right. left. assumption.
            + simpl. destruct fstOR.
                * apply length_zero_iff_nil in H0.
                  rewrite H0 in H. contradiction.
                * specialize (lengthOneUnique Task (D S) x t H0 HD H).
                    intros.
                    symmetry in H1.
                    left. left. assumption.
        - intros x Hx.
          destruct (fstCvr x Hx) as [HF | [HR | [HP | HD]]].
            + simpl. left. assumption.
            + simpl. right. left. right. assumption.
            + simpl. destruct (Nat.eq_dec t x).
                * right. left. left. assumption.
                * right. right. left. apply inRemoveInv.
                    -- assumption.
                    -- symmetry. assumption.
            + simpl. right. right. right. assumption.
Qed.


Lemma wfPreserved :
    forall S S', wfState S -> step S S' -> wfState S'.
Proof.
    intros S S' [Hcov Hdis] Hstep.
    destruct Hstep.
        (*ready -> running*)
        - split.
            (*coverage*)
            + intros x Hx.
              destruct (Hcov x Hx) as [HF | [HR | [HP | HD]]].
                * left; assumption.
                * destruct (Nat.eq_dec x t).
                    -- subst. right. right. right. simpl. auto.
                    -- right. left. simpl. apply inRemoveInv; auto.
                * right. right. left. assumption.
                * rewrite H in HD. contradiction.
            (*disjointness*)
            + split.
                * intros x HxF. split.
                    -- intro HR'. apply inRemove in HR'.
                        simpl in HxF.
                        destruct HR' as [HR _].
                        destruct Hdis as [Hfds _].
                        specialize (Hfds x HxF).
                        destruct Hfds as [Hnir _].
                        contradiction.
                    -- split. 
                        ++ simpl.
                            simpl in HxF.
                            destruct Hdis as [Hfds _].
                            specialize (Hfds x HxF).
                            destruct Hfds as [_ [xnp _]].
                            assumption.
                        ++ simpl in HxF.
                            simpl.
                            intro Hcontra.
                            destruct Hcontra.
                                ** symmetry in H1.
                                    rewrite H1 in HxF.
                                    destruct Hdis as [Hfds _].
                                    specialize (Hfds t HxF).
                                    destruct Hfds as [Hnrs _].
                                    contradiction.
                                ** assumption.
                * split. intros x HxR. simpl in HxR. split.
                    -- simpl.
                        intros Hcontra.
                        apply inRemove in HxR.
                        destruct HxR as [Hxrs _].
                        destruct Hdis as [_ [Hrds _]].
                        specialize (Hrds x Hxrs).
                        destruct Hrds as [Hnps _].
                        contradiction.
                    -- simpl.
                        intro.
                        destruct H1.
                            ++ apply inRemove in HxR.
                                destruct HxR as [_ Hnt].
                                symmetry in H1.
                                contradiction.
                            ++ assumption.
                    -- intros x HxP.
                        simpl.
                        simpl in HxP.
                        intro.
                        destruct H1.
                            ++ rewrite H1 in H0.
                                destruct Hdis as [_ [Hrds _]].
                                specialize (Hrds x H0).
                                destruct Hrds as [Hnp _].
                                contradiction.
                            ++ assumption.
        (*running -> finished*)
        - split.
            + intros x Hx.
              destruct (Hcov x Hx) as [HF | [HR | [HP | HD]]].
                * simpl. left. right. assumption.
                * simpl. right. left. assumption.
                * simpl. right. right. left. assumption.
                * simpl. left. left.

                        
                        





End Scheduler.