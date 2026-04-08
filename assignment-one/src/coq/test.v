Require Import List.
Require Import Arith.
Require Import Relations.
Require Import Coq.Logic.Classical.
Require Import Psatz.

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

Lemma measureDecreases:
    forall S S', step S S' -> mu S' < mu S.
Proof.
    intros S S' Hstep.
    destruct Hstep.
        - unfold mu. rewrite H. cbn [F R P D].
          simpl (length [t]). simpl (length []).
          change (0 + 2 * length (R S) + 3 * length (P S)) with
            (2 * length (R S) + 3 * length (P S)).
          pose proof (Nat.add_lt_mono_r) as Hsub.
          symmetry in Hsub.
          apply Hsub with (p := 3 * length (P S)).
          pose proof (remove_length_lt Nat.eq_dec (R S) t H0) as Hlen.
          
              
            

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

Lemma lengthOneNoTail :
    forall a (l xs : list a) (x : a), l = (x :: xs) -> length l = 1 -> l = [x].
Proof.
    intros a l xs x prfCons Hlen.
    subst.
    destruct xs as [| y ys].
        - reflexivity.
        - simpl in Hlen. congruence.
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

Lemma neq_sym :
    forall a (x y : a), x <> y -> y <> x.
Proof.
    intros a x y H Hxy.
    apply H.
    symmetry.
    assumption.
Qed.

Lemma disjointPreserved :
    forall S S', disjoint S -> step S S' -> disjoint S'.
Proof.
    intros S S' fstDj Hstep.
    destruct Hstep.
        - repeat split.
            + simpl in H1.
              simpl.
              destruct (Nat.eq_dec t x).
                * subst.
                  destruct fstDj as [Hdj _].
                  specialize (Hdj x H1).
                  destruct Hdj as [Hcontra _].
                  contradiction.
                * intro.
                  apply inRemove in H2.
                  destruct H2 as [Hcontra _].
                  destruct fstDj as [Hfdj _].
                  specialize (Hfdj x H1).
                  destruct Hfdj as [Hnir _].
                  contradiction.
            + simpl in H1.
              simpl.
              destruct fstDj as [Hdj _].
              specialize (Hdj x H1).
              destruct Hdj as [_ [Hnp _]].
              assumption.
            + simpl in H1. simpl. intro. destruct H2.
                * subst.
                  destruct fstDj as [Hdj _].
                  specialize (Hdj x H1).
                  destruct Hdj as [Hcontra _].
                  contradiction.
                * assumption.
            + simpl in H1. simpl.
              apply inRemove in H1.
              destruct H1 as [xrs _].
              destruct fstDj as [_ [Hdj _]].
              specialize (Hdj x xrs).
              destruct Hdj as [Hdone _].
              assumption.
            + simpl in H1. simpl. intro. destruct H2.
                * apply inRemove in H1.
                  destruct H1 as [_ Hcontra].
                  symmetry in H2.
                  contradiction.
                * assumption.
            + intros x xinp xind. simpl in xind. simpl in xinp.
              destruct xind.
                * subst.
                  destruct fstDj as [_ [Hdj _]].
                  specialize (Hdj x H0).
                  destruct Hdj as [Hcontra _].
                  contradiction.
                * contradiction.
        - repeat split.
            + intro. simpl in H0, H1. destruct H0.
                * subst.
                  destruct fstDj as [_ [Hdj _]].
                  specialize (Hdj x H1).
                  destruct Hdj. contradiction.
                * destruct fstDj as [Hdj _].
                  specialize (Hdj x H0).
                  destruct Hdj. contradiction.
            +  intro. simpl in H0, H1. destruct H0.
                * subst.
                  destruct fstDj as [_ [_ Hdj]].
                  specialize (Hdj x H1). contradiction.
                * destruct fstDj as [Hdj _].
                  specialize (Hdj x H0).
                  destruct Hdj as [_ [Hcontra _]].
                  contradiction.
            + intro. simpl in H0, H1. assumption.
            + intro. simpl in H0, H1. destruct fstDj as [_ [Hdj _]].
              specialize (Hdj x H0).
              destruct Hdj. contradiction.
            + intro. simpl in H0, H1. assumption.
            + intros x xinp ctra. simpl in ctra. assumption.
        - repeat split.
            + intro. simpl in H0, H1. destruct H1.
                * subst. destruct H as [H _].
                  destruct fstDj as [Hdj _].
                  specialize (Hdj x H0).
                  destruct Hdj as [_ [Hcontra _]].
                  contradiction.
                * destruct fstDj as [Hdj _].
                  specialize (Hdj x H0). firstorder.
            + intro. simpl in H0, H1. apply inRemove in H1. firstorder.
            + intro. simpl in H0, H1. firstorder.
            + intro. simpl in H0, H1. destruct H0.
                * apply inRemove in H1. firstorder.
                * apply inRemove in H1. firstorder.
            + intro. simpl in H0, H1. destruct H0.
                * rewrite H0 in H. firstorder.
                * firstorder.
            + intros x xinpr xind. simpl in xind, xinpr.
              apply inRemove in xinpr. firstorder.
Qed.
              
    

Theorem wfPreserved :
    forall S S', wfState S -> step S S' -> wfState S'.
Proof.
    intros S S' fstWf Hstep. destruct fstWf as [fstOR [fstCvr fstDj]]. split.
        - apply (oneRunStep S S' fstOR) in Hstep. assumption.
        - split.
            + apply (coverStep S S' fstCvr fstOR Hstep).
            + apply (disjointPreserved S S' fstDj Hstep).
Qed.


Definition terminal (S : Scheduler) : Prop :=
    ~ exists S', step S S'.

Definition finished (S : Scheduler) : Prop :=
    forall t, In t allTasks -> In t (F S).

Lemma findNotFinished :
    forall S, ~finished S -> covers S -> exists t,
        In t (D S) \/ In t (R S) \/ In t (P S).
Proof.
    intros S Hnf Hcv.
    apply not_all_ex_not in Hnf.
    destruct Hnf as [t Hnf].
    destruct (classic (In t allTasks)).
        - specialize (Hcv t H). firstorder.
        - exfalso. apply Hnf. intro. contradiction.
Qed.

Lemma findEnabled:
    forall S, wfState S -> R S = [] -> D S = [] -> ~finished S -> exists p, enabled S p.
Proof.
    intros S [Hmax [Hcov Hdis]] noR noD noFinish.
    assert (pne : P S <> []).
        - destruct (P S) as [| p ps] eqn:NP.
            + assert (finish : finished S).
                * intros someT Hsti.
                  specialize (Hcov someT Hsti).
                  destruct Hcov as [inF | [inR | [inP | inD]]].
                    -- assumption.
                    -- rewrite noR in inR. contradiction.
                    -- rewrite NP in inP. contradiction.
                    -- rewrite noD in inD. contradiction.
                * contradiction.
            + congruence.
        - destruct (P S) as [| p ps] eqn:NP.
            + contradiction.
            + 

Theorem progress:
    forall S, wfState S -> ~finished S -> exists S', step S S'.
Proof.
    intros S fstWf Hnf.
    destruct fstWf as [fstOR [fstCvr fstDj]].
    pose proof (findNotFinished S Hnf fstCvr).
    destruct H as [t H].
    destruct H as [HD | [HR | HP]].
        - exists {|F := t :: F S; R := R S; P := P S; D := []|}.
          apply complete. assumption.
        - destruct (D S) as [| d ds] eqn:HD.
            + exists {|F := F S; R := remove Nat.eq_dec t (R S); P := P S; D := [t]|}.
              apply start; assumption.
            + destruct fstOR.
                * rewrite HD in H. simpl in H. congruence.
                * pose proof (lengthOneNoTail Task (D S) ds d HD H).
                  exists {|F := d :: F S; R := R S; P := P S; D := []|}.
                  apply complete.
                  rewrite H0. left. reflexivity.
        - destruct (D S) as [| d ds] eqn:HD.
            + destruct (R S) as [| r rs] eqn:HR.
                (*lemma 2 goes here*)
                * give_up.
                * exists {|F := F S; R := remove Nat.eq_dec r (R S); P := P S; D := [r]|}.
                  apply start.
                    -- assumption.
                    -- rewrite HR. left. reflexivity.
            + destruct fstOR.
                * rewrite HD in H. simpl in H. congruence.
                * pose proof (lengthOneNoTail Task (D S) ds d HD H).
                  exists {|F := d :: F S; R := R S; P := P S; D := []|}.
                  apply complete.
                  rewrite H0. left. reflexivity.
Admitted.



End Scheduler.