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

Lemma ltsSplit :
    forall a b, a < S b -> a = b \/ a < b.
Proof.
    lia.
Qed.

Lemma ltSum:
    forall a b, a < b -> exists n, (S n) + a = b.
Proof.
    intros a b Hlt. simpl. induction b.
        - inversion Hlt.
        - apply ltsSplit in Hlt. destruct Hlt.
            + rewrite H. exists 0. auto.
            + pose proof (IHb H) as He. destruct He.
              symmetry in H0.
              rewrite H0.
              exists (S x). auto.
Qed.

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
          apply ltSum in Hlen. destruct Hlen.
          replace (2 * length (R S)) with (2 * (Datatypes.S x + length (remove Nat.eq_dec t (R S)))).
            + pose proof (Nat.mul_add_distr_l 2 (Datatypes.S x) (length (remove Nat.eq_dec t (R S)))).
              rewrite H2.
              apply Hsub with (p := 2 * length (remove Nat.eq_dec t (R S))).
              lia.
            + f_equal. assumption.
        - unfold mu. cbn [F R P D]. simpl (length []).
          pose proof (Nat.add_lt_mono_r) as Hsub.
          symmetry in Hsub.
          apply Hsub with (p := 3*length (P S)).
          apply Hsub with (p := 2*length (R S)).
          destruct (D S) as [| d ds].
            + contradiction.
            + simpl. lia.
        - unfold mu. cbn [F R P D].
          pose proof (Nat.add_lt_mono_l) as Hsub.
          repeat rewrite <- Nat.add_assoc.
          symmetry in Hsub.
          apply Hsub with (p := length (D S)).
          simpl (length (t :: R S)).
          rewrite (Nat.mul_succ_r 2 (length (R S))).
          repeat rewrite <- Nat.add_assoc.
          apply Hsub with (p := 2*length(R S)).
          destruct H as [H _].
          pose proof (remove_length_lt Nat.eq_dec (P S) t H) as Hlen.
          apply ltSum in Hlen. destruct Hlen.
          replace (3 * length (P S)) with (3 * (Datatypes.S x + length (remove Nat.eq_dec t (P S)))).
            + rewrite (Nat.mul_add_distr_l 3 (Datatypes.S x) (length (remove Nat.eq_dec t (P S)))).
              pose proof (Nat.add_lt_mono_r) as HsubR.
              symmetry in HsubR.
              apply HsubR with (p := 3 * length (remove Nat.eq_dec t (P S))).
              lia.
            + f_equal. assumption.
Qed. 

Variable allTasks : list Task.

Hypothesis E_closed :
    forall d t, E d t -> In t allTasks -> In d allTasks.

Definition covers (S : Scheduler) : Prop :=
    forall t, In t allTasks -> In t (F S) \/ In t (R S) \/ In t (P S) \/ In t (D S).

Definition disjoint (S : Scheduler) : Prop :=
  (forall x, In x (F S) -> ~ In x (R S) /\ ~ In x (P S) /\ ~ In x (D S)) /\
  (forall x, In x (R S) -> ~ In x (P S) /\ ~ In x (D S)) /\
  (forall x, In x (P S) -> ~ In x (D S)).

Definition maxOneRun (S : Scheduler) : Prop :=
    length (D S) = 0 \/ length (D S) = 1.

Definition statusAreTasks (S : Scheduler) : Prop :=
    forall t, In t (F S) \/ In t (R S) \/ In t (P S) \/ In t (D S)
        -> In t allTasks.

Definition wfState (S : Scheduler) : Prop :=
    maxOneRun S /\ covers S /\ disjoint S /\ statusAreTasks S.

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

Theorem statusAreTasksPreserved :
    forall S S', statusAreTasks S -> step S S' -> statusAreTasks S'.
Proof.
    intros S S' Hstat Hstep.
    destruct Hstep.
        - intros st [Inf | [InRSmaller | [Inp | InDSingle]]].
            + simpl in Inf. apply (Hstat st). left. assumption.
            + simpl in InRSmaller. apply inRemove in InRSmaller.
              destruct InRSmaller as [Istrs _].
              apply (Hstat st). right. left. assumption.
            + simpl in Inp. apply (Hstat st). right. right. left. assumption.
            + cbn [D] in InDSingle. destruct InDSingle.
                * rewrite <- H1. apply (Hstat t). right. left. assumption.
                * contradiction.
        - intros st [InfBigger | [InR | [Inp | InEmpty]]].
            + simpl in InfBigger. destruct InfBigger.
                * rewrite <- H0. apply (Hstat t). right. right. right. assumption.
                * apply (Hstat st). left. assumption.
            + simpl in InR. apply (Hstat st). right. left. assumption.
            + simpl in Inp. apply (Hstat st). right. right. left. assumption.
            + cbn [D] in InEmpty. contradiction.
        - intros st [Inf | [InRBigger | [InPSmaller | InD]]].
            + simpl in Inf. apply (Hstat st). left. assumption.
            + simpl in InRBigger. destruct InRBigger.
                * destruct H. rewrite H0 in H. apply (Hstat st).
                  right. right. left. assumption.
                * apply (Hstat st). right. left. assumption.
            + simpl in InPSmaller. apply inRemove in InPSmaller.
              destruct InPSmaller as [Hinp _].
              apply (Hstat st). right. right. left. assumption.
            + simpl in InD. apply (Hstat st). right. right. right. assumption.
Qed. 

Theorem wfPreserved :
    forall S S', wfState S -> step S S' -> wfState S'.
Proof.
    intros S S' fstWf Hstep. destruct fstWf as [fstOR [fstCvr [fstDj fstSt]]]. split.
        - apply (oneRunStep S S' fstOR) in Hstep. assumption.
        - split.
            + apply (coverStep S S' fstCvr fstOR Hstep).
            + split.
                * apply (disjointPreserved S S' fstDj Hstep).
                * apply (statusAreTasksPreserved S S' fstSt Hstep).
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

Lemma mkPorf:
    forall S, covers S -> (R S) = [] -> (D S) = [] ->
        forall t, In t allTasks -> (In t (F S)) \/ (In t (P S)).
Proof.
    intros S Hcov Hrn Hdn t Hia.
    destruct (Hcov t Hia) as [Hif | [Hir | [Hip | Hid]]].
        - left. assumption.
        - rewrite Hrn in Hir. contradiction.
        - right. assumption.
        - rewrite Hdn in Hid. contradiction.
Qed. 

Lemma allPorSomeQ :
  forall (a : Type) (l : list a) (p q : a -> Prop),
    (forall x, In x l -> p x \/ q x) ->
    ( (forall x, In x l -> p x)
    \/ (exists c, In c l /\ q c)).
Proof.
    intros a l p q Hporq.
    induction l as [| h t Ih].
        - left. intros x Hcontra. contradiction.
        - destruct (Hporq h (or_introl eq_refl)) as [Hp | Hq].
            + specialize (Ih (fun x Hx => Hporq x (or_intror Hx))).
              destruct Ih as [Ihp | [c [Hc Hqc]]].
                * left. intros y Hyin. simpl in Hyin. destruct Hyin.
                    -- rewrite <- H. assumption.
                    -- specialize (Ihp y H). assumption.
                * right. exists c. split.
                    -- simpl. right. assumption.
                    -- assumption.  
            + right. exists h. split.
                * simpl. left. reflexivity.
                * assumption.
Qed.

(*i'm sure this is in a library somewhere, but I can't find it for the life of me.*)
Lemma notImplies:
    forall (P Q : Prop), ~(P -> Q) -> (P /\ ~Q).
Proof.
    intros p q nimp.
    Search "not_imp".
    split.
        - apply (not_imply_elim p q). assumption.
        - apply (not_imply_elim2 p q). assumption.
Qed.

Lemma checkEnabled:
    forall S p, (forall t, In t allTasks -> In t (F S) \/ In t (P S))
        -> statusAreTasks S
        -> In p (P S)
        -> enabled S p \/ (exists d, E d p /\ In d (P S)).
Proof.
    intros S p porf Hst Hinp.
    destruct (classic (forall d, E d p -> In d (F S))) as [HallF | Hnot].
        - left. split; assumption.
        - apply not_all_ex_not in Hnot.
          destruct Hnot as [d Hd].
          apply notImplies in Hd.
          destruct Hd as [Hedge Hnotf].
          assert (In d allTasks) as Hdall.
            + apply E_closed with (t := p).
                * assumption.
                * apply Hst. right. right. left. assumption.
            + destruct (porf d Hdall) as [HdF | HdP].
                * contradiction.
                * right. exists d. split; assumption.
Qed.

Lemma allOutgoingEdgeContra :
    forall S,
        P S <> [] ->
        (forall x, In x (P S) -> exists d, E d x /\ In d (P S)) ->
        False.
Proof.
    give_up.
Admitted.

Lemma findEnabled:
    forall S, wfState S -> R S = [] -> D S = [] -> ~finished S -> exists p, enabled S p.
Proof.
    intros S [Hmax [Hcov [Hdis Hst]]] noR noD noFinish.
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
            + pose proof (mkPorf S Hcov noR noD) as porf.
              assert (Hforall : forall x, In x (P S) -> enabled S x \/ exists d, E d x /\ In d (P S)).
                {intros x Hx. apply checkEnabled; assumption. }
              assert (HforallFlip : forall x, In x (P S) -> (exists d, E d x /\ In d (P S)) \/ enabled S x).
                {intros x Hx. specialize (Hforall x Hx). destruct Hforall as [Hen | Hdep].
                 - right. exact Hen.
                 - left. exact Hdep.
                }
              destruct (allPorSomeQ Task (P S) _ _ HforallFlip) as [HallDeps | [c [HcP Hen]]].
                * exfalso. rewrite <- NP in pne. apply (allOutgoingEdgeContra S pne HallDeps).
                * exists c. exact Hen.
Qed.


Theorem progress:
    forall S, wfState S -> ~finished S -> exists S', step S S'.
Proof.
    intros S fstWf Hnf.
    pose proof fstWf as fstWf'.
    destruct fstWf' as [fstOR [fstCvr fstDj]].
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
                * destruct (findEnabled S fstWf HR HD Hnf) as [p Hen].
                  exists {|F := F S; R := p :: (R S); P := remove Nat.eq_dec p (P S); D := (D S)|}.
                    -- apply enqueue. exact Hen.
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
Qed.



End Scheduler.