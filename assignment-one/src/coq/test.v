Require Import Stdlib.Lists.List. 
Import ListNotations.

Lemma test : 1 + 1 = 2.
Proof.
    reflexivity.
Qed.
Print test.

Definition Task : Type := nat.

Definition Subset (xs ys : list Task) : Prop := Forall (fun x => In x ys) xs.

Inductive DAG : list Task -> Type :=
    | EmptyGraph : DAG []
    | AddSource : forall (t : Task) (deps : list Task) (rest : list Task),
        Subset deps rest -> DAG rest -> DAG (t::rest).

Record Scheduler : Type := MkScheduler {
    pending : list Task;
    ready : list Task;
    running : option Task;
    finished : list Task;
}.