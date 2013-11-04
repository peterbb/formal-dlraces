Require Import List.
Require Import TypeSpec.


Lemma abstrstate_order_constraint_commute:
    forall C1 C2 D D',
        abstrstate_order (C1 ++ C2) D D' <->
        abstrstate_order (C2 ++ C1) D D'.
Proof.
Admitted.
    

Lemma abstrstate_order_weaken_l:
    forall C D D',
        abstrstate_order C D D' ->
        forall C', abstrstate_order (C ++ C') D D'.
Proof.
    (* Cut off. *)
Admitted.


Lemma abstrstate_order_weaken_r:
    forall C D D',
        abstrstate_order C D D' ->
        forall C', abstrstate_order (C' ++ C) D D'.
Proof.
    (* Cut off. *)
Admitted.

Hint Resolve abstrstate_order_weaken_r : strengthen.
Hint Resolve abstrstate_order_weaken_l : strengthen.

Lemma abstrstate_order_weaken_nil:
    forall D D',
        abstrstate_order nil D D' ->
        forall C, abstrstate_order C D D'.
Proof.
    intros; 
    change (abstrstate_order (nil ++ C) D D');
    auto with strengthen.
Qed.

Hint Resolve abstrstate_order_weaken_nil : strengthen.
Import ListNotations.


Ltac solve_abstrstate_order :=
    match goal with
    | |- abstrstate_order [c_LockEnv ?X ?Y] ?X ?Y =>
            exact (SO_Ax X Y)
    | |- abstrstate_order (?X ++ ?Y) _ _ =>
            (apply abstrstate_order_weaken_l; solve_abstrstate_order) ||
            (apply abstrstate_order_weaken_r; solve_abstrstate_order)
    end.

Lemma abstrstate_order_trans:
    forall C D D',
        abstrstate_order C D D' ->
        forall D'',
        abstrstate_order C D' D'' ->
        abstrstate_order C D D''.
Proof.
    (* Cut off *)
Admitted.
