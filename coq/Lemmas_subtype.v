Require Import PArith.
Require Import List.

Require Import Program.

Require Import Constraint TypeAlgo TypeSpec Lemmas_constraints.
Require Import Lemmas_abstrstate_order.



Ltac solve_subtype_weaken' H :=
    dependent induction H;
    intro C';
    [ eapply S_Refl 
    | eapply S_Trans
    | eapply S_Lock
    | apply S_Arrow
    ]; eauto with strengthen.

Ltac solve_subtype_weaken :=
    let H := fresh "H" in 
    intros C AT AT' H;
    solve_subtype_weaken' H.

Lemma subtype_weaken_l:
    forall C AT AT',
        subtype C AT AT' ->
        forall C', subtype (C ++ C') AT AT'.
Proof. solve_subtype_weaken.  Qed.

Hint Resolve subtype_weaken_l : strengthen.

Lemma subtype_weaken_r:
    forall C' AT AT',
        subtype C' AT AT' ->
        forall C, subtype (C ++ C') AT AT'.
Proof. solve_subtype_weaken. Qed.

Hint Resolve subtype_weaken_r : strengthen.

Lemma subtype_weaken_nil:
    forall AT AT',
        subtype nil AT AT' ->
        forall C, subtype C AT AT'.
Proof.
    intros AT AT' H; 
    dependent induction H;
    intro C';
    [ eapply S_Refl 
    | eapply S_Trans
    | eapply S_Lock
    | apply S_Arrow
    ]; eauto with strengthen.
Qed.
Hint Resolve subtype_weaken_nil : strengthen.

Lemma subset_subtype:
    forall C r1 r2,
    (denote_constraints C -> denote_constraints [c_LockSet r1 r2]) ->
    forall G t E,
    welltyped_spec C G t (at_Lock r1) E ->
    welltyped_spec C G t (at_Lock r2) E.
Proof.
    intros C r1 r2 H G t E H'.
    dependent induction H'; eauto with strengthen.
Admitted.

Lemma spec_subtype:
    forall AT AT' C,
        subtype C AT AT' ->
    forall G t E,
        welltyped_spec C G t AT  E ->
        welltyped_spec C G t AT' E.
Proof.
Admitted.

Lemma subtype_trans:
    forall C AT AT',
        subtype C AT AT' ->
        forall AT'', subtype C AT' AT'' ->
                     subtype C AT AT''.
Proof.
Admitted.
