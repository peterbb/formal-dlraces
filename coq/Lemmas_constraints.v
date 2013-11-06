
Require Import List.
Require Import TypeSyntax.
Require Import Constraint.
Require Import MSetPositive.

Lemma denote_constraint_nil:
    denote_constraints nil <-> True.
Proof.
    split; auto; intro H; clear H.
    intros rho_den X_den.
    rewrite Forall_forall.
    intros x H; inversion H.
Qed.


Lemma denote_constraint_id_l:
    forall C,
        denote_constraints C <-> denote_constraints (nil ++ C).
Proof.  tauto.  Qed.


Lemma denote_constraint_id_r:
    forall C,
        denote_constraints C 
        <->
        denote_constraints (C  ++ nil).
Proof.
    intro C; rewrite <- app_nil_end; tauto.
Qed.


Ltac solve_constr_weak :=
    unfold denote_constraints;
    intros C C' H rho_den X_den;
    specialize (H rho_den X_den);
    rewrite Forall_forall in *;
    intuition.

Lemma denote_constraint_weak_l:
    forall C C',
        denote_constraints (C ++ C') ->
        denote_constraints C.
Proof. solve_constr_weak.  Qed.

Lemma denote_constraint_weak_r:
    forall C C',
        denote_constraints (C ++ C') ->
        denote_constraints C'.
Proof. solve_constr_weak. Qed.


Hint Resolve denote_constraint_weak_l : strengthen.
Hint Resolve denote_constraint_weak_r : strengthen.


Lemma denote_constraint_commute:
    forall C1 C2,
        denote_constraints (C1 ++ C2) <->
        denote_constraints (C2 ++ C1).
Proof.
    unfold denote_constraints.
    intros C1 C2; split; intros H rho_den X_den;
    specialize (H rho_den X_den);
    rewrite Forall_forall in *;
    intro x; specialize (H x);
    rewrite in_app_iff in *;
    tauto.
Qed.
Hint Rewrite denote_constraint_commute.

Lemma constraints_join:
    forall C C',
        denote_constraints C ->
        denote_constraints C' ->
        denote_constraints (C ++ C').
Proof.
    unfold denote_constraints.
    intros C C' H1 H2 rho_den X_den.
    specialize (H1 rho_den X_den).
    specialize (H2 rho_den X_den).
    rewrite Forall_forall in *.
    intros x; specialize (H1 x); specialize (H2 x).
    rewrite in_app_iff; tauto.
Qed.

Lemma lemma_4_7:
    forall C C1 C2,
        (denote_constraints C -> denote_constraints C1) ->
        (denote_constraints C -> denote_constraints C2) ->
        (denote_constraints C -> denote_constraints (C1 ++ C2)).
Proof.
    Local Hint Resolve constraints_join.
    auto.
Qed.

