
Require Import Setoid.
Require Import Program.Tactics.
Require Import Program.Equality.

Require Import Syntax TypeSyntax Constraint TypeSpec.
Require Import Lemmas_constraints.
Require Import Lemmas_abstrstate_order.
Require Import Lemmas_subtype.

Local Hint Constructors welltyped_spec subtype abstrstate_order.


Lemma spec_constraint_id_r:
    forall C G t SC E,
        welltyped_spec (C ++ nil) G t SC E
        <->
        welltyped_spec C G t SC E.
Proof.
    intro C; rewrite <- app_nil_end; reflexivity.
Qed.


Lemma spec_constraint_ass:
    forall C1 C2 C3 G t SC E,
        welltyped_spec (C1 ++ (C2 ++ C3)) G t SC E 
        <->
        welltyped_spec ((C1 ++ C2) ++ C3) G t SC E.
Proof.
    intros; rewrite app_assoc; reflexivity.
Qed.

Lemma spec_constraint_sym:
    forall C1 C2 G t SC E,
        welltyped_spec (C1 ++ C2) G t SC E 
        <->
        welltyped_spec (C2 ++ C1) G t SC E.
Proof.
(*
    intros ? ? ? ? ? ? H;
    dependent induction H; 
    try rewrite denote_constraint_commute in *;
    eauto with strengthen.
    *)
Admitted.


Lemma spec_strength_r:
    forall C G t SC phi,
        welltyped_spec C G t SC phi ->
        forall C', welltyped_spec (C ++ C') G t SC phi.
Proof.
    intros; dependent induction H; eauto with strengthen.
    - admit. (* T_Gen -- need alpha conversion. *)
Qed.

Lemma spec_strength_l:
    forall C C' G t SC phi,
        welltyped_spec C' G t SC phi ->
        welltyped_spec (C ++ C') G t SC phi.
Proof.
    intros;
    apply spec_constraint_sym;
    apply spec_strength_r;
    assumption.
Qed.


Hint Resolve spec_strength_l : strengthen.
Hint Resolve spec_strength_r : strengthen.

Ltac eval_empty_constraint :=
    (match goal with
    | H : context[ denote_constraints nil ] |- _ =>
        rewrite denote_constraint_nil in H
    | _  => idtac
    end).

Lemma spec_strength_nil:
    forall G t SC phi,
        welltyped_spec nil G t SC phi ->
        forall C,
            welltyped_spec C G t SC phi.
Proof.
    intros G t SC phi H; dependent induction H;
        eval_empty_constraint; intros; eauto.

    - apply T_Gen; auto with strengthen.
    - apply T_Unlock; auto with strengthen.
    - admit. (* Need T_Gen. alphaconversion. *)
    - eapply T_Sub; auto with strengthen.
Qed.

Hint Resolve spec_strength_nil : strengthen.

Lemma com2: forall C1 C2 C3 G t SC E,
    welltyped_spec (C1 ++ C2 ++ C3) G t SC E <->
    welltyped_spec (C1 ++ C3 ++ C2) G t SC E.
Proof.
    intros; split; intro H.
Admitted.


Lemma spec_constraint_lemma_1:
    forall C1 C2 C3 G t SC E,
        welltyped_spec ((C1 ++ C2) ++ C3) G t SC E
        <->
        welltyped_spec ((C1 ++ C3) ++ C2) G t SC E.
Proof.
    Hint Rewrite spec_constraint_ass.
    Hint Rewrite spec_constraint_sym.
    intros C1 C2 C3 G t SC E.
    rewrite app_assoc_reverse, com2, app_assoc.
    reflexivity.
Qed.
