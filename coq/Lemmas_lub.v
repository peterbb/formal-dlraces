Require Import Program.

Require Import TypeSpec TypeAlgo.

Require Import Lemmas_subtype.
Require Import Lemmas_constraints.
Require Import Lemmas_abstrstate_order.


Hint Constructors subtype leastupperboundAT.

Ltac solve_subtype :=
    match goal with
    | |- subtype [c_LockSet ?X ?Y] (at_Lock ?X) (at_Lock ?Y) => 
            apply S_Refl
    | |- subtype (?X ++ ?Y) _ _ =>
        (apply subtype_weaken_l; solve_subtype) ||
        (apply subtype_weaken_r; solve_subtype)
    end.    

Lemma lub_then_subtype_l:
    forall AT AT1 AT2 C,
        leastupperboundAT AT1 AT2 AT C ->
        subtype C AT1 AT.
Proof.
    intros AT AT1 AT2 C H;
    dependent induction H; auto with strengthen.
    do 2 (match goal with
            | H : stategeneration _ _ _ |- _ => inversion H; clear H
          end); subst *.
    - apply S_Lock; eauto with strengthen.
    - destruct phi; destruct phi1; apply S_Arrow.
      * admit. (* Seems like the definition in the paper is wrong. *)
      * admit.
      * inversion H1; apply SO_Refl.
      * inversion H1; apply SO_Refl.
Qed.

Lemma lub_then_subtype_r:
    forall AT AT1 AT2 C,
        leastupperboundAT AT1 AT2 AT C ->
        subtype C AT2 AT.
Proof.
Admitted.

Hint Constructors abstrstate_order.

Lemma lub_then_abstrorder_l:
    forall D1 D2 D C,
        leastupperboundD D1 D2 D C ->
        abstrstate_order C D1 D.
Proof.
    intros ? ? ? ? H; induction H; induction H.
    eauto with strengthen.
Qed.
Lemma lub_then_abstrorder_r:
    forall D1 D2 D C,
        leastupperboundD D1 D2 D C ->
        abstrstate_order C D2 D.
Proof.
    intros ? ? ? ? H; induction H; induction H0;
    eauto with strengthen.
Qed.

Hint Resolve lub_then_subtype_l : lub.
Hint Resolve lub_then_subtype_r : lub.
Hint Resolve lub_then_abstrorder_l : lub.
Hint Resolve lub_then_abstrorder_r : lub.
