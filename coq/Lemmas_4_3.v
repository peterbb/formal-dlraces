Require Import Program.
Require Import TypeSpec TypeAlgo.

Require Import Lemmas_subtype Lemmas_abstrstate_order.


Lemma lemma_4_3_1_a:
    forall AT1 AT2 C,
        stategeneration AT1 AT2 C ->
        subtype C AT1 AT2.
Proof.
    Local Hint Constructors subtype.
    intros AT1 AT2 C H;
    dependent induction H; auto;
    apply S_Arrow; auto with strengthen;
    solve_abstrstate_order.
Qed.

Lemma lemma_4_3_1_b:
    forall C D D',
        constraintgeneration D D' C ->
        abstrstate_order C D D'.
Proof.
    intros C D D' H; induction H; solve_abstrstate_order.
Qed.
