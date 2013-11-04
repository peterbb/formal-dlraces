

Require Import TypeSyntax.

Lemma lift_down_arrow_left: 
    forall ST1 ST2 AT1 AT2 max_rho max_X max_rho' max_X' phi, 
        lift_A (st_Arrow ST1 ST2) max_rho max_X = 
        (at_Arrow AT1 phi AT2, max_rho', max_X') -> 
            downAT AT1 = ST1. 
Proof. 
    intros. 
    injection H. intros; rewrite <- H4; apply downAT_lift_A_is_id. 
Qed. 


Lemma lift_down_arrow_right:
    forall ST1 ST2 AT1 AT2 max_rho max_X max_rho' max_X' phi,
        lift_A (st_Arrow ST1 ST2) max_rho max_X =
        (at_Arrow AT1 phi AT2, max_rho', max_X') ->
            downAT AT2 = ST2.
Proof.
    intros; injection H; intros; subst *;
    rewrite <- downAT_lift_A_is_id with
        (max1:=(snd (fst (lift_A ST1 max_rho max_X))))
        (max2:=(snd (lift_A ST1 max_rho max_X)));
    reflexivity.
Qed.


