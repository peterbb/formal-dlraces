Require Import Program.Tactics.
Require Import List SetoidList.

Require Import TypeSpec TypeAlgo Constraint FreeVar.

Require Import Program.Equality.
Require Import Lemmas_constraints.
Require Import Lemmas_4_3.
Require Import Lemmas_subtype.
Require Import Lemmas_lub.
Require Import Lemmas_spec.
Require Import Lemmas_abstrstate_order.

Lemma up_and_down_is_id:
    forall ST AT max1 max2 max3 max4,
        lift_A ST max1 max2 = (AT, max3, max4) ->
        downAT AT = ST.
Proof.
    Lemma downAT_lift_A_is_id:
        forall ST max1 max2,
            downAT (fst (fst (lift_A ST max1 max2))) = ST.
    Proof.
        intros ST; induction ST; auto;
        intros; simpl; f_equal; auto.
    Qed.
    intros ST AT max1 max2 max3 max4 H;
    rewrite <- downAT_lift_A_is_id with (max1 := max1) (max2 := max2);
    rewrite H; trivial.
Qed.
Hint Resolve up_and_down_is_id.

Hint Constructors welltyped_spec.
Hint Constructors subtype.
Hint Constructors abstrstate_order.


Lemma InDiffNot: forall x X Y,
    PS.In x (PS.diff X Y) -> ~ PS.In x Y.
Proof.
    intros x X Y H; rewrite PS.diff_spec in H; tauto.
Qed.

Ltac solve_freevars := 
    let ph := fresh "x" in
    let H := fresh "H" in
    let H' := fresh "H" in
    rewrite Forall_forall; intro ph;
    unfold FreeVar.sc_close_find_vars;
    intro H;
    (match goal with
     | H' : In ?x (PS.elements ?X) |- _  =>
        cut (PS.In x X)
     end);
     [ apply InDiffNot
     | rewrite <- PS.elements_spec1 
     ; apply In_InA; [ exact eq_equivalence | assumption ]
     ].


Lemma Lemma_4_4_Soundness:
    forall G t AT D1 D2 C max_rho max_X max_rho' max_X',
        welltyped_algo G max_rho max_X t AT (EffectIntro D1 D2) C max_rho' max_X' ->
        welltyped_spec C G t (sc_Quant nil nil nil AT) (EffectIntro D1 D2).
Proof.
    Hint Resolve subtype_weaken_l.
    Hint Resolve subtype_weaken_r.
    Hint Resolve lemma_4_3_1_b.

    intros G t AT D1 D2 C max_rho max_X max_rho' max_X' H; induction H.
    - (* TA_Var  ============================================================ *)
        eapply T_Inst; eauto.

    - (* TA_Newl  ============================================================ *)
        auto.

    - (* TA_LRef  ============================================================ *)
        auto.

    - (* TA_Abs1  ============================================================ *)
        apply T_Abs1; auto; [ | eapply T_Sub]; eauto with strengthen.

    - (* TA_Abs2  ============================================================ *)
        admit. (* Not correct. *)

    - (* TA_App  ============================================================ *)
        apply T_App with (AT_2:=AT_2).
        * apply T_Sub with (AT_2:= at_Arrow AT_2 (EffectIntro D_1 D_2) AT_1)
                           (D_1:=D)(D_2:=D);
            auto with strengthen.                    
        * apply T_Sub with (AT_2:= AT_2)
                           (D_1:=D)(D_2:=D); auto.
          apply spec_subtype with (AT:=AT'_2);
          auto using lemma_4_3_1_a with strengthen.

    - (* TA_Cond ============================================================ *)
        apply T_Cond; auto with strengthen;
        [ apply T_Sub with (AT_2:=AT_1) (D_1:=D0) (D_2:=D3)
        | apply T_Sub with (AT_2:=AT_2) (D_1:=D0) (D_2:=D4)
        ];  eauto with strengthen lub.

    - (* TA_Let ============================================================ *)
        apply T_Let with (SC_1:=SC1)(D_2:=D4); subst *; auto.
        cut (welltyped_spec nil G e1 (sc_close G C1 AT1) (EffectIntro D0 D4));
        auto with strengthen.
        apply T_Gen; auto with strengthen;
        try solve_freevars;
        rewrite Forall_forall; intros x0 H''; change (~ PositiveSet.In x0 PS.empty);
        destruct x0; compute; discriminate.

    - (* TA_Spawn ============================================================ *)
        eapply T_Spawn; eauto.

    - (* TA_Lock ============================================================ *)
        apply T_Lock; auto with strengthen.

    - (* TA_Unlock ============================================================ *)
        apply T_Unlock; auto with strengthen.
Qed.
