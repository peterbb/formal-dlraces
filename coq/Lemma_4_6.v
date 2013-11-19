Require Import Program.Tactics.
Require Import Program.

Require Import TypeSyntax TypeSpec.

Require Import Lemmas_subtype Lemmas_abstrstate_order.


Section LEMMA_4_6.
    Variable C : constraints.
    Variables T T1 T2 : annotatedtype.
    Variables D1 D2 : lockenv.


    Lemma Lemma_4_6:  
        subtype C T (at_Arrow T1 (EffectIntro D1 D2) T2) ->
    
        exists T1' T2' D1' D2',
            T = (at_Arrow T1' (EffectIntro D1' D2') T2') /\
            subtype C T1 T1' /\
            subtype C T2' T2 /\
            abstrstate_order C D1 D1' /\
            abstrstate_order C D2' D2.

    Proof.
        Local Hint Constructors subtype abstrstate_order.
        intro H; dependent induction H.
        - do 4 eexists; eauto.
        - destruct IHsubtype2 as [T1' [T2' [D1' [D2' IH2]]]].
          specialize (IHsubtype1 T1' T2' D1' D2' (proj1 IH2)).
          destruct IHsubtype1 as [T1'' [T2'' [D1'' [D2'' IH1]]]].
          exists T1'' T2'' D1'' D2''; 
            intuition; eauto using subtype_trans, abstrstate_order_trans.
        - exists AT_1 AT_2 D_1 D_2; intuition.
    Qed.

End LEMMA_4_6.
