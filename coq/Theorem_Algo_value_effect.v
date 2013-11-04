

Require Import TypeSyntax TypeAlgo.

Theorem alog_value_effect:
    forall v G max_rho max_X AT D C max_rho' max_X',
        welltyped_algo G max_rho max_X (e_Thread (t_Value v))  AT (EffectIntro D D) C max_rho' max_X' ->
        forall D', exists max_rho'' max_X'',
            welltyped_algo G max_rho max_X (e_Thread (t_Value v)) AT (EffectIntro D' D') C max_rho'' max_X''.
Proof.
    intros c G max_rho max_X AT D C max_rho' max_X' H; 
    induction H.
    - intro D'.



