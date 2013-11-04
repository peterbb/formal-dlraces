Require Import Syntax TypeAlgo.

Theorem algo_values_all_effect:
    forall C v T D G max_rho max_X max_rho' max_X',
        welltyped_algo G max_rho max_X (e_Thread (t_Value v)) T (EffectIntro D D) C max_rho' max_X' ->
        forall D',
        welltyped_algo G max_rho max_X (e_Thread (t_Value v)) T (EffectIntro D' D') C max_rho' max_X'.
Proof.


