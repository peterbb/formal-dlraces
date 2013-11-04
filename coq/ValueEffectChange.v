

(* Claim: *)
Require Import Syntax.
Require Import TypeSyntax.
Require Import TypeSpec.

Section Test.
    Variables f x z : variable.
    Variables rho rho' : ls_var.
    Variable X : le_var.

    Variable H_rhos_diff : rho <> rho'.
    Variable H_f_x_diff : f <> x.
    Variable H_f_z_diff : f <> z.
    Variable H_x_z_diff : x <> z.

    Hint Constructors abstrstate_order.

    Definition typeToScheme (a : annotatedtype) : scheme := sc_Quant nil nil c_Empty a.
    Coercion typeToScheme : annotatedtype >-> scheme.

    Definition le_singelton rho n := le_Append le_Empty (ls_Var rho) (Zinf_Z n).

    Definition C := c_LockEnv (le_singelton rho 1) (le_Var X).
    Definition Gamma := G_Empty.
    Definition AT_lock := (at_Lock (ls_Var rho)).

    Definition AT_arrow := at_Arrow AT_lock (EffectIntro le_Empty (le_Var X)) AT_lock.
    Definition ST_arrow := st_Arrow st_Lock st_Lock.

    Definition body := t_Let z st_Lock (e_AcqLock (v_VarRef x))
                        (t_Value (v_VarRef z)).
    Definition expr := e_Thread (t_Value (v_RecFun f ST_arrow x st_Lock body)).

    Definition eff_working := EffectIntro le_Empty le_Empty.

    Lemma Working:
        welltyped_spec C Gamma expr AT_arrow eff_working.
    Proof.
        apply T_Abs2 with (phi := eff_working); auto.
        apply T_Let with (SC_1 := AT_lock) (D_2 := le_Var X); auto.
        - apply T_Lock.
            * apply T_Var, CL_found.
            * 
                
        







