Require Import Arith.
Require Import Bool.
Require Import List.
Require Export ZArith.

Require Export Syntax.
Require Export TypeSyntax.
Require Import Substitution.
Require Import FreeVar.
Require Import Constraint.

Inductive abstrstate_order : constraints -> lockenv -> lockenv -> Prop :=
 | SO_Refl : forall (C:constraints) (D:lockenv),
     abstrstate_order C D D
 | SO_Trans : forall (C:constraints) (D1 D3 D2:lockenv),
     abstrstate_order C D1 D2 ->
     abstrstate_order C D2 D3 ->
     abstrstate_order C D1 D3
 | SO_Ax : forall (D D':lockenv),
     abstrstate_order  (cons (c_LockEnv D D') nil) D D'
 | SO_Base : forall (C:constraints) (D1 D2:lockenv),
     pointwise_leq D1 D2 ->
     abstrstate_order C D1 D2
 | SO_Plus1 : forall (C:constraints) (D2 D1:lockenv),
     abstrstate_order C le_Empty D1 ->
     abstrstate_order C D2 (le_Add D2 D1)
 | SO_Plus2 : forall (C:constraints) (D2 D1:lockenv),
     abstrstate_order C D1 le_Empty ->
     abstrstate_order C (le_Add D2 D1) D2
 | SO_Minus1 : forall (C:constraints) (D2 D1:lockenv),
     abstrstate_order C le_Empty D1 ->
     abstrstate_order C (le_Sub D2 D1) D2
 | SO_Minus2 : forall (C:constraints) (D2 D1:lockenv),
     abstrstate_order C D1 le_Empty ->
     abstrstate_order C D2 (le_Sub D2 D1).


Inductive subtype (C : constraints) : annotatedtype -> annotatedtype -> Prop :=
 | S_Refl : forall (AT:annotatedtype),
     subtype C AT AT
 | S_Trans : forall (AT1 AT3 AT2:annotatedtype),
     subtype C AT1 AT2 ->
     subtype C AT2 AT3 ->
     subtype C AT1 AT3
 | S_Lock : forall (r1 r2:lockset),
     (denote_constraints C -> 
        denote_constraints (cons (c_LockSet r1 r2) nil)) ->
     subtype C (at_Lock r1) (at_Lock r2)
 | S_Arrow : forall (AT1 AT2 AT1' AT2' :annotatedtype) (D1 D2 D1' D2' :lockenv),
     subtype C AT1' AT1 ->
     subtype C AT2 AT2' ->
     abstrstate_order C D1' D1 ->
     abstrstate_order C D2 D2' ->
     subtype C (at_Arrow AT1 (EffectIntro D1 D2) AT2) (at_Arrow AT1' (EffectIntro D1' D2') AT2').

Inductive welltyped_spec : constraints -> context -> expr -> scheme -> effect -> Prop :=
 | T_Var : forall C G x SC D,
     ContextLookup G x SC ->
     welltyped_spec C G (v_VarRef x) SC (EffectIntro D D)

 | T_NewL : forall C G pi rho D,
     (denote_constraints C -> denote_constraints (cons (c_LockSet (ls_Single pi) (ls_Var rho)) nil)) ->
     welltyped_spec C G (e_NewL pi)  (at_Lock (ls_Var rho)) (EffectIntro D D)

 | T_LRef : forall C G l rho rho' D,
     (denote_constraints C -> denote_constraints (cons (c_LockSet  (ls_Var rho) (ls_Var rho'))  nil)) ->
     welltyped_spec C G (v_LockRef l (ls_Var rho)) (at_Lock (ls_Var rho'))  (EffectIntro D D)

 | T_Abs1 : forall C G (x : variable) ST1 (t : thread) (AT1 AT2 : annotatedtype) phi D,
     downAT AT1 = ST1 ->
     welltyped_spec C ((x, AT_to_scheme AT1) :: G) t  AT2  phi ->
     welltyped_spec C G (v_Fun x ST1 t)  (at_Arrow AT1 phi AT2) (EffectIntro D D)

 | T_Abs2 : forall C G (f x : variable) (ST1 ST2:simpletype) (AT1 AT2 : annotatedtype) (t:thread) (D1 D2:lockenv) (phi:effect),
     downAT AT1 = ST1 ->
     downAT AT2 = ST2 ->
     welltyped_spec C ((f, AT_to_scheme (at_Arrow AT1 phi AT2)) :: (x, AT_to_scheme AT1) :: G) t AT2 (EffectIntro D1 D2) ->
     welltyped_spec C G (v_RecFun f (st_Arrow ST1 ST2) x ST1 t) (at_Arrow AT1 (EffectIntro D1 D2) AT2)  (EffectIntro D1 D1)

 | T_App : forall C G (v1 v2:value) (AT1:annotatedtype) (D1 D2:lockenv) (AT2:annotatedtype),
     welltyped_spec C G v1 (at_Arrow AT2 (EffectIntro D1 D2) AT1) (EffectIntro D1 D1) ->
     welltyped_spec C G v2 AT2                                    (EffectIntro D1 D1) ->
     welltyped_spec C G (e_App v1 v2) AT1                         (EffectIntro D1 D2)

 | T_Cond : forall C G (v:value) (e1 e2:expr) (AT:annotatedtype) (D1 D2:lockenv),
     welltyped_spec C G v at_Bool (EffectIntro D1 D1) ->
     welltyped_spec C G e1 AT (EffectIntro D1 D2) ->
     welltyped_spec C G e2 AT (EffectIntro D1 D2) ->
     welltyped_spec C G (e_Cond v e1 e2) AT (EffectIntro D1 D2)

 | T_Let : forall C G x (e : expr) (t : thread) ST AT SC D1 D2 D3,
     welltyped_spec C G e SC (EffectIntro D1 D2) ->
     downSC SC = ST ->
     welltyped_spec C ((x, SC) :: G) t AT (EffectIntro D2 D3) ->
     welltyped_spec C G (t_Let x ST e t) AT (EffectIntro D1 D3)

 | T_Spawn : forall C G (t:thread) (D1:lockenv) (AT:annotatedtype) (D2:lockenv),
     welltyped_spec C G t AT (EffectIntro le_Empty D2) ->
     welltyped_spec C G (e_Spawn t) at_Thread (EffectIntro D1 D1)

 | T_Lock : forall C G (v:value) (rho:ls_var) (D1 D2:lockenv),
     welltyped_spec C G v  (at_Lock (ls_Var rho))  (EffectIntro D1 D1) ->
     abstrstate_order C (le_Add D1 (le_Append le_Empty  (ls_Var rho)  (Zinf_Z 1)) ) D2 ->
     welltyped_spec C G (e_AcqLock v)  (at_Lock (ls_Var rho)) (EffectIntro D1 D2)

 | T_Unlock : forall C G (v:value) (rho:ls_var) (D1 D2:lockenv),
     welltyped_spec C G v (at_Lock (ls_Var rho))  (EffectIntro D1 D1) ->
     abstrstate_order C (le_Sub D1 (le_Append le_Empty (ls_Var rho)  (Zinf_Z 1)) ) D2 ->
     welltyped_spec C G (e_RelLock v)  (at_Lock (ls_Var rho)) (EffectIntro D1 D2)

 | T_Gen : forall G (X_list:list le_var) (rho_list:list ls_var) (C1:constraints) (e:expr) (C2:constraints) (AT:annotatedtype) (D1 D2:lockenv),
     welltyped_spec ( C1 ++ C2 ) G e  AT (EffectIntro D1 D2) ->
     (Forall (fun x => ~PositiveSet.In x (free_ls_G G)) rho_list) ->
     (Forall (fun x => ~PositiveSet.In x (free_le_G G)) X_list) ->
     (Forall (fun x => ~PositiveSet.In x (free_ls_C C1)) rho_list) ->
     (Forall (fun x => ~PositiveSet.In x (free_le_C C1)) X_list) ->
     welltyped_spec C1 G e (sc_All rho_list X_list C2 AT) (EffectIntro D1 D2)

 | T_Inst : forall G (r_list:list lockset) (D_list:list lockenv) (X_list:list le_var) (rho_list:list ls_var) (C1:constraints) (e:expr) (th:subst) (AT:annotatedtype) (C2:constraints) (D1 D2:lockenv),
     welltyped_spec C1 G e (sc_All rho_list X_list C2 AT) (EffectIntro D1 D2) ->
     th = (create_subst D_list X_list r_list rho_list) ->
     (denote_constraints C1 -> denote_constraints (lift_subst_C th C2)) ->
     welltyped_spec C1 G e  (lift_subst_AT th AT ) (EffectIntro D1 D2)

 | T_Sub : forall C G (e:expr) (AT1:annotatedtype) (D1' D2':lockenv) (AT2:annotatedtype) (D1 D2:lockenv),
     welltyped_spec C G e AT2 (EffectIntro D1 D2) ->
     subtype C AT2 AT1 ->
     abstrstate_order C D1' D1 ->
     abstrstate_order C D2 D2' ->
     welltyped_spec C G e AT1 (EffectIntro D1' D2').



Inductive welltyped_prog_spec : program -> program_type -> Prop :=
 | T_Thread : forall (p:processid) (t:thread) (phi:effect) (C:constraints) (AT:annotatedtype),
     welltyped_spec C nil (e_Thread t)  (sc_All nil nil nil  AT )  phi ->
     welltyped_prog_spec (P_Single p t) (pt_Single p phi C)
 | T_Par : forall (P1 P2:program) (Phi1 Phi2:program_type),
     welltyped_prog_spec P1 Phi1 ->
     welltyped_prog_spec P2 Phi2 ->
     welltyped_prog_spec (P_Parallel P1 P2) (pt_Parallell Phi1 Phi2).


