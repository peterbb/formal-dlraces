(* generated by Ott 0.21.2 from: ott/Syntax.ott ott/Common.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import ott_list_core.


Require Import Arith.Min.
Require Import Arith.Max.

Require Export Syntax.
Require Export TypeSyntax.
Require Import Substitution.
Require Import FreeVar.


Open Scope positive.
Section LiftA.
    Fixpoint lift_A (ST : simpletype) (max_rho : ls_var) (max_X : le_var) : annotatedtype * ls_var * le_var :=
        match ST with
        | st_Bool => (at_Bool, max_rho, max_X)
        | st_Thread => (at_Thread, max_rho, max_X)
        | st_Lock => (at_Lock (ls_Var (max_rho + 1)%positive), max_rho + 2, max_X)
        | st_Arrow ST1 ST2 =>

            let res1 := lift_A ST1 max_rho max_X in
            let AT1 := fst (fst res1) in
            let max_rho' := snd (fst res1) in
            let max_X' := snd res1 in

            let res2 := lift_A ST2 max_rho' max_X' in
            let AT2 := fst (fst res2) in
            let max_rho'' := snd (fst res2) in
            let max_X'' := snd res2 in

            let phi := EffectIntro (le_Var (Pplus max_X'' 1)) (le_Var (Pplus max_X'' 2))
            in
                (at_Arrow AT1 phi AT2, max_rho'', Pplus max_X'' 3)
        end.

End LiftA.

Section UniqueList.
    Variable T : Type.
    Variable T_eq : forall (x y : T), {x=y}+{x<>y}.
    Variable lst : list T.

    Definition unique_element x := (count_occ T_eq lst x) = 0%nat.

    Definition unique := Forall unique_element lst.
End UniqueList.
        

(** definitions *)

(* defns ConstraintGeneration *)
Inductive stategeneration : annotatedtype -> annotatedtype -> constraints -> Prop :=    (* defn stategeneration *)
 | C_Basic1 : 
     stategeneration at_Bool at_Bool  (@nil ineq) 
 | C_Basic2 : 
     stategeneration at_Thread at_Thread  (@nil ineq) 
 | C_Lock : forall (rho1 rho2:ls_var),
     stategeneration (at_Lock (ls_Var rho1)) (at_Lock (ls_Var rho2))  (cons  (c_LockSet (ls_Var rho1) (ls_Var rho2))  nil) 
 | C_Arrow : forall (AT_1:annotatedtype) (X_1 X_2:le_var) (AT_2 AT'_1:annotatedtype) (X'_1 X'_2:le_var) (AT'_2:annotatedtype) (C_1 C_2:constraints),
     stategeneration AT'_1 AT_1 C_1 ->
     stategeneration AT_2 AT'_2 C_2 ->
     stategeneration (at_Arrow AT_1 (EffectIntro (le_Var X_1) (le_Var X_2)) AT_2) (at_Arrow AT'_1 (EffectIntro (le_Var X'_1) (le_Var X'_2)) AT'_2)  (  (  ( C_1  ++  C_2 )   ++   (cons  (c_LockEnv (le_Var X'_1) (le_Var X_1))  nil)  )   ++   (cons  (c_LockEnv (le_Var X_2) (le_Var X'_2))  nil)  ) 
with constraintgeneration : lockenv -> lockenv -> constraints -> Prop :=    (* defn constraintgeneration *)
 | C_Id : forall (D D':lockenv),
     constraintgeneration D D'  (cons  (c_LockEnv D D')  nil) .
(** definitions *)

(* defns LeastUpperBound *)
Inductive leastupperboundAT : annotatedtype -> annotatedtype -> annotatedtype -> constraints -> Prop :=    (* defn leastupperboundAT *)
 | LT_Bool : 
     leastupperboundAT at_Bool at_Bool at_Bool  (@nil ineq) 
 | LT_Thread : 
     leastupperboundAT at_Thread at_Thread at_Thread  (@nil ineq) 
 | LT_Lock : forall (rho1 rho2 rho:ls_var) (C_1 C_2:constraints),
       ( rho  <>  rho1 )   ->
       ( rho  <>  rho2 )   ->
     stategeneration (at_Lock (ls_Var rho1)) (at_Lock (ls_Var rho)) C_1 ->
     stategeneration (at_Lock (ls_Var rho2)) (at_Lock (ls_Var rho)) C_2 ->
     leastupperboundAT (at_Lock (ls_Var rho1)) (at_Lock (ls_Var rho2)) (at_Lock (ls_Var rho))  ( C_1  ++  C_2 ) 
 | LT_Arrow : forall (AT1':annotatedtype) (phi1:effect) (AT2' AT1'':annotatedtype) (phi2:effect) (AT2'' AT1:annotatedtype) (phi:effect) (AT2:annotatedtype) (C1 C2 C3:constraints) (AT AT':annotatedtype),
     greatestlowerboundAT AT1' AT1'' AT C1 ->
     leastupperboundAT AT2' AT2'' AT' C2 ->
     leastupperboundE phi1 phi2 phi C3 ->
     leastupperboundAT (at_Arrow AT1' phi1 AT2') (at_Arrow AT1'' phi2 AT2'') (at_Arrow AT1 phi AT2)  (  ( C1  ++  C2 )   ++  C3 ) 
with greatestlowerboundAT : annotatedtype -> annotatedtype -> annotatedtype -> constraints -> Prop :=    (* defn greatestlowerboundAT *)
 | GT_Bool : 
     greatestlowerboundAT at_Bool at_Bool at_Bool  (@nil ineq) 
 | GT_Thread : 
     greatestlowerboundAT at_Thread at_Thread at_Thread  (@nil ineq) 
 | GT_Lock : forall (rho1 rho2 rho:ls_var) (C_1 C_2:constraints),
       ( rho  <>  rho1 )   ->
       ( rho  <>  rho2 )   ->
     stategeneration (at_Lock (ls_Var rho)) (at_Lock (ls_Var rho1)) C_1 ->
     stategeneration (at_Lock (ls_Var rho)) (at_Lock (ls_Var rho2)) C_2 ->
     greatestlowerboundAT (at_Lock (ls_Var rho1)) (at_Lock (ls_Var rho2)) (at_Lock (ls_Var rho))  ( C_1  ++  C_2 ) 
 | GT_Arrow : forall (AT1':annotatedtype) (phi1:effect) (AT2' AT1'':annotatedtype) (phi2:effect) (AT2'' AT1:annotatedtype) (phi:effect) (AT2:annotatedtype) (C1 C2 C3:constraints) (AT AT':annotatedtype),
     leastupperboundAT AT1' AT1'' AT C1 ->
     greatestlowerboundAT AT2' AT2'' AT' C2 ->
     greaterlowerboundE phi1 phi2 phi C3 ->
     greatestlowerboundAT  (at_Arrow AT1' phi1 AT2')   (at_Arrow AT1'' phi2 AT2'')   (at_Arrow AT1 phi AT2)   (  ( C1  ++  C2 )   ++  C3 ) 
with leastupperboundD : lockenv -> lockenv -> lockenv -> constraints -> Prop :=    (* defn leastupperboundD *)
 | LE_States : forall (D_1 D_2:lockenv) (X:le_var) (C1 C2:constraints),
     constraintgeneration D_1 (le_Var X) C1 ->
     constraintgeneration D_2 (le_Var X) C2 ->
     leastupperboundD D_1 D_2 (le_Var X)  ( C1  ++  C2 ) 
with greaterlowerboundD : lockenv -> lockenv -> lockenv -> constraints -> Prop :=    (* defn greaterlowerboundD *)
 | GE_States : forall (D_1 D_2:lockenv) (X:le_var) (C1 C2:constraints),
     constraintgeneration (le_Var X) D_1 C1 ->
     constraintgeneration (le_Var X) D_2 C2 ->
     greaterlowerboundD D_1 D_2 (le_Var X)  ( C1  ++  C2 ) 
with leastupperboundE : effect -> effect -> effect -> constraints -> Prop :=    (* defn leastupperboundE *)
 | LE_Arrow : forall (D1 D2 D'1 D'2:lockenv) (C1 C2:constraints) (D''1 D''2:lockenv),
     greaterlowerboundD D'1 D''1 D1 C1 ->
     leastupperboundD D'2 D''2 D2 C2 ->
     leastupperboundE (EffectIntro D1 D2) (EffectIntro D'1 D'2) (EffectIntro D1 D2)  ( C1  ++  C2 ) 
with greaterlowerboundE : effect -> effect -> effect -> constraints -> Prop :=    (* defn greaterlowerboundE *)
 | GE_Arrow : forall (D1 D2 D'1 D'2:lockenv) (C1 C2:constraints) (D''1 D''2:lockenv),
     leastupperboundD D'1 D''1 D1 C1 ->
     greaterlowerboundD D'2 D''2 D2 C2 ->
     greaterlowerboundE (EffectIntro D1 D2) (EffectIntro D'1 D'2) (EffectIntro D1 D2)  ( C1  ++  C2 ) .
(** definitions *)

(* defns TypeAndEffectAlgo *)
Inductive welltyped_algo : context -> ls_var -> le_var -> expr -> annotatedtype -> effect -> constraints -> ls_var -> le_var -> Prop :=    (* defn welltyped_algo *)
 | TA_Var : forall (X_list:list le_var) (rho_list:list ls_var) (X'_list:list le_var) (rho'_list:list ls_var) (G:context) (max_rho:ls_var) (max_X:le_var) (x:variable) (th:subst) (AT:annotatedtype) (D:lockenv) (C:constraints),
     ContextLookup G x (sc_Quant rho_list X_list C AT) ->
       ( th  =   (create_subst  (map (fun (X'_:le_var) => (le_Var X'_)) X'_list)   X_list   (map (fun (rho'_:ls_var) => (ls_Var rho'_)) rho'_list)   rho_list )  )   ->
       (unique _ eq_ls_var  rho'_list )   ->
       (unique _ eq_le_var  X'_list )   ->
       (Forall 
                                              (fun x => ~PositiveSet.In x   (free_ls_G  G )  )
                                               rho'_list )   ->
       (Forall 
                                              (fun x => ~PositiveSet.In x   (free_ls_C  C )  )
                                               rho'_list )   ->
       (Forall 
                                              (fun x => ~PositiveSet.In x   (free_ls_D  D )  )
                                               rho'_list )   ->
       (Forall 
                                              (fun x => ~PositiveSet.In x   (free_le_G  G )  )
                                               X'_list )   ->
       (Forall 
                                              (fun x => ~PositiveSet.In x   (free_le_C  C )  )
                                               X'_list )   ->
       (Forall 
                                              (fun x => ~PositiveSet.In x   (free_le_D  D )  )
                                               X'_list )   ->
       ( max_rho  <   (fold_left Pos.min  rho'_list  1%positive)  )   ->
       ( max_X  <   (fold_left Pos.min  X'_list  1%positive)  )%positive   ->
     welltyped_algo G max_rho max_X (e_Thread (t_Value (v_VarRef x)))  (lift_subst_AT  th   AT )  (EffectIntro D D)  (lift_subst_C  th   C )   (Pos.succ   (fold_left Pos.max  rho'_list  1%positive)  )   (  (fold_left Pos.max  X'_list  1%positive)   + 1)%positive 
 | TA_NewL : forall (G:context) (max_rho:ls_var) (max_X:le_var) (pi:programpoint) (rho:ls_var) (D:lockenv) (max_rho':ls_var) (max_X':le_var),
       ( max_X  <  max_X' )%positive   ->
       ( max_rho  <  rho )   ->
       ( rho  <  max_rho' )   ->
     welltyped_algo G max_rho max_X (e_NewL pi) (at_Lock (ls_Var rho)) (EffectIntro D D)  (cons  (c_LockSet (ls_Single pi) (ls_Var rho))  nil)  max_rho' max_X'
 | TA_Lref : forall (G:context) (max_rho:ls_var) (max_X:le_var) (l:lockref) (rho rho':ls_var) (D:lockenv) (max_rho':ls_var) (max_X':le_var),
       ( max_X  <  max_X' )%positive   ->
       ( max_rho  <  rho' )   ->
       ( rho'  <  max_rho' )   ->
     welltyped_algo G max_rho max_X (e_Thread (t_Value (v_LockRef l (ls_Var rho)))) (at_Lock (ls_Var rho')) (EffectIntro D D)  (cons  (c_LockSet (ls_Var rho) (ls_Var rho'))  nil)  max_rho' max_X'
 | TA_Abs1 : forall (G:context) (max_rho:ls_var) (max_X:le_var) (x:variable) (ST1:simpletype) (t:thread) (AT1:annotatedtype) (X1 X2:le_var) (AT2:annotatedtype) (D1:lockenv) (C:constraints) (D2:lockenv) (max_rho'':ls_var) (max_X''':le_var) (max_rho':ls_var) (max_X' max_X'':le_var),
     lift_A ST1 max_rho max_X = (AT1, max_rho', max_X')  ->
     welltyped_algo (G_Extend G x  (sc_Quant nil nil nil  AT1 ) ) max_rho' max_X' (e_Thread t) AT2 (EffectIntro (le_Var X1) D2) C max_rho'' max_X'' ->
       ( max_X''  <  X1 )%positive   ->
       ( X1  <  X2 )%positive   ->
       ( X2  <  max_X''' )%positive   ->
     welltyped_algo G max_rho max_X (e_Thread (t_Value (v_Fun x ST1 t))) (at_Arrow AT1 (EffectIntro (le_Var X1) (le_Var X2)) AT2) (EffectIntro D1 D1)  ( C  ++   (cons  (c_LockEnv D2 (le_Var X2))  nil)  )  max_rho'' max_X'''
 | TA_Abs2 : forall (G:context) (max_rho:ls_var) (max_X:le_var) (f:variable) (ST1 ST2:simpletype) (x:variable) (t:thread) (AT1:annotatedtype) (X1 X2:le_var) (AT2:annotatedtype) (D1:lockenv) (C1 C2 C3:constraints) (max_rho'':ls_var) (max_X'':le_var) (max_rho':ls_var) (max_X':le_var) (AT'2:annotatedtype) (D2:lockenv),
     lift_A (st_Arrow ST1 ST2) max_rho max_X = ((at_Arrow AT1 (EffectIntro (le_Var X1) (le_Var X2)) AT2), max_rho', max_X')  ->
     welltyped_algo (G_Extend (G_Extend G f  (sc_Quant nil nil nil  (at_Arrow AT1 (EffectIntro (le_Var X1) (le_Var X2)) AT2) ) ) x  (sc_Quant nil nil nil  AT1 ) ) max_rho' max_X' (e_Thread t) AT'2 (EffectIntro (le_Var X1) D2) C1 max_rho'' max_X'' ->
     stategeneration AT'2 AT2 C2 ->
     constraintgeneration D2 (le_Var X2) C3 ->
     (* No fresh claim X1, X2? *) True  ->
     welltyped_algo G max_rho max_X (e_Thread (t_Value (v_RecFun f (st_Arrow ST1 ST2) x ST1 t))) (at_Arrow AT1 (EffectIntro (le_Var X1) (le_Var X2)) AT2) (EffectIntro D1 D1)  (  ( C1  ++  C2 )   ++  C3 )  max_rho'' max_X''
 | TA_App : forall (G:context) (max_rho:ls_var) (max_X:le_var) (v_1 v_2:value) (AT_1:annotatedtype) (D:lockenv) (X:le_var) (C_1 C_2 C:constraints) (D_1 D_2:lockenv) (max_rho'':ls_var) (max_X''':le_var) (AT_2:annotatedtype) (max_rho':ls_var) (max_X':le_var) (AT'_2:annotatedtype) (max_X'':le_var),
     welltyped_algo G max_rho max_X (e_Thread (t_Value v_1)) (at_Arrow AT_2 (EffectIntro D_1 D_2) AT_1) (EffectIntro D D) C_1 max_rho' max_X' ->
     welltyped_algo G max_rho' max_X' (e_Thread (t_Value v_2)) AT'_2 (EffectIntro D D) C_2 max_rho'' max_X'' ->
     stategeneration AT'_2 AT_2 C ->
       ( max_X''  <  X )%positive   ->
       ( X  <  max_X''' )%positive   ->
     welltyped_algo G max_rho max_X (e_App v_1 v_2) AT_1 (EffectIntro D (le_Var X))  (  (  (  ( C_1  ++  C_2 )   ++  C )   ++   (cons  (c_LockEnv D D_1)  nil)  )   ++   (cons  (c_LockEnv D_2 (le_Var X))  nil)  )  max_rho'' max_X'''
 | TA_Cond : forall (G:context) (max_rho:ls_var) (max_X:le_var) (v:value) (e1 e2:expr) (AT:annotatedtype) (D0 D':lockenv) (C0 C1 C2 C C':constraints) (max_rho''':ls_var) (max_X''':le_var) (ST:simpletype) (AT_1 AT_2:annotatedtype) (D1 D2:lockenv) (max_rho':ls_var) (max_X':le_var) (max_rho'':ls_var) (max_X'':le_var),
       ( ST  =   (downAT AT_1 )  )   ->
       ( ST  =   (downAT AT_2 )  )   ->
     leastupperboundAT AT_1 AT_2 AT C ->
     leastupperboundD D1 D2 D' C' ->
     welltyped_algo G max_rho max_X (e_Thread (t_Value v)) at_Bool (EffectIntro D0 D0) C0 max_rho' max_X' ->
     welltyped_algo G max_rho' max_X' e1 AT_1 (EffectIntro D0 D1) C1 max_rho'' max_X'' ->
     welltyped_algo G max_rho'' max_X'' e2 AT_2 (EffectIntro D0 D2) C2 max_rho''' max_X''' ->
     welltyped_algo G max_rho max_X (e_Cond v e1 e2) AT (EffectIntro D0 D')  (  (  (  ( C0  ++  C1 )   ++  C2 )   ++  C )   ++  C' )  max_rho''' max_X'''
 | TA_Let : forall (G:context) (max_rho:ls_var) (max_X:le_var) (x:variable) (ST1:simpletype) (e1:expr) (t2:thread) (AT2:annotatedtype) (D1 D3:lockenv) (C2:constraints) (max_rho'':ls_var) (max_X'':le_var) (AT1:annotatedtype) (D2:lockenv) (C1:constraints) (max_rho':ls_var) (max_X':le_var) (SC1:scheme),
     welltyped_algo G max_rho max_X e1 AT1 (EffectIntro D1 D2) C1 max_rho' max_X' ->
       (  (downAT AT1 )   =  ST1 )   ->
     welltyped_algo (G_Extend G x SC1) max_rho' max_X' (e_Thread t2) AT2 (EffectIntro D2 D3) C2 max_rho'' max_X'' ->
       ( SC1  =   (sc_close  G   C1   AT1 )  )   ->
     welltyped_algo G max_rho max_X (e_Thread (t_Let x ST1 e1 t2)) AT2 (EffectIntro D1 D3) C2 max_rho'' max_X''
 | TA_Spawn : forall (G:context) (max_rho:ls_var) (max_X:le_var) (t:thread) (D1:lockenv) (C:constraints) (max_rho':ls_var) (max_X':le_var) (AT:annotatedtype) (D2:lockenv),
     welltyped_algo G max_rho max_X (e_Thread t) AT (EffectIntro le_Empty D2) C max_rho' max_X' ->
     (* Should it really be (EffectIntro D1 D1) in conclusion? *) True  ->
     welltyped_algo G max_rho max_X (e_Spawn t) at_Thread (EffectIntro D1 D1) C max_rho' max_X'
 | TA_Lock : forall (G:context) (max_rho:ls_var) (max_X:le_var) (v:value) (rho:ls_var) (D:lockenv) (X:le_var) (C1 C2:constraints) (max_rho':ls_var) (max_X'' max_X':le_var),
     welltyped_algo G max_rho max_X (e_Thread (t_Value v)) (at_Lock (ls_Var rho)) (EffectIntro D D) C1 max_rho' max_X' ->
       ( max_X'  <  X )%positive   ->
       ( X  <  max_X'' )%positive   ->
     constraintgeneration (le_Add D  (le_Append le_Empty  (ls_Var rho)  (Zinf_Z 1)) ) (le_Var X) C2 ->
     welltyped_algo G max_rho max_X (e_AcqLock v) (at_Lock (ls_Var rho)) (EffectIntro D (le_Var X))  ( C1  ++  C2 )  max_rho' max_X''
 | TA_Unlock : forall (G:context) (max_rho:ls_var) (max_X:le_var) (v:value) (rho:ls_var) (D:lockenv) (X:le_var) (C1 C2:constraints) (max_rho':ls_var) (max_X'' max_X':le_var),
     welltyped_algo G max_rho max_X (e_Thread (t_Value v)) (at_Lock (ls_Var rho)) (EffectIntro D D) C1 max_rho' max_X' ->
       ( max_X'  <  X )%positive   ->
       ( X  <  max_X'' )%positive   ->
     constraintgeneration (le_Sub D  (le_Append le_Empty  (ls_Var rho)  (Zinf_Z 1)) ) (le_Var X) C2 ->
     welltyped_algo G max_rho max_X (e_RelLock v) (at_Lock (ls_Var rho)) (EffectIntro D (le_Var X))  ( C1  ++  C2 )  max_rho' max_X''.

