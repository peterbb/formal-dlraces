Require Import Arith.
Require Import Bool.
Require Import List.
Require Import ott_list_core.


Require Import Syntax.
Require Import Maps.

Definition lockcount := nat. (*r Times lock is taken *)
Lemma eq_lockcount: forall (x y : lockcount), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_lockcount : ott_coq_equality.

Inductive lockstate : Set := 
 | lockstate_Free : lockstate
 | lockstate_Taken (p:processid) (lc:lockcount).

Definition state : Set := PTree.t lockstate.
Definition lockref_lookup (S : state) (l : lockref) : option lockstate :=
    PTree.get l S.

Definition lockref_fresh (S : state) (l : lockref) : Prop :=
    lockref_lookup S l = None.

(** definitions *)

(* defns LocalStep *)
Inductive localstep : thread -> thread -> Prop :=    (* defn localstep *)
 | R_Red : forall (x:variable) (ST:simpletype) (v:value) (t:thread),
     localstep (t_Let x ST (e_Thread (t_Value v)) t)  (value_subst_thread  v   x   t ) 
 | R_Let : forall (x_2:variable) (ST_2:simpletype) (x_1:variable) (ST_1:simpletype) (e_1:expr) (t_1 t_2:thread),
     localstep (t_Let x_2 ST_2 (e_Thread  (  (t_Let x_1 ST_1 e_1 t_1)  ) ) t_2) (t_Let x_1 ST_1 e_1  (  (t_Let x_2 ST_2 (e_Thread t_1) t_2)  ) )
 | R_If1 : forall (x:variable) (ST:simpletype) (e_1 e_2:expr) (t:thread),
     localstep (t_Let x ST  (e_Cond v_True e_1 e_2)  t) (t_Let x ST e_1 t)
 | R_If2 : forall (x:variable) (ST:simpletype) (e_1 e_2:expr) (t:thread),
     localstep (t_Let x ST  (e_Cond v_False e_1 e_2)  t) (t_Let x ST e_2 t)
 | R_App1 : forall (x:variable) (ST:simpletype) (x':variable) (ST':simpletype) (t':thread) (v:value) (t:thread),
     localstep (t_Let x ST  (e_App  (  (v_Fun x' ST' t')  )  v)  t) (t_Let x ST (e_Thread  (value_subst_thread  v   x'   t' ) ) t)
 | R_App2 : forall (x:variable) (ST:simpletype) (f:variable) (ST_1:simpletype) (x':variable) (ST_2:simpletype) (t':thread) (v:value) (t:thread),
     localstep (t_Let x ST  (e_App  (  (v_RecFun f ST_1 x' ST_2 t')  )  v)  t) (t_Let x ST (e_Thread  (value_subst_thread  (v_RecFun f ST_1 x' ST_2 t')   f    (   (value_subst_thread  v   x'   t' )   )  ) ) t).
(** definitions *)

(* defns GlobalStep *)
Inductive globalstep : state -> program -> state -> program -> Prop :=    (* defn globalstep *)
 | R_Lift : forall (S:state) (p:processid) (t_1 t_2:thread),
     localstep t_1 t_2 ->
     globalstep S (P_Single p t_1) S (P_Single p t_2)
 | R_Par : forall (S:state) (P1 P2:program) (S':state) (P1':program),
     globalstep S P1 S' P1' ->
     NoDup (dom_P ((P_Parallel P1 P2)))  ->
     globalstep S (P_Parallel P1 P2) S' (P_Parallel P1' P2)
 | R_Spawn : forall (S:state) (p1:processid) (x:variable) (ST:simpletype) (t2 t1:thread) (p2:processid),
       ( p1  <>  p2 )   ->
     globalstep S (P_Single p1 (t_Let x ST (e_Spawn t2) t1)) S (P_Parallel (P_Single p1 (t_Let x ST (e_Thread (t_Value (v_ProcessId p2))) t1)) (P_Single p2 t2))
 | R_NewL : forall (S:state) (p:processid) (x:variable) (ST:simpletype) (pi:programpoint) (t:thread) (S':state) (l:lockref) (r:lockset),
       ( S'  =   (PTree.set  l   lockstate_Free   S )  )   ->
     lockref_fresh S l  ->
     globalstep S (P_Single p (t_Let x ST (e_NewL pi) t)) S' (P_Single p (t_Let x ST (e_Thread (t_Value (v_LockRef l r))) t))
 | R_Lock : forall (S:state) (p:processid) (x:variable) (ST:simpletype) (l:lockref) (r:lockset) (t:thread) (S':state),
     lockref_lookup S l = Some lockstate_Free  ->
       ( S'  =   (PTree.set  l    (lockstate_Taken  p  1)    S )  )   ->
     globalstep S (P_Single p (t_Let x ST (e_AcqLock (v_LockRef l r)) t)) S' (P_Single p (t_Let x ST (e_Thread (t_Value (v_LockRef l r))) t))
 | R_Relock : forall (S:state) (p:processid) (x:variable) (ST:simpletype) (l:lockref) (r:lockset) (t:thread) (S':state) (lc:lockcount),
     lockref_lookup S l = Some (lockstate_Taken p lc)  ->
       ( S'  =   (PTree.set  l    (lockstate_Taken  p  ( lc  + 1))    S )  )   ->
     globalstep S (P_Single p (t_Let x ST (e_AcqLock (v_LockRef l r)) t)) S' (P_Single p (t_Let x ST (e_Thread (t_Value (v_LockRef l r))) t))
 | R_Unlock : forall (S:state) (p:processid) (x:variable) (ST:simpletype) (l:lockref) (r:lockset) (t:thread) (S':state) (lc:lockcount),
     lockref_lookup S l = Some (lockstate_Taken p lc)  ->
       ( S'  =   (PTree.set  l    (if beq_nat  lc  0
                    then lockstate_Free
                    else lockstate_Taken  p  ( lc  - 1))    S )  )   ->
     globalstep S (P_Single p (t_Let x ST (e_RelLock (v_LockRef l r)) t)) S' (P_Single p (t_Let x ST (e_Thread (t_Value (v_LockRef l r))) t)).


