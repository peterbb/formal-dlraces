Require Import Arith.
Require Export PArith.

Definition lockref : Set := nat.
Definition variable : Set := nat.
Definition programpoint : Set := positive.
Definition processid : Set := nat.

Definition ls_var : Set := positive.
Lemma eq_ls_var: forall (x y : ls_var), {x=y}+{x<>y}.
Proof. decide equality. Qed.

Inductive lockset : Set :=
 | ls_Var    (rho :ls_var)
 | ls_Single (pi :programpoint)
 | ls_Union   (r r':lockset).

Inductive simpletype : Set :=
 | st_Bool : simpletype
 | st_Thread : simpletype
 | st_Lock : simpletype
 | st_Arrow (ST ST' :simpletype).

Inductive thread : Set :=
 | t_Value (v :value)
 | t_Let (x:variable) (ST:simpletype) (e:expr) (t:thread)
with expr : Set :=
 | e_Thread (t:thread)
 | e_App (v_1:value) (v_2:value)
 | e_Cond (v:value) (e_1:expr) (e_2:expr)
 | e_Spawn (t:thread)
 | e_NewL (pi:programpoint)
 | e_AcqLock (v:value)
 | e_RelLock (v:value)
with value : Set :=
 | v_VarRef (x:variable)
 | v_LockRef (l:lockref) (r:lockset)
 | v_True : value
 | v_False : value 
 | v_ProcessId (p:processid)
 | v_Fun (x:variable) (ST:simpletype) (t:thread)
 | v_RecFun (f:variable) (ST_1:simpletype) (x:variable) (ST_2:simpletype) (t:thread).

 Coercion t_Value : value >-> thread.
 Coercion e_Thread : thread >-> expr.

Inductive program : Set :=
 | P_Empty : program
 | P_Single (p:processid) (t:thread)
 | P_Parallel (P P' :program).

