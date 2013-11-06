Require Import List.

Require Import Syntax.
Require Export Zinf.

Definition abstract_lockcount := Zinf.

Definition le_var : Set := positive.
Lemma eq_le_var: forall (x y : le_var), {x=y}+{x<>y}.
Proof. decide equality. Qed.

Inductive lockenv : Set :=
 | le_Empty : lockenv
 | le_Var (X:le_var)
 | le_Append (D:lockenv) (r:lockset) (n:abstract_lockcount)
 | le_Add (D D' :lockenv)
 | le_Sub (D D' :lockenv).

Inductive inequality : Set :=
 | c_LockSet (r r' : lockset)
 | c_LockEnv (D D' : lockenv).

Inductive effect : Set := EffectIntro (D D' :lockenv).

Inductive annotatedtype : Set :=
 | at_Bool : annotatedtype
 | at_Thread : annotatedtype
 | at_Lock (r:lockset)
 | at_Arrow (AT:annotatedtype) (phi:effect) (AT':annotatedtype).

Definition constraints : Set := list inequality.

Inductive scheme : Type :=
 | sc_All (rhos : list ls_var) (Xs : list le_var) 
          (C : constraints) (AT : annotatedtype).

Definition AT_to_scheme (AT : annotatedtype) : scheme :=
    sc_All nil nil nil AT.

Coercion AT_to_scheme : annotatedtype >-> scheme.

Definition context : Set := list (variable * scheme) % type.

Inductive program_type : Type :=
 | pt_Single (p:processid) (phi:effect) (C:constraints)
 | pt_Parallell (Phi Phi' :program_type).

Inductive ContextLookup : context -> variable -> scheme -> Prop :=
 | LookupAx : forall (G:context) (x:variable) (SC:scheme),
     ContextLookup  ((x, SC)::G)  x SC
 | LookupNext : forall (G:context) (x':variable) (SC':scheme) (x:variable) (SC:scheme),
     x <> x' ->
     ContextLookup G x SC ->
     ContextLookup  ((x', SC')::G)  x SC.

Fixpoint downAT (x1:annotatedtype) : simpletype:=
  match x1 with
  | at_Bool => st_Bool
  | at_Thread => st_Thread
  | at_Lock r => st_Lock
  | at_Arrow AT phi AT' => st_Arrow (downAT AT) (downAT AT')
  end.

Definition downSC (SC : scheme) : simpletype:=
  match SC with
  | sc_All rhos Xs C AT => downAT AT
  end.



