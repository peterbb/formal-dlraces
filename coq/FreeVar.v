Require Import Arith.
Require Import Bool.
Require Import List.
Require Import ott_list_core.


Require Export MSetPositive MSetProperties.
Module PS := PositiveSet.
Module PSProp := WPropertiesOn PS.


Definition free_le_var : Set := PS.t.


Definition free_ls_var : Set := PS.t.
Require Import Syntax TypeSyntax.

Section Traverse.
    (* Functions which walk the syntax tree, looking for free
     * variables.
     *)

    Variable remember_rho : ls_var -> PS.t.
    Variable remember_X : le_var -> PS.t.
    Variable select_binding : 
        list ls_var -> list le_var -> list positive.

    Definition list_to_set (xs : list positive) : PS.t :=
        fold_right (fun x set => PS.add x set) PS.empty xs.

    Fixpoint traverse_r (r : lockset) : PS.t :=
        match r with
        | ls_Var rho => remember_rho rho
        | ls_Single _ => PS.empty
        | ls_Union r1 r2 =>
            PS.union (traverse_r r1) (traverse_r r2)
        end.

    Fixpoint traverse_D (D : lockenv) : PS.t :=
        match D with
        | le_Empty => PS.empty
        | le_Var X => remember_X X
        | le_Append D' r _ => PS.union (traverse_D D') (traverse_r r)
        | le_Add D1 D2 => PS.union (traverse_D D1) (traverse_D D2)
        | le_Sub D1 D2 => PS.union (traverse_D D1) (traverse_D D2)
        end.

    Fixpoint traverse_AT (AT : annotatedtype) : PS.t :=
        match AT with
        | at_Lock r => traverse_r r
        | at_Arrow AT1 (EffectIntro D1 D2) AT2 =>
            PS.union (traverse_AT AT1)
              (PS.union (traverse_D D1)
                (PS.union (traverse_D D2)
                          (traverse_AT AT2)))
        | _ => PS.empty
        end.

    Definition traverse_ineq (c : inequality) : PS.t :=
        match c with
        | c_LockSet r1 r2 => 
            PS.union (traverse_r r1) (traverse_r r2)
        | c_LockEnv D1 D2 => 
            PS.union (traverse_D D1) (traverse_D D2)
        end.

    Definition traverse_C (C : constraints) : PS.t :=
        fold_right PS.union PS.empty (map traverse_ineq C).

    Definition traverse_SC (SC : scheme) : PS.t :=
        match SC with
        | sc_All rhos Xs C AT =>
            PS.diff (PS.union (traverse_C C) (traverse_AT AT))
                    (list_to_set (select_binding rhos Xs))
        end.

    Definition traverse_G (G : context) : PS.t :=
        fold_right PS.union PS.empty 
            (map (fun p => (traverse_SC (snd p))) G).

End Traverse.

Definition select_rhos (rhos : list ls_var) (Xs : list le_var) := rhos.
Definition select_Xs  (rhos : list ls_var) (Xs : list le_var) := Xs.
Definition ignore (_:positive) := PS.empty.

Definition free_ls_D := traverse_D PS.singleton ignore.
Definition free_ls_C := traverse_C PS.singleton ignore.
Definition free_ls_AT := traverse_AT PS.singleton ignore.
Definition free_ls_G := traverse_G PS.singleton ignore select_rhos.

Definition free_le_D := traverse_D ignore PS.singleton.
Definition free_le_C := traverse_C ignore PS.singleton.
Definition free_le_AT := traverse_AT ignore PS.singleton.
Definition free_le_G := traverse_G ignore PS.singleton select_Xs.



Definition sc_close_find_vars Gvars Cvars ATvars :=
    PS.elements (PS.diff (PS.union Cvars ATvars) Gvars).

Definition sc_close G C AT : scheme :=
    sc_All   (sc_close_find_vars (free_ls_G G) (free_ls_C C) (free_ls_AT AT))
             (sc_close_find_vars (free_le_G G) (free_le_C C) (free_le_AT AT))
             C AT.




