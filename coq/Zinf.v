Require Import ZArith.ZArith.

Open Scope Z_scope.

Inductive Zinf : Set :=
    | Zinf_Z : Z -> Zinf
    | Zinf_pinf : Zinf
    | Zinf_ninf : Zinf.

Coercion Zinf_Z : Z >-> Zinf.

Definition Zinf_inc (a : Zinf) : Zinf :=
    match a with
    | Zinf_Z n => Zinf_Z (n + 1)
    | _ => a
    end.

Definition Zinf_dec (a : Zinf) : Zinf :=
    match a with
    | Zinf_Z n => Zinf_Z (n - 1)
    | _ => a
    end.

Definition Zinf_Leq (a b : Zinf) : Prop :=
    match a, b with
    | Zinf_Z n, Zinf_Z m => n <= m
    | Zinf_Z _, Zinf_pinf => True
    | Zinf_Z _, Zinf_ninf => False
    | Zinf_pinf, Zinf_Z _ => False
    | Zinf_ninf, Zinf_Z _ => True
    | Zinf_pinf, Zinf_pinf => True
    | Zinf_ninf, Zinf_ninf => True
    | Zinf_ninf, Zinf_pinf => True
    | Zinf_pinf, Zinf_ninf => False
    end.

Definition Zinf_add (a b : Zinf) :=
    match a, b with
    | Zinf_Z n, Zinf_Z m => Zinf_Z (n + m)
    | Zinf_pinf, Zinf_pinf => Zinf_pinf
    | Zinf_ninf, Zinf_ninf => Zinf_ninf
    | Zinf_ninf, Zinf_pinf => Zinf_Z 0
    | Zinf_pinf, Zinf_ninf => Zinf_Z 0
    | Zinf_Z _, b' => b'
    | a', Zinf_Z _ => a'
    end.

Definition Zinf_sub (a b : Zinf) :=
    match a, b with
    | Zinf_Z n, Zinf_Z m => Zinf_Z (n - m)
    | Zinf_pinf, Zinf_pinf => Zinf_Z 0
    | Zinf_ninf, Zinf_ninf => Zinf_Z 0
    | Zinf_ninf, Zinf_pinf => Zinf_ninf
    | Zinf_pinf, Zinf_ninf => Zinf_pinf
    | Zinf_Z _, Zinf_ninf => Zinf_pinf
    | Zinf_Z _, Zinf_pinf => Zinf_ninf
    | a', Zinf_Z _ => a'
    end.


