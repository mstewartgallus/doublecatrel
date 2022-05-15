Require Import Blech.Spec.

Require Import Coq.Unicode.Utf8.

Bind Scope list_scope with environment.
Bind Scope list_scope with subst.
Bind Scope list_scope with usage.
Bind Scope list_scope with sorts.
Bind Scope list_scope with functions.
Bind Scope list_scope with relations.
Bind Scope list_scope with theory.

Infix "*" := t_prod.

Notation "'η'" := (eta) (at level 0).

Definition eq_usage (Δ Δ': usage): {Δ = Δ'} + {Δ ≠ Δ'}.
Proof.
  decide equality.
  destruct a as [x u], p as [y u'].
  destruct (eq_var x y), (eq_use u u').
  all: subst.
  all: auto.
  all: right.
  all: intro p.
  all: inversion p.
  all: auto.
Defined.

(* Notation "( X , F , G ) ⊢ v ⇐ t" := (Jv X F G v t) (at level 90). *)
(* Notation "( X , F , G ) ⊢ V ⇒ t" := (JV X F G V t) (at level 90). *)

(* Notation "ρ ⊢ v ⇓ v'" := (bigv ρ v v') (at level 90). *)
(* Notation "ρ ⊢ V ⇓ v'" := (bigv ρ V v') (at level 90). *)

(* Notation "D ⊢ E ⊠ D'" := (sE D E D') (at level 90). *)

Definition c_true := c_unify E_tt E_tt t_unit.
Definition c_and c c' := c_unify (E_match_tt c) (E_match_tt c') t_unit.

Module RelNotations.
  Declare Custom Entry rel.

  Notation "<{ E }>" := E (E custom rel at level 99).
  Notation "x" := x (in custom rel at level 0, x constr).
  Notation "( E )" := E (in custom rel, E custom rel at level 0).
  Notation "${ e }" := e (in custom rel, e constr, only parsing).

  Coercion t_var: sort >-> type.

  Notation "'I'" := t_unit (in custom rel at level 0).
  Notation "S ⊗ T" := (t_prod S T) (in custom rel at level 50, right associativity).

  Definition X: var := 0.
  Definition X1: var := 1.
  Definition X2: var := 2.

  Definition Y: var := 3.
  Definition Z: var := 4.

  Coercion V_var: var >-> elim.

  Coercion E_var: var >-> context.

  Notation "⊤" := c_true (in custom rel).
  Notation "⊥" := c_false (in custom rel).

  Infix "∧" := c_and (in custom rel at level 30, right associativity).
  Infix "∨" := c_or (in custom rel at level 30, right associativity).

  Notation "!" := E_tt (in custom rel).
  Infix "," := E_fanout (in custom rel at level 30, right associativity).

  (* Notation "'del'" := E_del (in custom rel). *)
  (* Notation "'dup'" := E_dup (in custom rel). *)
  (* Notation "'unify'" := c_unify (in custom rel). *)

  Notation "E '>>' c" := (c_unify E (E_match_tt c) t_unit) (in custom rel at level 30, right associativity).

  (* Notation "'ε' . c" := (E_match_tt c) *)
  (*                         (in custom rel at level 200, c custom rel at level 99, *)
  (*                             left associativity). *)
  (* Notation "'ε' X , Y . c" := (E_match_fanout X Y c) *)
  (*                               (in custom rel at level 200, *)
  (*                                   X constr at level 99, *)
  (*                                   Y constr at level 99, *)
  (*                                   c custom rel at level 99, *)
  (*                                   left associativity). *)

  (* Notation "'ε' X . c" := (E_epsilon X c) *)
  (*                           (in custom rel at level 200, *)
  (*                               X constr at level 99, *)
  (*                               c custom rel at level 99, *)
  (*                               left associativity). *)
End RelNotations.
