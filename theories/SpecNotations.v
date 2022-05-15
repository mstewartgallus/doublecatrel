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

Module RelNotations.
  Declare Custom Entry rel.

  Notation "<{ E }>" := E (E custom rel at level 99).
  Notation "x" := x (in custom rel, x ident).
  Notation "${ e }" := e (in custom rel, e constr).

  Notation "'I'" := t_unit (in custom rel at level 0).
  Notation "S ⊗ T" := (t_prod S T) (in custom rel at level 50, right associativity).

  (* Notation "'λ' X , E" := *)
  (*   (E_lam X E) *)
  (*     (in custom rel at level 200, *)
  (*         X constr at level 99, *)
  (*         E custom rel at level 99, *)
  (*         left associativity). *)

  Notation "( E , E' )" := (E_fanout E E') (in custom rel at level 30, right associativity).

  Coercion E_var: var >-> context.
End RelNotations.
