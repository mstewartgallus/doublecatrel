Require Import Blech.Spec.

Bind Scope list_scope with environment.
Bind Scope list_scope with subst.
Bind Scope list_scope with usage.

Infix "*" := t_prod.

Notation "'η'" := (eta) (at level 0).

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
