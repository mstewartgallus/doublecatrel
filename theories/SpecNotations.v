Require Import Blech.Spec.

Bind Scope list_scope with environment.
Bind Scope list_scope with subst.
Bind Scope list_scope with vars.
Bind Scope list_scope with usage.
Bind Scope list_scope with spans.
Bind Scope list_scope with stores.

Infix "*" := t_prod.

Notation "'η'" := (eta) (at level 0).

Notation "G ⊢ v ⇐ t" := (Jv G v t) (at level 90).
Notation "G ⊢ V ⇒ t" := (JV G V t) (at level 90).

Notation "ρ ⊢ v ⇓ v'" := (bigv ρ v v') (at level 90).
(* Notation "ρ ⊢ V ⇓ v'" := (bigv ρ V v') (at level 90). *)

Notation "D ⊢ E ⊠ D'" := (sE D E D') (at level 90).

Infix "|-" := P_with (at level 30).

Module RelNotations.
  Declare Custom Entry rel.

  Notation "<{ E }>" := E (E custom rel at level 99).
  Notation "x" := x (in custom rel, x ident).
  Notation "${ e }" := e (in custom rel, e constr).

  Notation "'I'" := t_unit (in custom rel at level 0).
  Notation "S ⊗ T" := (t_prod S T) (in custom rel at level 50, right associativity).

  Notation "'λ' X , E" :=
    (E_lam X E)
      (in custom rel at level 200,
          X constr at level 99,
          E custom rel at level 99,
          left associativity).

  Notation "( E , E' )" := (E_fanout E E') (in custom rel at level 30, right associativity).
  Notation "'let' ( X , Y ) := E 'in' E'" :=
    (e_let X Y E E')
      (in custom rel at level 90,
          X constr at level 99, Y constr at level 99,
          E custom rel at level 99, E' custom rel at level 99,
          left associativity).

  Coercion e_app: redex >-> Funclass.
  Coercion e_var: var >-> redex.
End RelNotations.
