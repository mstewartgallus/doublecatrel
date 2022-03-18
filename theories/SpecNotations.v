Require Import Blech.Spec.

Bind Scope list_scope with environment.
Bind Scope list_scope with subst.
Bind Scope list_scope with vars.
Bind Scope list_scope with usage.
Bind Scope list_scope with spans.

Infix "*" := t_prod.

Notation "G ⊢ v 'in' t" := (Jv G v t) (at level 90).

Notation "v ⇓ N" := (big v N) (at level 90).

Infix "|-" := P_with (at level 30).

Module RelNotations.
  Declare Custom Entry rel.

  Notation "<{ E }>" := E (E custom rel at level 99).
  Notation "x" := x (in custom rel, x ident).
  Notation "${ e }" := e (in custom rel, e constr).

  Notation "'I'" := t_unit (in custom rel at level 0).
  Notation "S ⊗ T" := (t_prod S T) (in custom rel at level 50, right associativity).

  Notation "'λ' X : t , E" :=
    (E_lam X t E)
      (in custom rel at level 200,
          X constr at level 99,
          t custom rel at level 99,
          E custom rel at level 99,
          left associativity).

  Notation "( E , E' )" := (E_fanout E E') (in custom rel at level 30, right associativity).
  Notation "'let' ( X , Y ) := E 'in' E'" :=
    (E_let X Y E E')
      (in custom rel at level 90,
          X constr at level 99, Y constr at level 99,
          E custom rel at level 99, E' custom rel at level 99,
          left associativity).

  Coercion E_app: context >-> Funclass.
  Coercion E_var: var >-> context.
End RelNotations.
