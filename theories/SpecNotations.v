Require Import Blech.Spec.

Infix "*" := t_prod.

Notation "Γ ⊢ E ? t" := (JE Γ E t) (at level 90).
Notation "Γ ⊢ v 'in' t" := (Jv Γ v t) (at level 90).

Notation "v ⇓ N" := (big v N) (at level 90).

Infix "|-" := P_with (at level 30).

Module RelNotations.
  Declare Custom Entry rel.

  Notation "<{ E }>" := E (E custom rel at level 99).

  Notation "( x )" := x (in custom rel, x at level 99).
  Notation "x" := x (in custom rel at level 0, x constr at level 0).

  Notation "'I'" := t_unit (in custom rel at level 0).
  Notation "S ⊗ T" := (t_prod S T) (in custom rel at level 50, right associativity).


  Notation "'λ' X : t , E" :=
    (E_lam X t E)
      (in custom rel at level 200,
          X at level 99,
          t custom rel at level 99,
          E custom rel at level 99,
          left associativity).

  Notation "( E , E' )" := (E_fanout E E') (in custom rel at level 30, right associativity).
  Notation "'let' ( X , Y ) := E 'in' E'" :=
    (E_let X Y E E')
      (in custom rel at level 90,
          X at level 99, Y at level 99,
          E custom rel at level 99, E' custom rel at level 99,
          left associativity).

  Coercion E_app: context >-> Funclass.
  Coercion E_var: cvar >-> context.
End RelNotations.
