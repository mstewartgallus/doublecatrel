Require Import Blech.Spec.

Infix "*" := t_prod.

Notation "Γ ⊢ E 'in' t" := (JE Γ E t) (at level 90).
Notation "⊢ v 'in' t" := (Jv v t) (at level 90).

Notation "v0 ~> v1" := (step v0 v1) (at level 90).
Notation "v0 *~> v1" := (multi v0 v1) (at level 90).

Notation "Δ ⊢ E [ v ]" := (sat Δ E v) (at level 90).
