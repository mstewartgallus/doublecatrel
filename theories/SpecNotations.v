Require Import Blech.Spec.

Infix "*" := t_prod.

Notation "Γ ⊢ E 'in' t" := (JE Γ E t) (at level 90).
Notation "⊢ v 'in' t" := (Jv v t) (at level 90).

Notation "v0 ~> v1" := (step_v v0 v1) (at level 90).
Notation "v0 *~> v1" := (multi_v v0 v1) (at level 90).

Notation "Δ ⊢ E [ v ]" := (Jsat Δ E v) (at level 90).
