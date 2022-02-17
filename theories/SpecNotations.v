Require Import Blech.Spec.

Infix "*" := t_prod.

Notation "Γ ⊢ E 'in' t" := (JE Γ E t) (at level 90).
Notation "⊢ v 'in' t" := (Jv v t) (at level 90).

Notation "v0 ⇓ v1" := (big v0 v1) (at level 90).

Notation "σ |- c 'in' E [ v ]" := (sat σ c E v) (at level 90).
