Require Import Blech.Spec.

Infix "*" := t_prod.

Notation "Γ ⊢ E ? t" := (JE Γ E t) (at level 90).
Notation "Γ ⊢ v 'in' t" := (Jv Γ v t) (at level 90).

Notation "v ⇓ N" := (big v N) (at level 90).

Infix "|-" := P_with (at level 30).
