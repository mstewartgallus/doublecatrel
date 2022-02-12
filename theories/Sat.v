Require Import Blech.Spec.
Require Blech.Map.
Require Import Blech.SpecNotations.

Require Import Coq.Classes.SetoidClass.

Import IfNotations.

Theorem id_fanout t v: Map.empty ⊢ (E_all 0 t (E_var 0)) [ v_fanout v v ].
Proof using.
  repeat econstructor.
Qed.
