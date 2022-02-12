Require Import Blech.Spec.
Require Blech.Map.
Require Import Blech.SpecNotations.

Require Import Coq.Classes.SetoidClass.

Import IfNotations.

Theorem id_fanout:
  forall v t,
  ⊢ v in t ->
  let x := 0 in
  Map.empty ⊢ (E_all x t (E_var x)) [ v_fanout v v ].
Proof using.
  repeat econstructor.
  auto.
Qed.
