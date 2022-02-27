Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Import Coq.Unicode.Utf8.
Require Coq.Lists.List.

Require Import FunInd.

Import List.ListNotations.
Import IfNotations.

Implicit Type Γ: environment.
Implicit Type t: type.
Implicit Types x y: var.

Function find x Γ :=
  if Γ is ((y, t) :: T)%list
  then
    if eq_var x y
    then
      Some t
    else
      find x T
  else
    None.

Lemma find_sound:
  ∀ {x Γ t}, find x Γ = Some t → mem x t Γ.
Proof using .
  intros x Γ.
  functional induction (find x Γ).
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: constructor.
  all: auto.
Qed.

Lemma find_complete {x Γ t}:
  mem x t Γ → find x Γ = Some t.
Proof using .
  intro p.
  induction p.
  all: cbn.
  - destruct eq_var.
    2: contradiction.
    reflexivity.
  - destruct eq_var.
    1: contradiction.
    auto.
Qed.
