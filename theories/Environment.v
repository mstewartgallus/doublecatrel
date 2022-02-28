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

Lemma unshadow {y t0 t1 Γ}:
  ∀ x t,
  mem x t ((y, t0) :: (y, t1) :: Γ)%list →
  mem x t ((y, t0) :: Γ)%list.
Proof using.
  intros ? ? p.
  inversion p.
  all: subst.
  - constructor.
  - constructor.
    all: auto.
    inversion H5.
    all: auto.
    subst.
    contradiction.
Qed.

Lemma shadow {y t0 t1 Γ}:
  ∀ x t,
  mem x t ((y, t0) :: Γ)%list →
  mem x t ((y, t0) :: (y, t1) :: Γ)%list.
Proof using.
  intros ? ? p.
  inversion p.
  all: subst.
  all: constructor.
  all: auto.
  constructor.
  all: auto.
Qed.

Lemma weaken_nil {Γ}: ∀ x t, mem x t nil → mem x t Γ.
Proof using.
  intros ? ? p.
  inversion p.
Qed.

Lemma weaken {Δ Γ}: ∀ x t, mem x t Δ → mem x t (Δ ++ Γ)%list.
Proof using.
  intros ? ? p.
  induction p.
  - cbn.
    constructor.
  - cbn.
    constructor.
    all: auto.
Qed.

Lemma swap {Γ y y' t0 t1}:
  y ≠ y' →
  ∀ x t, mem x t ((y, t0) :: (y', t1) :: Γ)%list → mem x t ((y', t1) :: (y, t0) :: Γ)%list.
Proof using.
  intros ? ? ? p.
  inversion p.
  all: subst.
  - constructor.
    1: auto.
    constructor.
  - inversion H6.
    all: subst.
    + constructor.
    + constructor.
      all: auto.
      constructor.
      all: auto.
Qed.
