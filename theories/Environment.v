Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Blech.OptionNotations.
Require Import Blech.Assoc.

Require Import Coq.Unicode.Utf8.
Require Coq.Bool.Bool.
Require Coq.Lists.List.
Require Coq.Arith.PeanoNat.

Require Import FunInd.

Import List.ListNotations.
Import IfNotations.
Import PeanoNat.Nat.

Implicit Type Γ: environment.
Implicit Type t: type.
Implicit Types x y: var.

Definition eq_environment Γ Γ': {Γ = Γ'} + {Γ ≠ Γ'}.
Proof.
  decide equality.
  destruct a as [v t], m as [v' t'].
  destruct (eq_var v v'), (eq_type t t').
  all: subst.
  - left.
    auto.
  - right.
    intro p.
    inversion p.
    contradiction.
  - right.
    intro p.
    inversion p.
    contradiction.
  - right.
    intro p.
    inversion p.
    contradiction.
Defined.

Lemma find_sound:
  ∀ {x Γ t}, Assoc.find x Γ = Some t → mem x t Γ.
Proof using .
  intros x Γ.
  functional induction (Assoc.find x Γ).
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: constructor.
  all: auto.
Qed.

Lemma find_complete {x Γ t}:
  mem x t Γ → Assoc.find x Γ = Some t.
Proof using .
  intro p.
  induction p.
  all: cbn.
  - destruct eq_dec.
    2: contradiction.
    reflexivity.
  - destruct eq_dec.
    1: contradiction.
    auto.
Qed.

Lemma unshadow {y t0 t1 Γ}:
  ∀ x t,
  mem x t (y ↦ t0 :: y ↦ t1 :: Γ) →
  mem x t (y ↦ t0 :: Γ).
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
  mem x t (y ↦ t0 :: Γ) →
  mem x t (y ↦ t0 :: y ↦ t1 :: Γ).
Proof using.
  intros ? ? p.
  inversion p.
  all: subst.
  all: constructor.
  all: auto.
  constructor.
  all: auto.
Qed.

Lemma weaken_nil {Γ}: ∀ x t, mem x t [] → mem x t Γ.
Proof using.
  intros ? ? p.
  inversion p.
Qed.

Lemma weaken {Γ Γ'}: ∀ x t, mem x t Γ → mem x t (Γ ++ Γ').
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
  ∀ x t, mem x t (y ↦ t0 :: y' ↦ t1 :: Γ) → mem x t (y' ↦ t1 :: y ↦ t0 :: Γ).
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
