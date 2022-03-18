Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.Opaque.
Require Blech.OptionNotations.

Require Import Coq.Unicode.Utf8.
Require Coq.Bool.Bool.
Require Coq.Lists.List.

Require Import FunInd.

Import List.ListNotations.
Import IfNotations.

Implicit Type Γ: environment.
Implicit Type t: type.
Implicit Types x y: var.

Definition eq_environment Γ Γ': {Γ = Γ'} + {Γ ≠ Γ'}.
Proof.
  decide equality.
  destruct a as [v t], p as [v' t'].
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

Fixpoint minus x Γ: environment :=
  if Γ is ((y, t) :: T)%list
  then
    if eq_var x y
    then
      T
    else
      cons (y, t) (minus x T)
  else
    nil.

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

Lemma find_minus {x y Γ}:
  x ≠ y →
  find x (minus y Γ) = find x Γ.
Proof.
  intros p.
  induction Γ.
  1: auto.
  destruct a as [x' t].
  cbn.
  destruct eq_var, eq_var.
  all: cbn.
  all: subst.
  all: try contradiction.
  all: try destruct eq_var.
  all: try contradiction.
  all: auto.
Qed.

Lemma unshadow {y t0 t1 Γ}:
  ∀ x t,
  mem x t ((y, t0) :: (y, t1) :: Γ) →
  mem x t ((y, t0) :: Γ).
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
  mem x t ((y, t0) :: Γ) →
  mem x t ((y, t0) :: (y, t1) :: Γ).
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
  ∀ x t, mem x t ((y, t0) :: (y', t1) :: Γ) → mem x t ((y', t1) :: (y, t0) :: Γ).
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
