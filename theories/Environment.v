Require Import Blech.Spec.
Require Import Blech.SpecNotations.
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

Module ProofTree.
  Import OptionNotations.

  Inductive mem: Set :=
  | mem_eq x t Γ
  | mem_ne x t Γ y t': mem → mem.

  Definition varof p :=
    match p with
    | mem_eq x _ _ => x
    | mem_ne x _ _ _ _ _ => x
    end.

  Definition typeof p :=
    match p with
    | mem_eq _ t _ => t
    | mem_ne _ t _ _ _ _ => t
    end.

  Definition envof p :=
    match p with
    | mem_eq x t Γ => cons (x, t) Γ
    | mem_ne _ _ Γ y t' _ => cons (y, t') Γ
    end.

  #[local]
  Definition test {P Q} (p: {P} + {Q}): bool := if p then true else false.

  Function check (p: mem): bool :=
    match p with
    | mem_eq x t Γ => true
    | mem_ne x t Γ y t' p =>
        negb (test (eq_var x y))
        && test (eq_var x (varof p))
        && test (eq_type t (typeof p))
        && test (eq_environment Γ (envof p))
        && check p
    end %bool.

  Definition asserts (p: mem): Prop := Spec.mem (varof p) (typeof p) (envof p).

  Lemma check_sound (p: mem): Bool.Is_true (check p) → asserts p.
  Proof.
    unfold asserts.
    induction p.
    all: cbn.
    all: intros q.
    - constructor.
    - destruct eq_var, eq_var, eq_type, eq_environment, (check p).
      all: try contradiction.
      subst.
      constructor.
      all: auto.
  Qed.

  Lemma check_complete {x t Γ}:
    Spec.mem x t Γ →
    ∃ p,
      x = varof p
      ∧ t = typeof p
      ∧ Γ = envof p
      ∧ Bool.Is_true (check p).
  Proof.
    intro q.
    induction q.
    all: cbn.
    - exists (mem_eq x t Γ).
      cbn.
      all: repeat split; auto.
    - destruct IHq as [p' [? [? []]]].
      exists (mem_ne x t Γ y t' p').
      cbn.
      subst.
      all: repeat split; auto.
      destruct (check p').
      2: contradiction.
      destruct eq_var.
      1: subst; contradiction.
      destruct eq_var, eq_type, eq_environment.
      all: cbv.
      all: auto.
  Qed.

  Function infer x Γ: option mem :=
    if Γ is cons (y, t') T
    then
      if eq_var x y
      then
        Some (mem_eq x t' T)
      else
        do p ← infer x T ;
        Some (mem_ne (varof p) (typeof p) (envof p) y t' p)
    else
      None.

  Lemma varof_infer {x Γ p}: infer x Γ = Some p → varof p = x.
  Proof.
    generalize dependent p.
    functional induction (infer x Γ).
    all: intros ? q.
    all: inversion q.
    all: auto.
    - assert (IHo' := IHo _ e1).
      cbn.
      auto.
  Qed.

  Lemma envof_infer {x Γ p}: infer x Γ = Some p → envof p = Γ.
  Proof.
    generalize dependent p.
    functional induction (infer x Γ).
    all: intros ? q.
    all: inversion q.
    all: auto.
    - assert (IHo' := IHo _ e1).
      cbn.
      subst.
      auto.
  Qed.

  Lemma infer_sound {x Γ p}:
    infer x Γ = Some p → Bool.Is_true (check p).
  Proof.
    generalize dependent p.
    induction Γ.
    1: discriminate.
    cbn.
    destruct a as [y t'].
    intro.
    destruct eq_var.
    - subst.
      intro q.
      inversion q.
      subst.
      cbn.
      auto.
    - destruct (infer x Γ) eqn:q.
      2: discriminate.
      rewrite (varof_infer q).
      intro q'.
      inversion q'.
      cbn.
      rewrite (varof_infer q).
      assert (IHΓ' := IHΓ _ eq_refl).
      destruct (check m).
      2: contradiction.
      destruct eq_environment.
      2: contradiction.
      destruct eq_type.
      2: contradiction.
      cbn.
      destruct eq_var.
      1: subst;contradiction.
      destruct eq_var.
      2: contradiction.
      auto.
  Qed.
End ProofTree.
