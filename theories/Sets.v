Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.SetoidClass.

Import IfNotations.

Import Nat.

Module Type SetInterface.
  Definition K: Set := nat.
  Axiom set: Set.

  Implicit Type k: K.
  Implicit Type m: set.

  Axiom empty: set.
  Axiom merge: ∀ m m', set.
  Axiom one: ∀ k, set.
  Axiom minus: ∀ k m, set.
  Axiom find: ∀ k m, bool.

    Axiom extensional:
      ∀ m m',
      (∀ k, find k m = find k m') → m = m'.

    Axiom find_empty:
      ∀ {k},
        find k empty = false.

    Axiom find_merge:
      ∀ {k m m'},
        find k (merge m m') = (find k m || find k m')%bool.

    Axiom find_one:
      ∀ {k k'},
      find k (one k') = if eq_dec k k' then true else false.

    Axiom find_minus:
      ∀ {k k' m},
      find k (minus k' m) = if eq_dec k k' then false else find k m.
End SetInterface.

Module FnSet: SetInterface with Definition K := nat.
  Definition K := nat.
  Definition set := K → bool.

  Implicit Type k: K.
  Implicit Type m: set.

  Definition empty: set := λ _, false.

  Definition merge m m' :=
    λ k,
      (m k || m' k) %bool.

  Definition one k: set :=
    λ k',
      if eq_dec k' k then true else false.

  Definition minus k m: set :=
    λ k',
      if eq_dec k' k
      then
        false
      else
        m k'.

  Definition find k m := m k.

  Lemma extensional {m m'}:
    (∀ k, find k m = find k m') → m = m'.
  Proof.
    intros.
    extensionality k.
    apply H.
  Qed.

  Lemma find_empty {k}: find k empty = false.
  Proof.
    auto.
  Qed.

  Lemma find_merge {k m m'}:
    find k (merge m m') = (find k m || find k m')%bool.
  Proof.
    auto.
  Qed.

  Lemma find_one {k k'}:
    find k (one k') = if eq_dec k k' then true else false.
  Proof.
    auto.
  Qed.

  Lemma find_minus {k k' m}:
    find k (minus k' m) = if eq_dec k k' then false else find k m.
  Proof.
    auto.
  Qed.
End FnSet.

Include FnSet.

Module Import SetNotations.
  Declare Scope set_scope.
  Bind Scope set_scope with set.
  Delimit Scope set_scope with set.

  Notation "∅" := empty: set_scope.
  Notation "m \ k" := (minus k m) (at level 30): set_scope.
  Infix "∪" := merge (at level 30): set_scope.
End SetNotations.

Implicit Type k: K.
Implicit Type m: set.

#[local]
 Lemma weaken {m m'}:
  m = m' →
  ∀ k, find k m = find k m'.
Proof.
  intros.
  subst.
  auto.
Qed.

Lemma find_add {k m}:
  find k (one k ∪ m) = true.
Proof.
  intros.
  rewrite find_merge.
  rewrite find_one.
  destruct eq_dec.
  2: contradiction.
  auto.
Qed.

Lemma add_add {k m}: merge (one k) (merge (one k) m) = merge (one k) m.
Proof.
  apply extensional.
  intro k'.
  repeat rewrite find_merge, find_one.
  destruct (eq_dec k' k) eqn:q.
  all: auto.
Qed.

Lemma merge_assoc {m0 m1 m2}: merge (merge m0 m1) m2 = merge m0 (merge m1 m2).
Proof.
  apply extensional.
  intro k.
  repeat rewrite find_merge.
  destruct (find k m0) eqn:q0, (find k m1) eqn:q1.
  all: auto.
Qed.

Lemma merge_empty_r {m}: merge m empty = m.
Proof.
  apply extensional.
  intro k.
  rewrite find_merge, find_empty.
  destruct (find k m) eqn:q.
  all: auto.
Qed.

Lemma merge_empty_l {m}: merge empty m = m.
Proof.
  apply extensional.
  intro k.
  rewrite find_merge, find_empty.
  destruct (find k m) eqn:q.
  all: auto.
Qed.

Lemma add_swap {m k k'}:
  k ≠ k' →
  merge (one k) (merge (one k') m) = merge (one k') (merge (one k) m).
Proof.
  intro p.
  apply extensional.
  intro k''.
  repeat rewrite find_merge, find_one.
  destruct (eq_dec k'' k'), (eq_dec k'' k).
  all: auto.
Qed.

Lemma add_minus {k m}:
  find k m = true →
  merge (one k) (minus k m) = m.
Proof.
  intro p.
  apply extensional.
  intro k'.
  rewrite find_merge, find_one, find_minus.
  destruct (eq_dec k' k).
  all: auto.
  subst.
  auto.
Qed.

Lemma minus_one {k}:
  minus k (one k) = empty.
Proof.
  apply extensional.
  intro k'.
  rewrite find_empty, find_minus, find_one.
  destruct (eq_dec k' k).
  - subst.
    reflexivity.
  - auto.
Qed.

Lemma minus_merge {k m m'}:
  minus k (merge m m') = merge (minus k m) (minus k m').
Proof.
  apply extensional.
  intro k'.
  repeat rewrite find_minus.
  repeat rewrite find_merge.
  repeat rewrite find_minus.
  destruct eq_dec.
  1: auto.
  auto.
Qed.

Lemma one_inj {k k'}:
  one k = one k' → k = k'.
Proof.
  intro p.
  set (p1 := weaken p k).
  set (p2 := weaken p k').
  repeat rewrite find_one in p1.
  repeat rewrite find_one in p2.
  destruct (eq_dec k k).
  2: contradiction.
  destruct (eq_dec k' k) eqn:q.
  - subst.
    destruct (eq_dec k k).
    2: contradiction.
    inversion p1.
    subst.
    split.
    all: auto.
  - subst.
    destruct  (eq_dec k' k').
    2: contradiction.
    discriminate.
Qed.

Lemma merge_empty {m m'}:
  merge m m' = empty → (m = empty ∧ m' = empty).
Proof.
  intros p.
  split.
  all: apply extensional.
  all: intro k'.
  all: set (p' := weaken p k').
  all: rewrite find_empty.
  all: rewrite find_merge in p'.
  all: rewrite find_empty in p'.
  all: destruct (find k' m), (find k' m').
  all: try discriminate.
  all: auto.
Qed.

Definition disjoint m m' :=
  ∀ k, find k m = false ∨ find k m' = false.

#[export]
 Instance disjoint_Symmetric: Symmetric disjoint.
Proof.
  intros m m' p k.
  destruct (p k).
  all: auto.
Qed.

Definition fst_disjoint {m0 m1 m2}:
  disjoint (m0 ∪ m1) m2 → disjoint m0 m2.
Proof.
  unfold disjoint.
  intros p k.
  set (p' := p k).
  rewrite find_merge in p'.
  destruct (find k m0) eqn:q0, (find k m2) eqn:q2.
  all: auto.
Qed.

Definition snd_disjoint {m0 m1 m2}:
  disjoint (m0 ∪ m1) m2 → disjoint m1 m2.
Proof.
  unfold disjoint.
  intros p k.
  set (p' := p k).
  rewrite find_merge in p'.
  destruct (find k m0) eqn:q0, (find k m1) eqn:q1, (find k m2) eqn:q2.
  all: auto.
Qed.
