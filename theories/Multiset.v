Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.SetoidClass.

Import IfNotations.

Import Nat.

Module Type MultisetInterface.
  Definition K: Set := nat.
  Axiom multiset: Set.

  Implicit Type k: K.
  Implicit Type m: multiset.

  Axiom empty: multiset.
  Axiom merge: ∀ m m', multiset.
  Axiom one: ∀ k, multiset.
  Axiom minus: ∀ k m, multiset.
  Axiom find: ∀ k m, nat.

  Axiom extensional:
    ∀ m m',
      (∀ k, find k m = find k m') → m = m'.

  Axiom find_empty:
    ∀ {k},
      find k empty = 0.

  Axiom find_merge:
    ∀ {k m m'},
      find k (merge m m') = find k m + find k m'.

  Axiom find_one:
    ∀ {k k'},
      find k (one k') = if eq_dec k k' then 1 else 0.

  Axiom find_minus:
    ∀ {k k' m},
      find k (minus k' m) =
        if eq_dec k k'
        then
          match find k m with
          | O => O
          | S n' => n'
          end
        else
          find k m.
End MultisetInterface.

Module FnSet: MultisetInterface with Definition K := nat.
  Definition K := nat.
  Definition multiset := K → nat.

  Implicit Type k: K.
  Implicit Type m: multiset.

  Definition empty: multiset := λ _, 0.
  Definition merge m m' := λ k, m k + m' k.
  Definition one k: multiset :=
    λ k', if eq_dec k' k then 1 else 0.

  Definition minus k m: multiset :=
    λ k',
      if eq_dec k' k
      then
        match m k' with
        | O => O
        | S n' => n'
        end
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

  Lemma find_empty {k}: find k empty = 0.
  Proof.
    auto.
  Qed.

  Lemma find_merge {k m m'}:
    find k (merge m m') = find k m + find k m'.
  Proof.
    auto.
  Qed.

  Lemma find_one {k k'}:
    find k (one k') = if eq_dec k k' then 1 else 0.
  Proof.
    auto.
  Qed.

  Lemma find_minus {k k' m}:
    find k (minus k' m) =
      if eq_dec k k'
      then
        match find k m with
        | O => O
        | S n' => n'
        end
      else find k m.
  Proof.
    auto.
  Qed.
End FnSet.

Include FnSet.

Module Import MultisetNotations.
  Declare Scope multiset_scope.
  Bind Scope multiset_scope with multiset.
  Delimit Scope multiset_scope with multiset.

  Notation "∅" := empty: multiset_scope.
  Notation "m \ k" := (minus k m) (at level 30): multiset_scope.
  Infix "∪" := merge (at level 30): multiset_scope.
End MultisetNotations.

Implicit Type k: K.
Implicit Type m: multiset.

#[local]
 Lemma weaken {m m'}:
  m = m' →
  ∀ k, find k m = find k m'.
Proof.
  intros.
  subst.
  auto.
Qed.

Lemma merge_assoc {m0 m1 m2}: merge (merge m0 m1) m2 = merge m0 (merge m1 m2).
Proof.
  apply extensional.
  intro k.
  repeat rewrite find_merge.
  destruct (find k m0) eqn:q0, (find k m1) eqn:q1.
  all: auto.
  rewrite Nat.add_assoc.
  auto.
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
  merge (one k) (merge (one k') m) = merge (one k') (merge (one k) m).
Proof.
  apply extensional.
  intro k''.
  repeat rewrite find_merge, find_one.
  destruct (eq_dec k'' k'), (eq_dec k'' k).
  all: auto.
Qed.

Lemma add_minus {k m}:
  find k m > 0 →
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
  destruct (find k m).
  1: inversion p.
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

Lemma one_inj {k k'}:
  one k = one k' → k = k'.
Proof.
  intro p.
  assert (p1 := weaken p k).
  assert (p2 := weaken p k').
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
  all: assert (p' := weaken p k').
  all: rewrite find_empty.
  all: rewrite find_merge in p'.
  all: rewrite find_empty in p'.
  all: destruct (find k' m), (find k' m').
  all: try discriminate.
  all: auto.
Qed.

Definition disjoint m m' :=
  ∀ k, find k m = 0 ∨ find k m' = 0.

#[export]
 Instance disjoint_Symmetric: Symmetric disjoint.
Proof.
  intros m m' p k.
  destruct (p k).
  all: auto.
Qed.
