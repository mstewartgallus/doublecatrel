Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Coq.Lists.List.

Import IfNotations.
Import List.ListNotations.

Definition map V := nat → option V.

Implicit Type k: nat.

Section Prim.
  Context {V: Type}.

  Implicit Type m: map V.

  Definition find k m := m k.

  Definition empty: map V := λ _, None.

  Definition merge m m' :=
    λ k,
      if find k m is Some v
      then
        Some v
      else
        find k m'.

  Definition one k (v: V): map V :=
    λ k',
      if Nat.eq_dec k k'
      then
        Some v
      else
        None.

  Definition put k (v: option V) m: map V :=
    λ k',
      if Nat.eq_dec k k'
      then
        v
      else
        find k' m.

  Definition minus k := put k None.

  Definition disjoint m m' :=
    ∀ k, m k = None \/ m' k = None.
End Prim.

Module Import MapNotations.
  Declare Scope map_scope.
  Bind Scope map_scope with map.
  Delimit Scope map_scope with map.

  Notation "∅" := empty: map_scope.
  Notation "m \ k" := (minus k m) (at level 30): map_scope.
  Infix "∪" := merge (at level 30): map_scope.

  Notation "x '↦' v" := (one x v) (at level 20): map_scope.
End MapNotations.

Section Map.
  Context {V: Type}.

  Implicit Type m: map V.
  Implicit Type v: V.

  Open Scope map.

  Fixpoint add_list kv m :=
    if kv is ((k, v) :: t)%list
    then
      k ↦ v ∪ add_list t m
    else
      m.

  Definition of_list kv := add_list kv empty.

  Lemma add_minus:
    ∀ {k v m},
      find k m = Some v →
      (k ↦ v ∪ (m \ k)) = m.
  Proof.
    intros ? ? ? p.
    extensionality n.
    unfold merge, one, minus, empty.
    unfold put.
    unfold find in p.
    unfold find.
    destruct Nat.eq_dec.
    2: reflexivity.
    subst.
    rewrite p.
    reflexivity.
  Qed.

  Lemma find_add:
    ∀ {k v m},
      find k (k ↦ v ∪ m) = Some v.
  Proof.
    intros.
    unfold find, merge, one, put, empty, find.
    destruct Nat.eq_dec.
    1: reflexivity.
    contradiction.
  Qed.

  Lemma add_add {k m v v'}: (k ↦ v ∪ k ↦ v' ∪ m) = (k ↦ v ∪ m).
  Proof.
    unfold merge, put, find, one, put, empty.
    extensionality k'.
    destruct Nat.eq_dec.
    all: reflexivity.
  Qed.

  Lemma merge_assoc {m0 m1 m2}: (m0 ∪ m1) ∪ m2 = m0 ∪ (m1 ∪ m2).
  Proof.
    extensionality k.
    unfold merge, find.
    destruct (m0 k).
    1: reflexivity.
    destruct (m1 k).
    1: reflexivity.
    reflexivity.
  Qed.

  Lemma merge_empty_r {m}: m ∪ ∅ = m.
  Proof.
    extensionality k.
    unfold merge, find, empty.
    destruct (m k).
    all: reflexivity.
  Qed.

  Lemma merge_empty_l {m}: ∅ ∪ m = m.
  Proof.
    intros.
    unfold merge, empty, find.
    extensionality k.
    reflexivity.
  Qed.

  Lemma find_one_ne {k k' v}:
      k <> k' →
      find k (one k' v) = None.
  Proof.
    intros.
    unfold find, one.
    unfold put, empty.
    destruct Nat.eq_dec.
    1: subst.
    1: contradiction.
    unfold find.
    reflexivity.
  Qed.
End Map.
