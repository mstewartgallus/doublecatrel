Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.

Import IfNotations.

Definition map V := nat -> option V.

Definition find {V} (n: nat) (m: map V): option V := m n.
Definition empty {V}: map V := fun _ => None.

Definition put {V} (n: nat) (v: option V) (m: map V): map V := fun n' =>
  if Nat.eq_dec n n'
  then
    v
  else
    find n' m.

Definition add {V} n (v: V) := put n (Some v).
Definition minus {V} (n: nat): map V -> _ := put n None.

Definition one {V} (x: nat) (v: V) := add x v empty.

Definition merge {V} (m m': map V) :=
  fun n =>
    if find n m is Some v
    then
      Some v
    else
      find n m'.

Fixpoint add_list {V} (kv: list (nat * V)) (m: map V): map V :=
  if kv is cons (k, v) t
  then
    add k v (add_list t m)
  else
    m.

Definition of_list {V} (kv: list (nat * V)) := add_list kv empty.

Lemma add_minus {V}:
  forall x (t: V) Γ,
    find x Γ = Some t ->
    add x t (minus x Γ) = Γ.
Proof.
  intros ? ? ? p.
  extensionality n.
  unfold add, minus.
  unfold put.
  unfold find in p.
  unfold find.
  destruct Nat.eq_dec.
  2: reflexivity.
  subst.
  rewrite p.
  reflexivity.
Qed.

Lemma find_add {V}:
  forall x (t: V) Γ,
    find x (add x t Γ) = Some t.
Proof.
  intros x.
  intros.
  unfold find, add, put.
  destruct Nat.eq_dec.
  1: reflexivity.
  contradiction.
Qed.

Lemma add_add {V}:
  forall x (s t: V) Γ,
    add x s (add x t Γ) = add x s Γ.
Proof.
  intros.
  unfold add, put, find.
  extensionality n.
  destruct Nat.eq_dec.
  all: reflexivity.
Qed.

Lemma merge_empty_r {V}:
  forall (Γ: map V),
    merge Γ empty = Γ.
Proof.
  intros.
  extensionality n.
  unfold merge, find, empty.
  destruct (Γ n).
  all: reflexivity.
Qed.

Lemma merge_empty_l {V}:
  forall (Γ: map V),
    merge empty Γ = Γ.
Proof.
  intros.
  unfold merge, empty, find.
  extensionality n.
  reflexivity.
Qed.

Lemma find_one_ne {V}:
  forall {x x'} {t: V},
    x <> x' ->
    find x (one x' t) = None.
Proof.
  intros.
  unfold find, one.
  unfold add.
  unfold put, empty.
  destruct Nat.eq_dec.
  1: subst.
  1: contradiction.
  unfold find.
  reflexivity.
Qed.
