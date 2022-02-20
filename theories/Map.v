Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.

Import IfNotations.

Section Map.
  Context {V: Type}.

  Definition map := nat → option V.

  Definition find n (m: map): option V := m n.
  Definition empty: map := λ _, None.

  Definition put (n: nat) (v: option V) (m: map): map :=
    λ n',
      if Nat.eq_dec n n'
      then
        v
      else
        find n' m.

  Definition add n (v: V) := put n (Some v).
  Definition minus (n: nat): map → _ := put n None.

  Definition one (x: nat) (v: V) := add x v empty.

  Definition merge (m m': map) :=
    λ n,
      if find n m is Some v
      then
        Some v
      else
        find n m'.

  Fixpoint add_list (kv: list (nat * V)) (m: map): map :=
    if kv is cons (k, v) t
    then
      add k v (add_list t m)
    else
      m.

  Definition of_list (kv: list (nat * V)) := add_list kv empty.

  Definition disjoint (f g: map) :=
    ∀ x, f x = None \/ g x = None.

  Lemma add_minus:
    ∀ x (t: V) Γ,
      find x Γ = Some t →
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

  Lemma find_add:
    ∀ x (t: V) Γ,
      find x (add x t Γ) = Some t.
  Proof.
    intros x.
    intros.
    unfold find, add, put.
    destruct Nat.eq_dec.
    1: reflexivity.
    contradiction.
  Qed.

  Lemma add_add:
    ∀ x (s t: V) Γ,
      add x s (add x t Γ) = add x s Γ.
  Proof.
    intros.
    unfold add, put, find.
    extensionality n.
    destruct Nat.eq_dec.
    all: reflexivity.
  Qed.

  Lemma merge_assoc:
    ∀ A B C,
      merge (merge A B) C = merge A (merge B C).
  Proof.
    intros.
    extensionality n.
    unfold merge, find.
    destruct (A n).
    1: reflexivity.
    destruct (B n).
    1: reflexivity.
    reflexivity.
  Qed.

  Lemma merge_empty_r:
    ∀ (Γ: map),
      merge Γ empty = Γ.
  Proof.
    intros.
    extensionality n.
    unfold merge, find, empty.
    destruct (Γ n).
    all: reflexivity.
  Qed.

  Lemma merge_empty_l:
    ∀ (Γ: map),
      merge empty Γ = Γ.
  Proof.
    intros.
    unfold merge, empty, find.
    extensionality n.
    reflexivity.
  Qed.

  Lemma find_one_ne:
    ∀ {x x'} {t: V},
      x <> x' →
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
End Map.

Arguments map: clear implicits.

Module MapNotations.
  Notation "m \ k" := (minus k m) (at level 30).
  Infix "∪" := merge (at level 30).
End MapNotations.
