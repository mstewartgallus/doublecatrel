Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Coq.Lists.List.

Import IfNotations.
Import List.ListNotations.

Module Type MapInterface.
  Axiom K: Set.
  Axiom map: Set → Set.

  Implicit Type k: K.

  Section Prim.
    Context {V: Set}.

    Implicit Type m: map V.
    Implicit Type v: V.

    Axiom empty: map V.
    Axiom merge: ∀ m m', map V.
    Axiom one: ∀ k v, map V.
    Axiom minus: ∀ k m, map V.
    Axiom find: ∀ k m, option V.
    Axiom disjoint: ∀ m m', Prop.

    Axiom add_minus:
      ∀ {k v m},
        find k m = Some v →
        (merge (one k v) (minus k m)) = m.
    Axiom find_add:
      ∀ {k v m},
        find k (merge (one k v) m) = Some v.
    Axiom add_add:
      ∀ {k m v v'},
        merge (one k v) (merge (one k v') m) = merge (one k v) m.

    Axiom merge_assoc:
      ∀ {m0 m1 m2}, merge (merge m0 m1) m2 = merge m0 (merge m1 m2).

    Axiom merge_empty_r:
      ∀ {m}, merge m empty = m.
    Axiom merge_empty_l:
      ∀ {m}, merge empty m = m.
    Axiom find_one_ne:
      ∀ {k k' v},
      k <> k' →
      find k (one k' v) = None.
  End Prim.
End MapInterface.

Module FnMap: MapInterface with Definition K := nat.
  Definition K := nat.
  Definition map (V: Set) := K → option V.

  Implicit Type k: K.

  Section Map.
    Context {V: Set}.

    Implicit Type m: map V.
    Implicit Type v: V.

    Definition empty: map V := λ _, None.

    Definition merge m m' :=
      λ k,
        if m k is Some v
        then
          Some v
        else
          m' k.

    Definition one k (v: V): map V :=
      λ k',
        if Nat.eq_dec k k'
        then
          Some v
        else
          None.

    Definition minus k m: map V :=
      λ k',
        if Nat.eq_dec k k'
        then
          None
        else
          m k'.

    Definition disjoint m m' :=
      ∀ k, m k = None ∨ m' k = None.

    Definition find k m := m k.

    Lemma add_minus {k v m}:
        find k m = Some v →
        (merge (one k v) (minus k m)) = m.
    Proof.
      unfold find.
      unfold merge, one, minus.
      intro p.
      extensionality n.
      destruct Nat.eq_dec.
      2: reflexivity.
      subst.
      rewrite p.
      reflexivity.
    Qed.

    Lemma find_add {k v m}:
        find k (merge (one k v) m) = Some v.
    Proof.
      intros.
      unfold find, merge, one, empty.
      destruct Nat.eq_dec.
      1: reflexivity.
      contradiction.
    Qed.

    Lemma add_add {k m v v'}: (merge (one k v) (merge (one k v') m)) = (merge (one k v) m).
    Proof.
      unfold merge, find, one, empty.
      extensionality k'.
      destruct Nat.eq_dec.
      all: reflexivity.
    Qed.

    Lemma merge_assoc {m0 m1 m2}: merge (merge m0 m1) m2 = merge m0 (merge m1 m2).
    Proof.
      unfold merge.
      extensionality k.
      destruct (m0 k).
      1: reflexivity.
      destruct (m1 k).
      1: reflexivity.
      reflexivity.
    Qed.

    Lemma merge_empty_r {m}: merge m empty = m.
    Proof.
      unfold merge, empty.
      extensionality k.
      destruct (m k).
      all: reflexivity.
    Qed.

    Lemma merge_empty_l {m}: merge empty m = m.
    Proof.
      unfold merge, empty.
      extensionality k.
      reflexivity.
    Qed.

    Lemma find_one_ne {k k' v}:
      k <> k' →
      find k (one k' v) = None.
    Proof.
      intros.
      unfold find, one.
      unfold empty.
      destruct Nat.eq_dec.
      1: subst.
      1: contradiction.
      reflexivity.
    Qed.
  End Map.
End FnMap.

Include FnMap.

Module MapNotations.
  Declare Scope map_scope.
  Bind Scope map_scope with map.
  Delimit Scope map_scope with map.

  Notation "∅" := empty: map_scope.
  Notation "m \ k" := (minus k m) (at level 30): map_scope.
  Infix "∪" := merge (at level 30): map_scope.

  Notation "x '↦' v" := (one x v) (at level 20): map_scope.
End MapNotations.
