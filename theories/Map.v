Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.SetoidClass.

Import IfNotations.

Module Type MapInterface.
  Definition K: Set := nat.
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

    Axiom extensional:
      ∀ m m',
      (∀ k, find k m = find k m') → m = m'.

    Axiom find_empty:
      ∀ {k},
        find k empty = None.

    Axiom find_merge:
      ∀ {k m m'},
        find k (merge m m') =
          if find k m is Some v
          then Some v
          else find k m'.

    Axiom find_one:
      ∀ {k k' v},
      find k (one k' v) = if Nat.eq_dec k k' then Some v else None.

    Axiom find_minus:
      ∀ {k k' m},
      find k (minus k' m) = if Nat.eq_dec k k' then None else find k m.
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
        if Nat.eq_dec k' k
        then
          Some v
        else
          None.

    Definition minus k m: map V :=
      λ k',
        if Nat.eq_dec k' k
        then
          None
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

    Lemma find_empty {k}: find k empty = None.
    Proof.
      auto.
    Qed.

    Lemma find_merge {k m m'}:
        find k (merge m m') =
          if find k m is Some v
          then Some v
          else find k m'.
    Proof.
      auto.
    Qed.

    Lemma find_one {k k' v}:
      find k (one k' v) = if Nat.eq_dec k k' then Some v else None.
    Proof.
      auto.
    Qed.

    Lemma find_minus {k k' m}:
      find k (minus k' m) = if Nat.eq_dec k k' then None else find k m.
    Proof.
      auto.
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

Section Map.
  Context {V: Set}.

  Import MapNotations.

  Implicit Type k: K.

  Implicit Type m: map V.
  Implicit Type v: V.

  #[local]
   Lemma weaken {m m'}:
    m = m' →
    ∀ k, find k m = find k m'.
  Proof.
    intros.
    subst.
    auto.
  Qed.

  Lemma one_inj_r {k v v'}:
    one k v = one k v' → v = v'.
  Proof.
    intro p.
    set (p' := weaken p k).
    repeat rewrite find_one in p'.
    destruct Nat.eq_dec.
    2: contradiction.
    inversion p'.
    auto.
  Qed.

  Lemma find_add {k v m}:
    find k (one k v ∪ m) = Some v.
  Proof.
    intros.
    rewrite find_merge.
    rewrite find_one.
    destruct Nat.eq_dec.
    2: contradiction.
    auto.
  Qed.

  Lemma add_add {k m v v'}: merge (one k v) (merge (one k v') m) = merge (one k v) m.
  Proof.
    apply extensional.
    intro k'.
    repeat rewrite find_merge, find_one.
    destruct (Nat.eq_dec k' k) eqn:q.
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

  Lemma add_inj {m k v v'}:
    merge (one k v) m = merge (one k v') m → v = v'.
  Proof.
    intro p.
    set (p' := weaken p k).
    repeat rewrite Map.find_merge in p'.
    repeat rewrite Map.find_one in p'.
    destruct (Nat.eq_dec k k).
    2: contradiction.
    inversion p'.
    subst.
    auto.
  Qed.

  Lemma add_swap {m k k' v v'}:
    k ≠ k' →
    merge (one k v) (merge (one k' v') m) = merge (one k' v') (merge (one k v) m).
  Proof.
    intro p.
    apply extensional.
    intro k''.
    repeat rewrite find_merge, find_one.
    destruct (Nat.eq_dec k'' k'), (Nat.eq_dec k'' k).
    all: auto.
    subst.
    contradiction.
  Qed.

  Lemma add_minus {k v m}:
    find k m = Some v →
    merge (one k v) (minus k m) = m.
  Proof.
    intro p.
    apply extensional.
    intro k'.
    rewrite find_merge, find_one, find_minus.
    destruct (Nat.eq_dec k' k).
    all: auto.
    subst.
    auto.
  Qed.

  Lemma minus_one {k v}:
    minus k (one k v) = empty.
  Proof.
    apply extensional.
    intro k'.
    rewrite find_empty, find_minus, find_one.
    destruct (Nat.eq_dec k' k).
    - subst.
      reflexivity.
    - auto.
  Qed.

  Lemma one_inj {k v k' v'}:
    one k v = one k' v' → (k = k' ∧ v = v').
  Proof.
    intro p.
    set (p1 := weaken p k).
    set (p2 := weaken p k').
    repeat rewrite find_one in p1.
    repeat rewrite find_one in p2.
    destruct (Nat.eq_dec k k).
    2: contradiction.
    destruct (Nat.eq_dec k' k) eqn:q.
    - subst.
      destruct (Nat.eq_dec k k).
      2: contradiction.
      inversion p1.
      subst.
      split.
      all: auto.
    - subst.
      destruct  (Nat.eq_dec k' k').
      2: contradiction.
      discriminate.
  Qed.

  Lemma merge_empty {m m'}:
    merge m m' = empty → (m = empty ∧ m' = empty).
  Proof.
    intros p.
    split.
    all: apply Map.extensional.
    all: intro k'.
    all: set (p' := weaken p k').
    all: rewrite Map.find_empty.
    all: rewrite Map.find_merge in p'.
    all: rewrite Map.find_empty in p'.
    all: destruct (Map.find k' m), (Map.find k' m').
    all: try discriminate.
    all: auto.
  Qed.

  Definition disjoint m m' :=
    ∀ k, find k m = None ∨ find k m' = None.

  #[export]
  Instance disjoint_Symmetric: Symmetric disjoint.
  Proof.
    intros m m' p k.
    destruct (p k).
    all: auto.
  Qed.

  Definition fst_disjoint {m0 m1 m2}:
    Map.disjoint (m0 ∪ m1) m2 → Map.disjoint m0 m2.
  Proof.
    unfold disjoint.
    intros p k.
    set (p' := p k).
    rewrite find_merge in p'.
    destruct (find k m0) eqn:q0, (find k m2) eqn:q2.
    all: auto.
  Qed.

  Definition snd_disjoint {m0 m1 m2}:
    Map.disjoint (m0 ∪ m1) m2 → Map.disjoint m1 m2.
  Proof.
    unfold disjoint.
    intros p k.
    set (p' := p k).
    rewrite find_merge in p'.
    destruct (find k m0) eqn:q0, (find k m1) eqn:q1, (find k m2) eqn:q2.
    all: auto.
    destruct p'.
    all: discriminate.
  Qed.
End Map.
