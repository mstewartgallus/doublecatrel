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

    Axiom extensional:
      ∀ m m',
      (∀ k, find k m = find k m') → m = m'.

    Axiom find_empty:
      ∀ {k},
        find k empty = None.

    Axiom find_merge_l:
      ∀ {k v m m'},
        find k m = Some v →
        find k (merge m m') = Some v.
    Axiom find_merge_r:
      ∀ {k e m m'},
        find k m = None →
        find k m' = e →
        find k (merge m m') = e.

    Axiom find_one:
      ∀ {k v},
      find k (one k v) = Some v.
    Axiom find_one_ne:
      ∀ {k k' v},
      k <> k' →
      find k (one k' v) = None.

    Axiom one_inj:
      ∀ {k v k' v'}, one k v = one k' v' → (k = k' ∧ v = v').

    Axiom add_minus:
      ∀ {k v m},
        find k m = Some v →
        (merge (one k v) (minus k m)) = m.

    Axiom minus_one:
      ∀ {k v},
      minus k (one k v) = empty.
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

    Definition find k m := m k.

    Lemma extensional {m m'}:
      (∀ k, find k m = find k m') → m = m'.
    Proof.
      intros.
      extensionality k.
      apply H.
    Qed.

    Lemma find_merge_l {k v m m'}:
        find k m = Some v →
        find k (merge m m') = Some v.
    Proof.
      unfold find, merge.
      intro p.
      rewrite p.
      auto.
    Qed.

    Lemma find_merge_r {k e m m'}:
        find k m = None →
        find k m' = e →
        find k (merge m m') = e.
    Proof.
      unfold find, merge.
      intros p q.
      rewrite p.
      auto.
    Qed.

    Lemma find_one {k v}:
      find k (one k v) = Some v.
    Proof.
      unfold find, one.
      destruct Nat.eq_dec.
      2: contradiction.
      auto.
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

    Lemma find_empty {k}:
      find k empty = None.
    Proof.
      unfold find, empty.
      reflexivity.
    Qed.

    #[local]
    Lemma weaken {A B} {f f': A -> B}:
      f = f' → ∀ x, f x = f' x.
    Proof.
      intros.
      subst.
      reflexivity.
    Qed.

    Lemma one_inj {k v k' v'}:
      one k v = one k' v' → (k = k' ∧ v = v').
    Proof.
      intro p.
      destruct (Nat.eq_dec k k) eqn:q,  (Nat.eq_dec k' k') eqn:q'.
      all: try contradiction.
      set (p' := weaken p k').
      unfold one in p'.
      rewrite q' in p'.
      destruct Nat.eq_dec in p'.
      2: discriminate.
      inversion p'.
      subst.
      auto.
    Qed.

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

    Lemma minus_one {k v}:
      minus k (one k v) = empty.
    Proof.
      unfold minus, one, empty.
      extensionality k'.
      destruct Nat.eq_dec.
      all: auto.
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

  Definition disjoint m m' :=
    ∀ k, find k m = None ∨ find k m' = None.

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
    inversion p'.
    auto.
  Qed.

  Lemma find_add {k v m}:
    find k (merge (one k v) m) = Some v.
  Proof.
    intros.
    erewrite find_merge_l.
    2: rewrite find_one.
    all: eauto.
  Qed.

  Lemma add_add {k m v v'}: merge (one k v) (merge (one k v') m) = merge (one k v) m.
  Proof.
    apply extensional.
    intro k'.
    destruct (Nat.eq_dec k k') eqn:q.
    - subst.
      repeat rewrite find_add.
      reflexivity.
    - erewrite find_merge_r.
      2: {
        rewrite find_one_ne.
        all: auto.
      }
      1: {
        erewrite find_merge_r.
        3: reflexivity.
        2: rewrite find_one_ne.
        all: auto.
      }
      erewrite find_merge_r.
      2: {
        rewrite find_one_ne.
        all: auto.
      }
      2: reflexivity.
      reflexivity.
  Qed.

  Lemma merge_assoc {m0 m1 m2}: merge (merge m0 m1) m2 = merge m0 (merge m1 m2).
  Proof.
    apply extensional.
    intro k.
    destruct (find k m0) eqn:q0.
    - erewrite find_merge_l.
      2: erewrite find_merge_l.
      3: apply q0.
      2: reflexivity.
      erewrite find_merge_l.
      2: apply q0.
      auto.
    - destruct (find k m1) eqn:q1.
      + erewrite find_merge_l.
        2: erewrite find_merge_r.
        3: auto.
        3: apply q1.
        2: reflexivity.
        erewrite find_merge_r.
        2: auto.
        2: erewrite find_merge_l.
        3: apply q1.
        2: reflexivity.
        auto.
      + erewrite find_merge_r.
        2: erewrite find_merge_r.
        3: auto.
        all: eauto.
        erewrite find_merge_r.
        2: apply q0.
        1: reflexivity.
        erewrite find_merge_r.
        all: eauto.
  Qed.

  Lemma merge_empty_r {m}: merge m empty = m.
  Proof.
    apply extensional.
    intro k.
    destruct (find k m) eqn:q.
    - erewrite find_merge_l.
      all: eauto.
    - erewrite find_merge_r.
      all: eauto.
      rewrite find_empty.
      auto.
  Qed.

  Lemma merge_empty_l {m}: merge empty m = m.
  Proof.
    apply extensional.
    intro k.
    destruct (find k m) eqn:q.
    - erewrite find_merge_r.
      all: eauto.
      rewrite find_empty.
      auto.
    - erewrite find_merge_r.
      all: eauto.
      rewrite find_empty.
      auto.
  Qed.

  Lemma add_swap {m k k' v v'}:
    k ≠ k' →
    merge (one k v) (merge (one k' v') m) = merge (one k' v') (merge (one k v) m).
  Proof.
    intro p.
    apply extensional.
    intro k''.
    destruct (Nat.eq_dec k k'').
    - subst.
      rewrite find_add.
      erewrite find_merge_r.
      1: reflexivity.
      1: rewrite find_one_ne.
      1: reflexivity.
      1: auto.
      rewrite find_add.
      reflexivity.
    - erewrite find_merge_r.
      2: rewrite find_one_ne.
      all: auto.
      destruct (Nat.eq_dec k' k'').
      + subst.
        rewrite find_add.
        rewrite find_add.
        reflexivity.
      + erewrite find_merge_r.
        1: reflexivity.
        rewrite find_one_ne.
        1: reflexivity.
        1: auto.
        erewrite find_merge_r.
        2: rewrite find_one_ne.
        all: auto.
        erewrite find_merge_r.
        2: rewrite find_one_ne.
        all: auto.
  Qed.
End Map.
