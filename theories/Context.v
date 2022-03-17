Require Blech.Map.
Require Import Blech.Opaque.
Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.Environment.
Require Import Blech.Category.
Require Blech.OptionNotations.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Arith.PeanoNat.
Require Coq.Lists.List.

Require Import FunInd.
Require Import Psatz.

Import List.ListNotations.
Import IfNotations.

Implicit Type Γ: environment.
Implicit Type Δ: usage.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types x y: var.
Implicit Type xs: vars.
Implicit Type σ: store.

Import Map.MapNotations.

Definition eq_usage Δ Δ': {Δ = Δ'} + {Δ ≠ Δ'}.
Proof.
  set (s := eq_use).
  decide equality.
Defined.

Lemma length_mt {n}: length (mt n) = n.
Proof.
  induction n.
  1: auto.
  cbn.
  rewrite IHn.
  auto.
Qed.

Fixpoint one x Γ: option usage :=
  if Γ is cons (y, t) T
  then
    if eq_var x y
    then
      Some (cons u_used (mt (length T)))
    else
      if one x T is Some T'
      then
        Some (cons u_unused T')
      else
        None
  else
    None.

Lemma find_one {x Γ t}: find x Γ = Some t → { ns & one x Γ = Some ns }.
Proof.
  induction Γ.
  1: discriminate.
  intros p.
  cbn in *.
  destruct a.
  destruct eq_var.
  all: subst.
  - exists (cons u_used (mt (length Γ))).
    auto.
  - destruct (IHΓ p).
    rewrite e.
    exists (cons u_unused x0).
    auto.
Defined.

Lemma length_merge_eq {ns ns'}:
  length ns = length ns' →
  length (merge ns ns') = length ns.
Proof.
  generalize dependent ns'.
  induction ns.
  all: cbn.
  - intros ns' p.
    destruct ns'.
    all: cbn in *.
    all: auto.
    discriminate.
  - intros ns' p.
    destruct ns'.
    all: cbn.
    all: auto.
    discriminate.
Qed.

Lemma length_xsof {Γ}: length (xsof Γ) = length Γ.
Proof.
  induction Γ.
  1: auto.
  destruct a.
  cbn.
  rewrite IHΓ.
  auto.
Qed.

Lemma length_same_lmem_l {x xs Δ Δ'}: lmem x xs Δ Δ' → length xs = length Δ.
Proof.
  intro p.
  induction p.
  all: cbn.
  all: auto.
Qed.

Lemma length_same_lmem_r {x xs Δ Δ'}: lmem x xs Δ Δ' → length xs = length Δ'.
Proof.
  intro p.
  induction p.
  all: cbn.
  all: auto.
Qed.

Lemma length_same_l {Γ Δ Δ' E t}: JE Γ Δ Δ' E t → length Γ = length Δ.
Proof.
  intro p.
  induction p.
  all: cbn.
  all: auto.
  - assert (H0' := length_same_lmem_l H0).
    symmetry in H0'.
    symmetry.
    rewrite H0'.
    rewrite length_xsof.
    auto.
Qed.

Lemma length_same_r {Γ Δ Δ' E t}: JE Γ Δ Δ' E t → length Γ = length Δ'.
Proof.
  intro p.
  induction p.
  all: cbn.
  all: auto.
  - assert (H0' := length_same_lmem_r H0).
    symmetry in H0'.
    symmetry.
    rewrite H0'.
    rewrite length_xsof.
    auto.
  - cbn in IHp2.
    inversion IHp2.
    auto.
Qed.

Section Typecheck.
  Import OptionNotations.

  Function lookup x Γ Δ :=
    match Γ, Δ with
    | cons (y, t) Γ', cons u Δ' =>
        if eq_var x y
        then
          if u is u_unused
          then
            if Nat.eq_dec (length Γ') (length Δ')
            then
              Some (cons u_used Δ', t)
            else
              None
          else
            None
        else
          do (Δ'', t)  ← lookup x Γ' Δ' ;
          Some (cons u Δ'', t)
    | _, _ => None
    end.

  Function typecheck Γ Δ E: option (usage * type) :=
    match E with
    | E_var x => lookup x Γ Δ
    | E_lam x t1 E =>
        do (u_used :: Δ', t2) ← typecheck ((x, t1) :: Γ) (u_unused :: Δ) E ;
        Some (Δ', t1 * t2)
    | E_app E E' =>
        do (Δ1, t1 * t2) ← typecheck Γ Δ E ;
        do (Δ2, t1') ← typecheck Γ Δ1 E' ;
        if eq_type t1 t1'
        then
          Some (Δ2, t2)
        else
          None

    | E_tt =>
        if Nat.eq_dec (length Γ) (length Δ)
        then
          Some (Δ, t_unit)
        else
          None
    | E_step E E' =>
        do (Δ1, t_unit) ← typecheck Γ Δ E ;
        do (Δ2, t) ← typecheck Γ Δ1 E' ;
        Some (Δ2, t)

    | E_fanout E E' =>
        do (Δ1, t1) ← typecheck Γ Δ E ;
        do (Δ2, t2) ← typecheck Γ Δ1 E' ;
        Some (Δ2, t1 * t2)

    | E_let x y E E' =>
        do (Δ1, t1 * t2) ← typecheck Γ Δ E ;
        do (u_used :: u_used :: Δ2, t3) ← typecheck ((y, t2) :: (x, t1) :: Γ) (u_unused :: u_unused :: Δ1) E' ;
        Some (Δ2, t3)
    end
      %list.
End Typecheck.

Theorem typecheck_sound:
  ∀ Γ {E Δ Δ' t}, typecheck Γ Δ E = Some (Δ', t) → JE Γ Δ Δ' E t.
Proof using.
  intros Γ E Δ.
  functional induction (typecheck Γ Δ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: clear p.
  all: econstructor; eauto.
  - generalize dependent Δ'.
    functional induction (lookup x Γ Δ).
    all: cbn.
    all: intros ? p.
    all: inversion p.
    all: subst.
    all: constructor.
    all: eauto.
  - generalize dependent Δ'.
    functional induction (lookup x Γ Δ).
    all: cbn.
    all: intros ? p.
    all: inversion p.
    all: subst.
    all: constructor.
    all: eauto.
    rewrite length_xsof.
    auto.
Qed.

Theorem typecheck_complete:
  ∀ Γ {E Δ Δ' t}, JE Γ Δ Δ' E t → typecheck Γ Δ E = Some (Δ', t).
Proof using.
  intros ? ? ? ? ? p.
  induction p.
  all: cbn.
  all: try rewrite IHp.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: auto.
  - generalize dependent Δ'.
    generalize dependent Δ.
    induction H.
    all: cbn.
    all: intros ? ? q.
    all: inversion q.
    all: subst.
    all: cbn.
    all: try contradiction.
    all: destruct eq_var.
    all: try contradiction.
    + rewrite <- H1.
      rewrite length_xsof.
      destruct Nat.eq_dec.
      2: contradiction.
      auto.
    + rewrite (IHmem _ _ H7).
      auto.
  - destruct eq_type.
    2: contradiction.
    auto.
  - destruct Nat.eq_dec.
    2: contradiction.
    auto.
Qed.

Notation "'do' n ← e0 ; e1" :=
  (List.flat_map (λ n, e1) e0)
    (n pattern, at level 200, left associativity): list_scope.

Fixpoint generate t: list normal :=
  match t with
  | t_unit => [N_tt]
  | t * t' =>
      do N ← generate t ;
      do N' ← generate t' ;
      [N_fanout N N']
  end%list.

Fixpoint search σ E: list span :=
  match E with
  | E_var x => if Map.find x σ is Some N then [x ↦ N |- N] else []

  | E_lam x t E =>
      do N0 ← generate t ;
      do (σ' |- N1) ← search (x ↦ N0 ∪ σ) E ;
      if Map.find x σ' is Some N0'
      then
        if eq_normal N0 N0'
        then
          [σ' \ x |- N_fanout N0 N1]
        else
          []
      else
        []

  | E_app E E' =>
      do (σ1 |- N) ← search σ E ;
      do (σ2 |- N0) ← search σ E' ;
      if N is N_fanout N0' N1
      then
        if eq_normal N0 N0'
        then
          [σ1 ∪ σ2 |- N1]
        else
          []
      else
        []

  | E_tt => [∅ |- N_tt]

  | E_step E E' =>
      do (σ1 |- N) ← search σ E ;
      do (σ2 |- N') ← search σ E' ;
      if N is N_tt
      then
        [σ1 ∪ σ2 |- N']
      else
        []

  | E_fanout E E' =>
      do (σ1 |- N) ← search σ E ;
      do (σ2 |- N') ← search σ E' ;
      [σ1 ∪ σ2 |- N_fanout N N']

  | E_let x y E E' =>
      do (σ1 |- N) ← search σ E ;
      do (a, b) ← (if N is N_fanout a b then [(a, b)] else []) ;
      do (σ2 |- N') ← search ((x ↦ a) ∪ (y ↦ b) ∪ σ) E' ;
      match Map.find x (σ2 \ y), Map.find y σ2 with
      | Some a', Some b' =>
          if eq_normal a a'
          then
            if eq_normal b b'
            then
              [σ1 ∪ ((σ2 \ y) \ x) |- N']
            else
              []
          else
            []
      | _, _ => []
      end
  end%list %map.

Lemma sound_pure:
  ∀ {σ E N}, sat σ E N → sound E ([σ |- N]%list).
Proof.
  repeat constructor.
  auto.
Defined.

Lemma sound_mon {E p p'}:
  sound E p → sound E p' →
  sound E ((p ++ p')%list).
Proof.
  intros.
  induction p.
  1: auto.
  cbn.
  inversion H.
  constructor.
  all: auto.
Defined.

Theorem search_sound:
  ∀ σ E, sound E (search σ E).
Proof using.
  Open Scope map.
  intros σ E.
  generalize dependent σ.
  induction E.
  all: intros.
  - cbn.
    destruct Map.find eqn:q.
    2: constructor.
    apply sound_pure.
    constructor.
  - cbn.
    induction (generate t).
    1: cbn.
    1: constructor.
    cbn in *.
    apply sound_mon.
    2: auto.
    clear IHl.
    induction (IHE (x ↦ a ∪ σ)).
    1: constructor.
    cbn.
    destruct Map.find eqn:q.
    2: auto.
    destruct (eq_normal a n).
    2: auto.
    subst.
    constructor.
    1: auto.
    constructor.
    rewrite Map.add_minus.
    all: auto.
  - cbn.
    induction (IHE1 σ).
    1: constructor.
    cbn.
    apply sound_mon.
    2: auto.
    clear IHs.
    induction (IHE2 σ).
    1: constructor.
    cbn in *.
    destruct N.
    1: auto.
    destruct (eq_normal N0 N1).
    2: cbn.
    2: auto.
    cbn.
    subst.
    constructor.
    1: auto.
    econstructor.
    all: eauto.
  - all: repeat constructor.
  - cbn.
    induction (IHE1 σ).
    1: constructor.
    cbn.
    apply sound_mon.
    2: auto.
    clear IHs.
    induction (IHE2 σ).
    1: constructor.
    cbn.
    destruct N.
    2: auto.
    constructor.
    1: auto.
    constructor.
    all: auto.
  - cbn.
    induction (IHE1 σ).
    1: constructor.
    cbn.
    apply sound_mon.
    2: auto.
    clear IHs.
    induction (IHE2 σ).
    1: constructor.
    cbn.
    constructor.
    1: auto.
    econstructor.
    all: eauto.
  - cbn.
    induction (IHE1 σ).
    1: constructor.
    apply sound_mon.
    2: auto.
    clear IHs.
    destruct N.
    1: constructor.
    cbn.
    rewrite List.app_nil_r.
    induction (IHE2 (((x ↦ N1 ∪ y ↦ N2) ∪ σ))).
    1: constructor.
    cbn.
    destruct (Map.find x (σ1 \ y)) eqn:q.
    2: auto.
    destruct (Map.find y σ1) eqn:q'.
    2: auto.
    destruct (eq_normal N1 n).
    2: auto.
    subst.
    destruct (eq_normal N2 n0).
    2: auto.
    subst.
    cbn.
    constructor.
    1: auto.
    econstructor.
    all: eauto.
    all: repeat rewrite Map.add_minus.
    all: eauto.
    all: cbn.
Qed.

(* FIXME type check *)
Record span := {
  s: Set ;
  π1: s → store ;
  π2: s → normal ;
}.

Definition satspan E: span :=
  {|
    s := { σN & sat (fst σN) E (snd σN) } ;
    π1 s := fst (projT1 s) ;
    π2 s := snd (projT1 s) ;
  |}.

Definition searchspan E: span :=
  {|
    s := { '(σ, N, n) | List.nth_error (search σ E) n = Some (σ |- N) } ;
    π1 '(exist _ (σ, _, _) _) := σ ;
    π2 '(exist _ (_, N, _) _) := N ;
  |}.

Definition sound E: s (searchspan E) → s (satspan E).
Proof.
  cbn.
  intros [[[σ N] n] p].
  exists (σ, N).
  cbn.
  generalize dependent n.
  induction (search_sound σ E).
  all: intros n p.
  1: destruct n; discriminate.
  destruct n.
  - cbn in p.
    inversion p.
    subst.
    auto.
  - cbn in p.
    destruct Ps.
    1: destruct n; discriminate.
    apply (IHs0 n).
    auto.
Defined.

Definition π1_sound1 E: ∀ s, π1 (searchspan E) s = π1 (satspan E) (sound E s).
Proof.
  cbn.
  intros [[[σ N] n] p].
  cbn.
  auto.
Defined.

Definition π2_sound1 E: ∀ s, π2 (searchspan E) s = π2 (satspan E) (sound E s).
Proof.
  cbn.
  intros [[[σ N] n] p].
  cbn.
  auto.
Defined.

Lemma subst_assoc {x f g h}:
  subst_context (subst_context h x g) x f = subst_context h x (subst_context g x f).
Proof.
  induction f.
  all: cbn.
  all: auto.
  - destruct eq_var eqn:q.
    1: auto.
    cbn.
    rewrite q.
    auto.
  - rewrite IHf.
    destruct eq_var eqn:q.
    all: auto.
  - rewrite IHf1.
    rewrite IHf2.
    auto.
  - rewrite IHf1.
    rewrite IHf2.
    auto.
  - rewrite IHf1.
    rewrite IHf2.
    auto.
  - rewrite IHf1.
    rewrite IHf2.
    auto.
    destruct eq_var.
    1: auto.
    destruct eq_var.
    1: auto.
    auto.
Qed.

Definition useonce Γ u: usage := List.map (λ '(x, t), u) Γ.

Definition oftype Γ t := { E | JE Γ (useonce Γ u_unused) (useonce Γ u_used) E t }.

Record iso A B := {
    to: A → B ;
    from: B → A ;
    to_from b: to (from b) = b;
    from_to a: from (to a) = a;
}.
Arguments to {A B}.
Arguments from {A B}.
Arguments to_from {A B}.
Arguments from_to {A B}.

Inductive tr A: Prop := | tr_intro (a: A).

Definition equiv E E' :=
  ∀ σ N, tr (iso (sat σ E N) (sat σ E' N)).

Instance equiv_Reflexive: Reflexive equiv.
Proof.
  unfold Reflexive.
  intro.
  exists.
  exists (λ a, a) (λ a, a).
  all: auto.
Qed.

Instance equiv_Symmetric: Symmetric equiv.
Proof.
  unfold Symmetric.
  intros x y p σ N.
  destruct (p σ N) as [p'].
  exists.
  exists (from p') (to p').
  - apply from_to.
  - apply to_from.
Qed.

Instance equiv_Transitive: Transitive equiv.
Proof.
  unfold Transitive.
  intros ? ? ? p q σ N.
  destruct (p σ N) as [p'].
  destruct (q σ N) as [q'].
  exists.
  exists (λ a, to q' (to p' a)) (λ a, from p' (from q' a)).
  - intros.
    rewrite to_from.
    rewrite to_from.
    auto.
  - intros.
    rewrite from_to.
    rewrite from_to.
    auto.
Qed.

Instance equiv_Equivalence: Equivalence equiv := {
    Equivalence_Reflexive := _ ;
}.

Instance context_Setoid: Setoid context := {
    equiv := equiv ;
}.

Lemma subst_var {x E}:
  subst_context (E_var x) x E = E.
Proof.
  induction E.
  all: cbn.
  all: auto.
  all: try destruct eq_var.
  all: subst.
  all: auto.
  all: try destruct eq_var.
  all: try rewrite IHE.
  all: try rewrite IHE1.
  all: try rewrite IHE2.
  all: auto.
Qed.

Lemma length_0 {A} {l: list A}: length l = 0 → l = nil.
Proof.
  destruct l.
  1: auto.
  cbn.
  discriminate.
Qed.

Function is_mt Δ :=
  if Δ is cons u Δ'
  then
    if u is u_unused
    then is_mt Δ'
    else false
  else
    true.

Lemma is_mt_sound:
  ∀ {Δ}, Bool.Is_true (is_mt Δ) → Δ = mt (length Δ).
Proof using .
  intros Δ.
  functional induction (is_mt Δ).
  all: cbn.
  all: intro p.
  - rewrite IHb.
    all: auto.
    rewrite length_mt.
    auto.
  - contradiction.
  - destruct Δ.
    1: auto.
    contradiction.
Qed.

Lemma is_mt_complete:
  ∀ {n}, is_mt (mt n) = true.
Proof using .
  intros n.
  induction n.
  all: cbn.
  all: auto.
Qed.

Function minus_xs x xs :=
  match xs with
  | cons y T' =>
      if eq_var x y
      then
        T'
      else
        cons y (minus_xs x T')
  | _ => nil
  end.

Function rm n Δ :=
  match n, Δ with
  | O, cons u_used Δ' => Δ'
  | S n', cons u_unused Δ' => cons u_unused (rm n' Δ')
  | _, _ => nil
  end.

Lemma xsof_minus {x Γ}:
  xsof (minus x Γ) = minus_xs x (xsof Γ).
Proof.
  induction Γ.
  all: cbn.
  1: auto.
  destruct a as [y t].
  cbn.
  destruct eq_var.
  all: subst.
  1: auto.
  cbn.
  rewrite IHΓ.
  auto.
Qed.
