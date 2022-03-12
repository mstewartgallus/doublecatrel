Require Blech.Map.
Require Blech.Multiset.
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
Implicit Type Δ: linear.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types x y: var.
Implicit Type σ: store.

Import Map.MapNotations.
Import Multiset.MultisetNotations.

Fixpoint dec x (p: linear) {struct p}: option linear :=
  match p with
  | cons (y, t, n) T =>
      if eq_var x y
      then
        if n is S n'
        then
          Some (cons (x, t, n') T)
        else
          None
      else
        if dec x T is Some T'
        then
          Some (cons (y, t, n) T')
        else
          None
  | _ => None
  end.

Fixpoint inc x (p: linear) {struct p}: linear :=
  match p with
  | cons (y, t, n) T =>
      if eq_var x y
      then
        cons (x, t, S n) T
      else
        cons (y, t, n) (inc x T)
  | _ => nil
  end.

Definition eq_linear Δ Δ': {Δ = Δ'} + {Δ ≠ Δ'}.
Proof.
  decide equality.
  destruct p as [[x t] n].
  destruct a as [[y t'] n'].
  destruct (eq_var x y), (eq_type t t'), (Nat.eq_dec n n').
  all: subst.
  1: left.
  1: reflexivity.
  all: right.
  all: intro p.
  all: inversion p.
  all:  subst.
  all: contradiction.
Defined.

Definition eq_ts (l r: ts): {l = r} + {l ≠ r}.
Proof.
  assert (teq := eq_type).
  decide equality.
Defined.

Definition eq_xs (l r: xs): {l = r} + {l ≠ r}.
Proof.
  assert (xeq := eq_var).
  decide equality.
Defined.

Definition eq_ns (l r: ns): {l = r} + {l ≠ r}.
Proof.
  assert (neq := Nat.eq_dec).
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

Lemma length_len {l}: len l = length l.
Proof.
  induction l.
  1: auto.
  cbn.
  destruct a.
  rewrite IHl.
  auto.
Qed.

Fixpoint one x Γ: option ns :=
  if Γ is cons (y, t) T
  then
    if Nat.eq_dec x y
    then
      Some (cons 1 (mt (length T)))
    else
      if one x T is Some T'
      then
        Some (cons 0 T')
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
  destruct eq_var, Nat.eq_dec.
  all: subst.
  all: try contradiction.
  - exists (cons 1 (mt (length Γ))).
    auto.
  - destruct (IHΓ p).
    rewrite e.
    exists (cons 0 x0).
    auto.
Defined.

Fixpoint toxs Γ: xs :=
  if Γ is cons (x, _) T
  then
    cons x (toxs T)
  else
    nil.

Fixpoint tots Γ: ts :=
  if Γ is cons (_, t) T
  then
    cons t (tots T)
  else
    nil.

Lemma zip_toxs_tots {Γ: environment}: zip (toxs Γ) (tots Γ) = Γ.
Proof.
  induction Γ.
  1: auto.
  cbn.
  destruct a.
  cbn.
  rewrite IHΓ.
  auto.
Qed.

Lemma zip3_toxs_tots {Γ: environment} {ns: ns}: zip21 Γ ns = zip3 (toxs Γ) (tots Γ) ns.
Proof.
  generalize dependent ns.
  induction Γ.
  all: auto.
  intro ns.
  cbn.
  destruct a.
  destruct ns.
  1: auto.
  cbn in *.
  rewrite IHΓ.
  cbn.
  auto.
Qed.

Fixpoint toenv Δ: environment :=
  if Δ is cons (x, t, _) T
  then
    cons (x, t) (toenv T)
  else
    nil.

Fixpoint tons Δ: ns :=
  if Δ is cons (_, _, n) T
  then
    cons n (tons T)
  else
    nil.

Lemma length_merge {ns ns'}:
  length (merge ns ns') = min (length ns) (length ns').
Proof.
  generalize dependent ns'.
  induction ns.
  all: cbn.
  1: auto.
  intros ns'.
  destruct ns'.
  1: auto.
  cbn.
  rewrite IHns.
  auto.
Qed.

Lemma length_merge_eq {ns ns'}:
  length ns = length ns' →
  length (merge ns ns') = length ns.
Proof.
  generalize dependent ns'.
  induction ns.
  all: cbn.
  1: auto.
  intros ns' p.
  destruct ns'.
  1: auto.
  cbn.
  cbn in p.
  rewrite IHns.
  auto.
  inversion p.
  auto.
Qed.

Lemma length_same {Γ ns E t}: JE Γ ns E t → length Γ = length ns.
Proof.
  intro p.
  induction p.
  all: cbn.
  - induction H.
    + cbn.
      rewrite length_mt.
      rewrite length_len.
      auto.
    + cbn.
      rewrite IHlmem.
      auto.
  - inversion IHp.
    auto.
  - rewrite IHp1 in IHp2.
    rewrite length_merge_eq.
    all: auto.
  - rewrite length_mt.
    rewrite length_len.
    auto.
  - rewrite IHp1 in IHp2.
    rewrite length_merge_eq.
    all: auto.
  - rewrite IHp1 in IHp2.
    rewrite length_merge_eq.
    all: auto.
  - cbn in IHp2.
    inversion IHp2.
    rewrite IHp1 in H0.
    rewrite length_merge_eq.
    all: auto.
Qed.

Module ProofTree.
  Inductive JE: Set :=
  | JE_var Γ x
  | JE_lam: JE → JE
  | JE_app: JE → JE → JE
  | JE_tt Γ
  | JE_step: JE → JE → JE
  | JE_fanout: JE → JE → JE
  | JE_let: JE → JE → JE
  .

  #[local]
  Definition unknown_list {A} (_: JE): list A := nil.
  #[local]
  Definition unknown_type (_: JE): type := t_unit.
  #[local]
  Definition unknown_context (_: JE): context := E_tt.
  Function envof (E: JE): environment :=
    match E with
    | JE_var Γ _ => Γ
    | JE_lam p =>
        if envof p is cons _ T then T else unknown_list E
    | JE_app p1 _ => envof p1
    | JE_tt Γ => Γ
    | JE_step p1 _ => envof p1
    | JE_fanout p1 _ => envof p1
    | JE_let p1 _ => envof p1
    end.

  Function xsof (E: JE): xs :=
    match E with
    | JE_var Γ _ => toxs Γ
    | JE_lam p =>
        if xsof p is cons _ T then T else unknown_list E
    | JE_app p1 _ => xsof p1
    | JE_tt Γ => toxs Γ
    | JE_step p1 _ => xsof p1
    | JE_fanout p1 _ => xsof p1
    | JE_let p1 _ => xsof p1
    end.

  Lemma toxs_envof {E: JE}: toxs (envof E) = xsof E.
  Proof.
    induction E.
    all: cbn.
    all: auto.
    destruct (envof E), (xsof E).
    all: try discriminate.
    all: auto.
    + cbn in IHE.
      destruct p.
      discriminate.
    + cbn in IHE.
      destruct p.
      inversion IHE.
      subst.
      auto.
  Qed.

  Function tsof (E: JE): ts :=
    match E with
    | JE_var Γ _ => tots Γ
    | JE_lam p =>
        if tsof p is cons _ T then T else unknown_list E
    | JE_app p1 _ => tsof p1
    | JE_tt Γ => tots Γ
    | JE_step p1 _ => tsof p1
    | JE_fanout p1 _ => tsof p1
    | JE_let p1 _ => tsof p1
    end.

  Lemma tots_envof {E: JE}: tots (envof E) = tsof E.
  Proof.
    induction E.
    all: cbn.
    all: auto.
    destruct (envof E), (tsof E).
    all: try discriminate.
    all: auto.
    + cbn in IHE.
      destruct p.
      discriminate.
    + cbn in IHE.
      destruct p.
      inversion IHE.
      subst.
      auto.
  Qed.

  Opaque unknown_list.
  Opaque unknown_type.
  Opaque unknown_context.

  Function nsof (E: JE): ns :=
    match E with
    | JE_var Γ x => if one x Γ is Some ns then ns else nil
    | JE_lam p =>
        if nsof p is cons _ T then T else unknown_list E
    | JE_app p1 p2 => merge (nsof p1) (nsof p2)
    | JE_tt Γ => mt (length Γ)
    | JE_step p1 p2 => merge (nsof p1) (nsof p2)
    | JE_fanout p1 p2 => merge (nsof p1) (nsof p2)
    | JE_let p1 p2 =>
        merge (nsof p1) (if nsof p2 is cons 1 (cons 1 T) then T else unknown_list E)
    end.

  Function ctxof (E: JE): context :=
    match E with
    | JE_var _ x => E_var x
    | JE_lam p =>
        match envof p with
        | cons (x, t) _ => E_lam x t (ctxof p)
        | _ => unknown_context E
        end
    | JE_app p1 p2 => E_app (ctxof p1) (ctxof p2)
    | JE_tt _ => E_tt
    | JE_step p1 p2 => E_step (ctxof p1) (ctxof p2)
    | JE_fanout p1 p2 => E_fanout (ctxof p1) (ctxof p2)
    | JE_let p1 p2 =>
        if envof p2 is cons (y, _) (cons (x, _) _)
        then
          E_let x y (ctxof p1) (ctxof p2)
        else
          unknown_context E
    end.

  Function typeof (E: JE): type :=
    match E with
    | JE_var Γ x => if find x Γ is Some t then t else unknown_type E
    | JE_lam p =>
        if envof p is cons (_, t) _
        then
          t * typeof p
        else
          unknown_type E
    | JE_app p1 p2 => if typeof p1 is _ * t then t else unknown_type E
    | JE_tt _ => t_unit
    | JE_step _ p2 => typeof p2
    | JE_fanout p1 p2 => typeof p1 * typeof p2
    | JE_let _ p2 => typeof p2
    end.

  Definition linof (E: JE): linear := zip (envof E) (nsof E).

  Definition asserts (E: JE): Prop := Spec.JE (envof E) (nsof E) (ctxof E) (typeof E).

  Notation "'test' p" := (match p with | left _ => true | right _ => false end) (at level 1).

  Function check (p: JE): bool :=
    match p with
    | JE_var Γ x =>
        if find x Γ is Some _ then true else false
    | JE_lam p =>
        match envof p, nsof p with
         | cons (x, t) _, cons 1 _ => true
         | _, _ => false
        end
        && check p
    | JE_app p1 p2 =>
        test (eq_environment (envof p1) (envof p2))
        && (if typeof p1 is t * _ then test (eq_type t (typeof p2)) else false)
        && check p1
        && check p2
    | JE_tt _ => true
    | JE_step p1 p2 =>
        test (eq_environment (envof p1) (envof p2))
        && (if typeof p1 is t_unit then true else false)
        && check p1
        && check p2
    | JE_fanout p1 p2 =>
        test (eq_environment (envof p1) (envof p2))
        && check p1
        && check p2
    | JE_let p1 p2 =>
        (match envof p2, nsof p2, typeof p1 with
         | cons (y, t2) (cons (x, t1) g2),
           cons 1 (cons 1 _),
           t1' * t2' =>
             test (eq_environment (envof p1) g2)
             && test (eq_type t1 t1')
             && test (eq_type t2 t2')
         | _, _, _ => false
         end)
        && check p1
        && check p2
    end %bool.

  Lemma check_sound (p: JE): Bool.Is_true (check p) → asserts p.
  Proof.
    unfold asserts.
    functional induction (check p).
    all: cbn.
    all: intro q.
    all: try contradiction.
    - rewrite e0.
      assert (e0' := find_sound e0).
      destruct (find_one e0).
      rewrite e.
      rewrite <- zip_toxs_tots.
      clear e0.
      constructor.
      + rewrite zip_toxs_tots.
        generalize dependent x0.
        induction e0'.
        all: cbn.
        all: intros.
        * destruct Nat.eq_dec.
          2: contradiction.
          inversion e.
          subst.
          rewrite <- length_len.
          constructor.
        * cbn in e.
          destruct Nat.eq_dec.
          1: subst; contradiction.
          destruct (find_one (find_complete e0')).
          rewrite e0 in e.
          inversion e.
          subst.
          constructor.
          all: auto.
    - destruct (check p0).
      2: contradiction.
      rewrite e0, e1.
      rewrite e0, e1 in IHb.
      cbn in IHb.
      constructor.
      auto.
    - rewrite e1.
      rewrite e1 in IHb.
      rewrite <- _x in IHb0.
      destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      econstructor.
      all: eauto.
    - rewrite <- length_len.
      constructor.
    - destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      rewrite e1 in IHb.
      rewrite <- _x in IHb0.
      constructor.
      all: auto.
    - destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      rewrite <- _x in IHb0.
      constructor.
      all: auto.
    - destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      rewrite e0.
      rewrite e1.
      rewrite e2 in IHb.
      rewrite e0 in IHb0.
      rewrite e1 in IHb0.
      econstructor.
      all: eauto.
  Qed.
End ProofTree.

Section Typecheck.
  Import OptionNotations.

  Function typecheck Γ E: option (ns * type) :=
    match E with
    | E_var x =>
        do t ← find x Γ ;
        do ns ← one x Γ ;
        Some (ns, t)
    | E_lam x t1 E =>
        do (cons 1 Δ, t2) ← typecheck ((x, t1) :: Γ) E ;
        Some (Δ, t1 * t2)
    | E_app E E' =>
        do (Δ', t1 * t2) ← typecheck Γ E ;
        do (Δ, t1') ← typecheck Γ E' ;
        if eq_type t1 t1'
        then
          Some (merge Δ' Δ, t2)
        else
          None

    | E_tt => Some (mt (length Γ), t_unit)
    | E_step E E' =>
        do (Δ', t_unit) ← typecheck Γ E ;
        do (Δ, t) ← typecheck Γ E' ;
        Some (merge Δ' Δ, t)

    | E_fanout E E' =>
        do (Δ', t1) ← typecheck Γ E ;
        do (Δ, t2) ← typecheck Γ E' ;
        Some (merge Δ' Δ, t1 * t2)

    | E_let x y E E' =>
        do (Δ1, t1 * t2) ← typecheck Γ E ;
        do (cons 1 (cons 1 Δ2), t3) ← typecheck ((y, t2) :: (x, t1) :: Γ) E' ;
        Some (merge Δ1 Δ2, t3)
    end
      %list %multiset.
End Typecheck.

Theorem typecheck_sound:
  ∀ Γ {E ns t}, typecheck Γ E = Some (ns, t) → JE Γ ns E t.
Proof using.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
  - generalize dependent ns0.
    induction Γ.
    1: discriminate.
    cbn.
    all: intros ? ? ?.
    destruct a.
    cbn.
    cbn in *.
    destruct eq_var, Nat.eq_dec.
    all: subst.
    all: try contradiction.
    + inversion e1.
      subst.
      inversion e0.
      subst.
      rewrite <- length_len.
      constructor.
    + destruct (find_one e0).
      rewrite e in e1.
      inversion e1.
      subst.
      constructor.
      all:auto.
  - rewrite <- length_len.
    constructor.
Qed.

Lemma length_one {x Γ}:
  ∀ {ns},
  one x Γ = Some ns →
  length ns = length Γ.
Proof.
  induction Γ.
  1: discriminate.
  cbn in *.
  intros ns p.
  destruct a.
  cbn in *.
  destruct Nat.eq_dec.
  + subst.
    inversion p.
    subst.
    cbn.
    rewrite length_mt.
    auto.
  + destruct (one x Γ).
    2: discriminate.
    inversion p.
    subst.
    rewrite <- (IHΓ n0).
    2: auto.
    auto.
Qed.


Theorem length_typecheck:
  ∀ {Γ E t ns},
    typecheck Γ E = Some (ns, t) →
    length ns = length Γ.
Proof using.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  - eapply length_one.
    eauto.
  - cbn in IHo.
    assert (IHo' := IHo _ _ e0).
    cbn in IHo'.
    inversion IHo'.
    auto.
  - assert (IHo' := IHo _ _ e0).
    assert (IHo0' := IHo0 _ _ e1).
    rewrite <- IHo' in IHo0'.
    rewrite length_merge_eq.
    all: auto.
  - rewrite length_mt.
    auto.
  - assert (IHo' := IHo _ _ e0).
    assert (IHo0' := IHo0 _ _ e1).
    rewrite <- IHo' in IHo0'.
    rewrite length_merge_eq.
    all: auto.
  - assert (IHo' := IHo _ _ e0).
    assert (IHo0' := IHo0 _ _ e1).
    rewrite <- IHo' in IHo0'.
    rewrite length_merge_eq.
    all: auto.
  - assert (IHo' := IHo _ _ e0).
    assert (IHo0' := IHo0 _ _ e1).
    cbn in IHo0'.
    inversion IHo0'.
    rewrite <- IHo' in H0.
    rewrite length_merge_eq.
    all: auto.
Qed.

Lemma mem_lmem {x t Γ ns}:
  lmem x t Γ ns → mem x t Γ.
Proof.
  intros p.
  induction p.
  all: constructor.
  all: auto.
Qed.

Theorem typecheck_complete:
  ∀ Γ {E ns t}, JE Γ ns E t → typecheck Γ E = Some (ns, t).
Proof using.
  intros ? ? ? ? p.
  induction p.
  all: cbn.
  all: try rewrite IHp.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: auto.
  - rewrite (find_complete (mem_lmem H)).
    destruct (find_one (find_complete (mem_lmem H))).
    rewrite e.
    generalize dependent x0.
    induction H.
    all: cbn.
    all: intros.
    + cbn in e.
      destruct Nat.eq_dec.
      2: contradiction.
      inversion e.
      subst.
      rewrite length_len.
      auto.
    + cbn in e.
      destruct Nat.eq_dec.
      1: subst; contradiction.
      destruct (find_one (find_complete (mem_lmem H0))).
      rewrite e0 in e.
      inversion e.
      subst.
      assert (IHlmem' := IHlmem _ e0).
      inversion IHlmem'.
      auto.
  - destruct eq_type.
    2: contradiction.
    auto.
  - rewrite length_len.
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

Definition useonce Γ: linear := List.map (λ '(x, t), (x, t, 1)) Γ.

Definition oftype Γ t := { E | JE (useonce Γ) E t }.

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
