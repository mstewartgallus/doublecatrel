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
  set (s := Nat.eq_dec).
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
  rewrite IHl.
  auto.
Qed.

Fixpoint one x Γ: option usage :=
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

Lemma length_same {Γ ns E t}: JE Γ ns E t → length Γ = length ns.
Proof.
  intro p.
  induction p.
  all: cbn.
  - generalize dependent Δ.
    induction H.
    all: cbn.
    all: intros Δ p.
    + inversion p.
      2: subst; contradiction.
      subst.
      cbn.
      rewrite length_mt.
      rewrite length_len.
      rewrite length_len in p.
      rewrite length_xsof.
      auto.
    + inversion p.
      1: subst; contradiction.
      subst.
      cbn in *.
      rewrite (IHmem _ H6).
      auto.
  - inversion IHp.
    auto.
  - rewrite IHp1 in IHp2.
    rewrite length_merge_eq.
    all: auto.
  - rewrite length_mt.
    rewrite length_len.
    rewrite length_xsof.
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
   Definition unknown_list {A}: JE → list A := opaque (λ _: JE, nil).

  #[local]
   Definition unknown_type: JE → type := opaque (λ _: JE, t_unit).

  #[local]
   Definition unknown_context: JE → context := opaque (λ _: JE, E_tt).

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

  Function nsof (E: JE): usage :=
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
      constructor.
      1: auto.
      generalize dependent x0.
      induction e0'.
      all: cbn in *.
      all: intros.
      * destruct Nat.eq_dec, eq_var.
        all: try contradiction.
        inversion e.
        subst.
        cbn.
        replace (mt (length Γ)) with (mt (len (xsof Γ))).
        2: {
          rewrite length_len.
          rewrite length_xsof.
          auto.
        }
        constructor.
      * destruct Nat.eq_dec, eq_var.
        all: subst.
        all: try contradiction.
        destruct (find_one (find_complete e0')).
        rewrite e1 in e.
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
    - replace (mt (length _x)) with (mt (len (xsof _x))).
      1: constructor.
      rewrite length_len.
      rewrite length_xsof.
      auto.
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

  Function typecheck Γ E: option (usage * type) :=
    match E with
    | E_var x =>
        do t ← find x Γ ;
        do Δ ← one x Γ ;
        Some (Δ, t)
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
      %list.
End Typecheck.

Theorem typecheck_sound:
  ∀ Γ {E Δ t}, typecheck Γ E = Some (Δ, t) → JE Γ Δ E t.
Proof using.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
  - generalize dependent Δ0.
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
      constructor.
    + apply find_sound.
      cbn.
      destruct eq_var.
      1: subst; contradiction.
      auto.
  - clear p.
    generalize dependent Δ0.
    induction Γ.
    all: cbn.
    1: discriminate.
    intros Δ0 p.
    destruct a.
    cbn in e0.
    destruct eq_var, Nat.eq_dec.
    all: subst.
    all: try contradiction.
    + inversion p.
      subst.
      replace (mt (length Γ)) with (mt (len (xsof Γ))).
      2: {
        rewrite length_len.
        rewrite length_xsof.
        auto.
      }
      constructor.
    + destruct (find_one e0).
      rewrite e in p.
      inversion p.
      subst.
      constructor.
      all: auto.
  - replace (length Γ) with (length (xsof Γ)).
    2: {
      rewrite length_xsof.
      auto.
    }
    rewrite <- length_len.
    constructor.
Qed.

Lemma length_one {x Γ}:
  ∀ {Δ},
  one x Γ = Some Δ →
  length Δ = length Γ.
Proof.
  induction Γ.
  1: discriminate.
  cbn in *.
  intros Δ p.
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
    cbn.
    rewrite <- (IHΓ u).
    2: auto.
    auto.
Qed.


Theorem length_typecheck:
  ∀ {Γ E t Δ},
    typecheck Γ E = Some (Δ, t) →
    length Δ = length Γ.
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

Theorem typecheck_complete:
  ∀ Γ {E Δ t}, JE Γ Δ E t → typecheck Γ E = Some (Δ, t).
Proof using.
  intros ? ? ? ? p.
  induction p.
  all: cbn.
  all: try rewrite IHp.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: auto.
  - rewrite (find_complete H).
    destruct (find_one (find_complete H)).
    rewrite e.
    generalize dependent x0.
    generalize dependent Δ.
    induction H.
    all: cbn.
    all: intros.
    + cbn in e.
      destruct Nat.eq_dec.
      2: contradiction.
      inversion e.
      subst.
      replace (length Γ) with (len (xsof Γ)).
      2: {
        rewrite length_xsof.
        auto.
      }
      cbn in *.
      inversion H0.
      all: subst.
      2: contradiction.
      auto.
    + cbn in e.
      destruct Nat.eq_dec.
      1: subst; contradiction.
      destruct (find_one (find_complete H0)).
      rewrite e0 in e.
      inversion e.
      subst.
      inversion H1.
      all: subst.
      1: contradiction.
      assert (IHmem' := IHmem _ H7 _ e0).
      inversion IHmem'.
      auto.
  - destruct eq_type.
    2: contradiction.
    auto.
  - rewrite length_len.
    rewrite length_xsof.
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

Definition useonce Γ: usage := List.map (λ '(x, t), 1) Γ.

Definition oftype Γ t := { E | JE Γ (useonce Γ) E t }.

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

Lemma merge_empty_r {Δ}:
  merge Δ (mt (length Δ)) = Δ.
Proof.
  induction Δ.
  all: cbn.
  1: auto.
  rewrite Nat.add_0_r.
  rewrite IHΔ.
  auto.
Qed.

Lemma length_0 {A} {l: list A}: length l = 0 → l = nil.
Proof.
  destruct l.
  1: auto.
  cbn.
  discriminate.
Qed.

Function is_mt Δ :=
  if Δ is cons n Δ'
  then
    if n is O
    then is_mt Δ'
    else false
  else
    true.

Function lmem_find x xs Δ :=
  match xs, Δ with
  | cons y xs', cons 1 Δ' =>
      if eq_var x y
      then
        if is_mt Δ'
        then
          if Nat.eq_dec (length Δ') (length xs')
          then
            true
          else
            false
        else
          false
      else
        false
  | cons y xs', cons 0 Δ' =>
      if eq_var x y
      then
        false
      else
        lmem_find x xs' Δ'
  | _, _ => false
  end.

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

Lemma lmem_find_sound:
  ∀ {x xs Δ}, Bool.Is_true (lmem_find x xs Δ) → lmem x xs Δ.
Proof using .
  intros x xs Δ.
  functional induction (lmem_find x xs Δ).
  all: cbn.
  all: intros p.
  all: try contradiction.
  - assert (q := @is_mt_sound Δ').
    destruct is_mt.
    2: discriminate.
    rewrite q.
    2: auto.
    rewrite _x0.
    rewrite <- length_len.
    constructor.
  - constructor.
    all: auto.
Qed.

Lemma lmem_find_complete {x xs Δ}:
  lmem x xs Δ → lmem_find x xs Δ = true.
Proof using .
  intro p.
  induction p.
  all: cbn.
  - destruct eq_var.
    2: contradiction.
    rewrite is_mt_complete.
    rewrite length_mt.
    rewrite length_len.
    destruct Nat.eq_dec.
    2: contradiction.
    cbv.
    auto.
  - destruct eq_var.
    1: subst; contradiction.
    auto.
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

Function rm x xs Δ :=
  match xs, Δ with
  | cons y T, cons n T' =>
      if eq_var x y
      then
        if Nat.eq_dec n 1
        then
          T'
        else
          nil
      else
        cons n (rm x T T')
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


Lemma is_mt_rm {x xs Δ}:
  Bool.Is_true (is_mt Δ) → is_mt (rm x xs Δ) = true.
Proof.
  generalize dependent xs.
  functional induction (is_mt Δ).
  all: cbn.
  all: try contradiction.
  all: intros xs q.
  - destruct xs.
    all: cbn.
    1: auto.
    destruct eq_var.
    1: auto.
    cbn.
    auto.
  - destruct Δ.
    2: contradiction.
    destruct xs.
    all: cbn.
    all: auto.
Qed.
