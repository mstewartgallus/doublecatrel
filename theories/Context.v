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

  Function typecheck Γ Δ E t: option usage :=
    match E, t with
    | E_lam x E, t1 * t2 =>
        do (u_used :: Δ') ← typecheck ((x, t1) :: Γ) (u_unused :: Δ) E t2 ;
        Some Δ'

    | E_tt, t_unit =>
        if Nat.eq_dec (length Γ) (length Δ)
        then
          Some Δ
        else
          None

    | E_fanout E E', t1 * t2 =>
        do Δ1 ← typecheck Γ Δ E t1 ;
        do Δ2 ← typecheck Γ Δ1 E' t2 ;
        Some Δ2

    | E_neu e, _ =>
        do (Δ, t') ← typeinfer Γ Δ e ;
        if eq_type t t' then Some Δ else None

    | _, _ => None
    end
      %list
  with typeinfer Γ Δ e: option (usage * type) :=
    match e with
    | e_var x => lookup x Γ Δ

    | e_app e E' =>
        do (Δ1, t1 * t2) ← typeinfer Γ Δ e ;
        do Δ2 ← typecheck Γ Δ1 E' t1 ;
        Some (Δ2, t2)

    | e_step e E' t =>
        do (Δ1, t_unit) ← typeinfer Γ Δ e ;
        do Δ2 ← typecheck Γ Δ1 E' t ;
        Some (Δ2, t)

    | e_let x y e E' t3 =>
        do (Δ1, t1 * t2) ← typeinfer Γ Δ e ;
        do (u_used :: u_used :: Δ2) ← typecheck ((y, t2) :: (x, t1) :: Γ) (u_unused :: u_unused :: Δ1) E' t3 ;
        Some (Δ2, t3)

    | e_cut E t =>
        do Δ ← typecheck Γ Δ E t ;
        Some (Δ, t)
    end
      %list.
End Typecheck.

Fixpoint
  typecheck_sound {E} {struct E}:
  ∀ {Γ Δ Δ' t}, typecheck Γ Δ E t = Some Δ' → check Γ Δ Δ' E t
    with
  typeinfer_sound {e} {struct e}:
  ∀ {Γ Δ Δ' t}, typeinfer Γ Δ e = Some (Δ', t) → infer Γ Δ Δ' e t

.
Proof using.
  - destruct E.
    all: cbn.
    all: intros ? ? ? ? p.
    all: inversion p.
    all: subst.
    all: clear p.
    + destruct t.
      1: discriminate.
      destruct typecheck eqn:q.
      2: discriminate.
      destruct u.
      1: discriminate.
      destruct u.
      2: discriminate.
      inversion H0.
      subst.
      constructor.
      auto.
    + destruct t.
      2: discriminate.
      destruct Nat.eq_dec.
      2: discriminate.
      inversion H0.
      subst.
      constructor.
      auto.
    + destruct t.
      1: discriminate.
      destruct typecheck eqn:q1.
      2: discriminate.
      destruct typecheck eqn:q2 in H0.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
    + constructor.
      destruct typeinfer eqn:q.
      2: discriminate.
      destruct p.
      destruct eq_type.
      2: discriminate.
      inversion H0.
      subst.
      eauto.
  - destruct e.
    all: cbn.
    all: intros ? ? ? ? p.
    all: inversion p.
    all: subst.
    all: clear p.
    + constructor.
      * generalize dependent Δ'.
        functional induction (lookup x Γ Δ).
        all: cbn.
        all: intros ? p.
        all: inversion p.
        all: subst.
        all: constructor.
        all: eauto.
      * generalize dependent Δ'.
        functional induction (lookup x Γ Δ).
        all: cbn.
        all: intros ? p.
        all: inversion p.
        all: subst.
        all: constructor.
        all: eauto.
        rewrite length_xsof.
        auto.
    + destruct typeinfer eqn:q1.
      2: discriminate.
      destruct p.
      destruct t0.
      1: discriminate.
      destruct typecheck eqn:q2.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
    + destruct typeinfer eqn:q1.
      2: discriminate.
      destruct p.
      destruct t1.
      2: discriminate.
      destruct typecheck eqn:q2.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
    + destruct typeinfer eqn:q1.
      2: discriminate.
      destruct p.
      destruct t1.
      1: discriminate.
      destruct typecheck eqn:q2.
      2: discriminate.
      destruct u0.
      1: discriminate.
      destruct u0.
      2: discriminate.
      destruct u1.
      1: discriminate.
      destruct u0.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
    + destruct typecheck eqn:q.
      2: discriminate.
      inversion H0.
      subst.
      constructor.
      eauto.
Qed.

Fixpoint typecheck_complete {Γ E Δ Δ' t} (p: check Γ Δ Δ' E t):
  typecheck Γ Δ E t = Some Δ'
with
typeinfer_complete {Γ e Δ Δ' t} (p: infer Γ Δ Δ' e t):
  typeinfer Γ Δ e = Some (Δ', t).
Proof using.
  - destruct p.
    all: cbn.
    all: try rewrite (typecheck_complete _ _ _ _ _ p).
    all: try rewrite (typecheck_complete _ _ _ _ _ p1).
    all: try rewrite (typecheck_complete _ _ _ _ _ p2).
    all: try rewrite (typeinfer_complete _ _ _ _ _ H).
    all: auto.
    + destruct Nat.eq_dec.
      2: contradiction.
      auto.
    + destruct eq_type.
      2: contradiction.
      auto.
  - destruct p.
    all: cbn.
    all: try rewrite (typeinfer_complete _ _ _ _ _ p).
    all: try rewrite (typecheck_complete _ _ _ _ _ H).
    all: auto.
    + generalize dependent Δ'.
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
      * rewrite <- H1.
        rewrite length_xsof.
        destruct Nat.eq_dec.
        2: contradiction.
        auto.
      * rewrite (IHmem _ _ H7).
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

Fixpoint search σ E t: spans :=
  match E, t with
  | E_lam x E, t1 * t2 =>
      do N0 ← generate t1 ;
      do (σ' |- N1) ← search (x ↦ (t1, N0) ∪ σ) E t2 ;
      if Map.find x σ' is Some (t1', N0')
      then
        match eq_normal N0 N0', eq_type t1 t1' with
        | left _, left _ => [σ' \ x |- N_fanout N0 N1]
        | _, _ => []
        end
      else
        []

  | E_tt, t_unit => [∅ |- N_tt]

  | E_fanout E E', t1 * t2 =>
      do (σ1 |- N) ← search σ E t1 ;
      do (σ2 |- N') ← search σ E' t2 ;
      [σ1 ∪ σ2 |- N_fanout N N']

  | E_neu e, _ =>
      do (t', p) ← search_redex σ e ;
      if eq_type t t' then [p] else []
  | _, _ => []
  end%list %map
with search_redex σ e: list (type * span) :=
  match e with
  | e_var x => if Map.find x σ is Some (t, N) then [(t, x ↦ (t, N) |- N)] else []

  | e_app e E' =>
      do (t, σ1 |- N) ← search_redex σ e ;
      if t is t1 * t2
      then
        do (σ2 |- N0) ← search σ E' t1 ;
        if N is N_fanout N0' N1
        then
          if eq_normal N0 N0'
          then
            [(t2, σ1 ∪ σ2 |- N1)]
          else
            []
        else
          []
      else
        []

  | e_step e E' t2 =>
      do (t1, σ1 |- N) ← search_redex σ e ;
      do (σ2 |- N') ← search σ E' t2 ;
      if N is N_tt
      then
        if t1 is t_unit
        then
          [(t2, σ1 ∪ σ2 |- N')]
        else
          []
      else
        []

  | e_let x y e E' t3 =>
      do (t, σ1 |- N) ← search_redex σ e ;
      do (t1, t2) ← (if t is a * b then [(a, b)] else []) ;
      do (a, b) ← (if N is N_fanout a b then [(a, b)] else []) ;
      do (σ2 |- N') ← search ((x ↦ (t1, a)) ∪ (y ↦ (t2, b)) ∪ σ) E' t3 ;
      match Map.find x (σ2 \ y), Map.find y σ2 with
      | Some (t1', a'), Some (t2', b') =>
          match eq_normal a a', eq_normal b b', eq_type t1 t1', eq_type t2 t2' with
          | left _, left _, left _, left _ =>
              [(t3, σ1 ∪ ((σ2 \ y) \ x) |- N')]
          | _, _, _, _ => []
          end
      | _, _ => []
      end

  | e_cut E t =>
      do p ← search σ E t ;
      [(t, p)]
  end%list %map.

Lemma sound_pure:
  ∀ {σ E N t}, satE σ E N t → sound E [σ |- N] t.
Proof.
  repeat constructor.
  auto.
Defined.

Lemma sound_mon {E t p p'}:
  sound E p t → sound E p' t →
  sound E (p ++ p') t.
Proof.
  intros.
  induction p.
  1: auto.
  cbn.
  inversion H.
  constructor.
  all: auto.
Defined.

Lemma sounde_mon {e p p'}:
  sounde e p → sounde e p' →
  sounde e (p ++ p')%list.
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
  ∀ σ E t, sound E (search σ E t) t
 with
 searche_sound:
   ∀ σ e, sounde e (search_redex σ e).
Proof using.
  Open Scope map.
  - intros σ E.
    generalize dependent σ.
    destruct E.
    all: intros.
    + cbn.
      destruct t.
      1:constructor.
      induction (generate t1).
      1: cbn.
      1: constructor.
      cbn in *.
      apply sound_mon.
      2: auto.
      clear IHl.
      induction (search_sound (x ↦ (t1, a) ∪ σ) E t2).
      1: constructor.
      cbn.
      destruct Map.find eqn:q.
      2: auto.
      destruct p.
      destruct (eq_normal a n).
      2: auto.
      subst.
      destruct (eq_type t1 t0).
      2: auto.
      subst.
      cbn.
      constructor.
      1: auto.
      constructor.
      rewrite Map.add_minus.
      all: auto.
    + cbn.
      destruct t.
      all: try econstructor.
      all: constructor.
    + cbn.
      destruct t.
      1: constructor.
      induction (search_sound σ E1 t1).
      1: constructor.
      cbn.
      apply sound_mon.
      2: auto.
      clear IHs.
      induction (search_sound σ E2 t2).
      1: constructor.
      cbn.
      constructor.
      1: auto.
      constructor.
      all: eauto.
    + cbn.
      induction (searche_sound σ e).
      1: constructor.
      cbn.
      destruct eq_type.
      2: auto.
      cbn.
      subst.
      cbn.
      constructor.
      1: auto.
      constructor.
      auto.
  - intros σ e.
    generalize dependent σ.
    destruct e.
    all: intros.
    + cbn.
      destruct Map.find eqn:q.
      2: constructor.
      destruct p.
      constructor.
      1: constructor.
      constructor.
    + cbn.
      induction (searche_sound σ e).
      1: constructor.
      cbn.
      destruct t.
      all: cbn.
      all: auto.
      apply sounde_mon.
      all: cbn.
      2: auto.
      clear IHs.
      induction (search_sound σ E' t1).
      all: cbn.
      1: constructor.
      cbn.
      destruct N.
      all: cbn.
      all: auto.
      destruct eq_normal.
      all: cbn.
      all: auto.
      constructor.
      1: auto.
      subst.
      econstructor.
      all: eauto.
    + cbn.
      induction (searche_sound σ e).
      1: constructor.
      cbn.
      apply sounde_mon.
      all: cbn.
      2: auto.
      clear IHs.
      induction (search_sound σ E' t).
      all: cbn.
      1: constructor.
      cbn.
      destruct N.
      all: cbn.
      all: auto.
      destruct t0.
      all: cbn.
      all: auto.
      constructor.
      1: auto.
      constructor.
      all: eauto.
    + cbn.
      induction (searche_sound σ e).
      1: constructor.
      cbn.
      apply sounde_mon.
      2: auto.
      clear IHs.
      destruct t0.
      1: constructor.
      cbn.
      destruct N.
      cbn.
      1: constructor.
      cbn.
      repeat rewrite List.app_nil_r.
      induction (search_sound (((x ↦ (t0_1, N1) ∪ y ↦ (t0_2, N2)) ∪ σ)) E' t).
      1: constructor.
      cbn.
      destruct (Map.find x (σ1 \ y)) eqn:q.
      2: auto.
      destruct p.
      destruct (Map.find y σ1) eqn:q'.
      2: auto.
      destruct p.
      destruct (eq_normal N1 n).
      2: auto.
      subst.
      destruct (eq_normal N2 n0).
      2: auto.
      subst.
      cbn.
      destruct eq_type.
      2: auto.
      subst.
      cbn.
      destruct eq_type.
      2: auto.
      subst.
      cbn.
      constructor.
      1: auto.
      econstructor.
      all: eauto.
      all: repeat rewrite Map.add_minus.
      all: eauto.
    + cbn.
      induction (search_sound σ E t).
      1: constructor.
      cbn.
      constructor.
      1: auto.
      constructor.
      auto.
Qed.

(* FIXME type check *)
Record span := {
  s: Set ;
  π1: s → store ;
  π2: s → normal ;
}.

Definition useonce Γ u: usage := List.map (λ '(x, t), u) Γ.

Definition oftype Γ t := { E | check Γ (useonce Γ u_unused) (useonce Γ u_used) E t }.

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
