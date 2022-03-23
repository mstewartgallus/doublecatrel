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
Implicit Types x y: var.
Implicit Type xs: vars.
Implicit Type σ: store.
Implicit Type v: intro.

Import Map.MapNotations.

Definition eq_usage Δ Δ': {Δ = Δ'} + {Δ ≠ Δ'}.
Proof.
  set (s := eq_use).
  decide equality.
Defined.

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
          do ' (Δ'', t)  ← lookup x Γ' Δ' ;
          Some (cons u Δ'', t)
    | _, _ => None
    end.

  Function typecheck Γ Δ E t: option usage :=
    match E, t with
    | E_lam x E, t1 * t2 =>
        do ' (u_used :: Δ') ← typecheck ((x, t1) :: Γ) (u_unused :: Δ) E t2 ;
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
        do ' (Δ, t') ← typeinfer Γ Δ e ;
        if eq_type t t' then Some Δ else None

    | _, _ => None
    end
      %list
  with typeinfer Γ Δ e: option (usage * type) :=
    match e with
    | e_var x => lookup x Γ Δ

    | e_app e E' =>
        do ' (Δ1, t1 * t2) ← typeinfer Γ Δ e ;
        do Δ2 ← typecheck Γ Δ1 E' t1 ;
        Some (Δ2, t2)

    | e_step e E' t =>
        do ' (Δ1, t_unit) ← typeinfer Γ Δ e ;
        do Δ2 ← typecheck Γ Δ1 E' t ;
        Some (Δ2, t)

    | e_let x y e E' t3 =>
        do ' (Δ1, t1 * t2) ← typeinfer Γ Δ e ;
        do ' (u_used :: u_used :: Δ2) ← typecheck ((y, t2) :: (x, t1) :: Γ) (u_unused :: u_unused :: Δ1) E' t3 ;
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
      all: try discriminate.
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
      all: try discriminate.
      destruct Nat.eq_dec.
      2: discriminate.
      inversion H0.
      subst.
      constructor.
      auto.
    + destruct t.
      all: try discriminate.
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
      all: try discriminate.
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
      all: try discriminate.
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
      all: try discriminate.
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

Fixpoint generate t: list intro :=
  match t with
  | t_var _ => []
  | t_unit => [v_tt]
  | t * t' =>
      do v ← generate t ;
      do v' ← generate t' ;
      [v_fanout v v']
  end%list.

Fixpoint verify σ E v: list store :=
  match E, v with
  | E_lam x E, v_fanout v1 v2 =>
      do σ' ← verify (x ↦ v1 ∪ σ) E v2 ;
      if Map.find x σ' is Some v1'
      then
        if eq_intro v1 v1'
        then [σ' \ x]
        else []
      else
        []

  | E_tt, v_tt => [∅]

  | E_fanout E E', v_fanout v1 v2 =>
      do σ1 ← verify σ E v1 ;
      do σ2 ← verify σ E' v2 ;
      [σ1 ∪ σ2]

  | E_neu e, _ =>
      do (σ' |- v') ← search σ e ;
      if eq_intro v v'
      then [σ']
      else []
  | _, _ => []
  end%list %map
with search σ e: list span :=
  match e with
  | e_var x => if Map.find x σ is Some v then [x ↦ v |- v] else []

  | e_app e E' =>
      do (σ1 |- v) ← search σ e ;
      if v is v_fanout v0 v1
      then
          do σ2 ← verify σ E' v0 ;
          [σ1 ∪ σ2 |- v1]
      else []

  | e_step e E' t2 =>
      do (σ1 |- v) ← search σ e ;
      do v' ← generate t2 ;
      do σ2 ← verify σ E' v' ;
      if v is v_tt
      then [σ1 ∪ σ2 |- v']
      else []

  | e_let x y e E' t3 =>
      do (σ1 |- v) ← search σ e ;
      do (a, b) ← (if v is v_fanout a b then [(a, b)] else []) ;
      do v' ← generate t3 ;
      do σ2 ← verify ((x ↦ a) ∪ (y ↦ b) ∪ σ) E' v' ;
      match Map.find x (σ2 \ y), Map.find y σ2 with
      | Some a', Some b' =>
          match eq_intro a a', eq_intro b b' with
          | left _, left _ =>
              [(σ1 ∪ ((σ2 \ y) \ x) |- v')]
          | _, _ => []
          end
      | _, _ => []
      end

  | e_cut E t =>
      do v ← generate t ;
      do σ ← verify σ E v ;
      [σ |- v]
  end%list %map.

Lemma sound_pure:
  ∀ {σ E v}, accepts σ E v → sound E [σ] v.
Proof.
  repeat constructor.
  auto.
Defined.

Lemma sound_mon {E p p' v}:
  sound E p v → sound E p' v →
  sound E (p ++ p') v.
Proof.
  intros.
  induction p.
  1: auto.
  cbn.
  inversion H.
  econstructor.
  all: eauto.
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

Theorem verify_sound:
  ∀ σ E v, sound E (verify σ E v) v
 with
 search_sound:
   ∀ σ e, sounde e (search σ e).
Proof using.
  Open Scope map.
  - intros σ E.
    generalize dependent σ.
    destruct E.
    all: intros.
    + cbn.
      destruct v.
      1: constructor.
      induction (verify_sound (x ↦ v1 ∪ σ) E v2).
      1,3: constructor.
      cbn.
      destruct Map.find eqn:q.
      2: auto.
      destruct eq_intro.
      2: auto.
      subst.
      cbn.
      econstructor.
      1: auto.
      constructor.
      rewrite Map.add_minus.
      all: eauto.
    + cbn.
      destruct v.
      all: try econstructor.
      all: constructor.
    + cbn.
      destruct v.
      1: constructor.
      induction (verify_sound σ E1 v1).
      1: constructor.
      cbn.
      apply sound_mon.
      2: auto.
      clear IHs.
      induction (verify_sound σ E2 v2).
      1,3: constructor.
      cbn.
      econstructor.
      1: auto.
      constructor.
      all: eauto.
    + cbn.
      induction (search_sound σ e).
      1: constructor.
      cbn.
      destruct eq_intro.
      2: auto.
      cbn.
      subst.
      cbn.
      econstructor.
      1: auto.
      constructor.
      eauto.
  - intros σ e.
    generalize dependent σ.
    destruct e.
    all: intros.
    + cbn.
      destruct Map.find eqn:q.
      2: constructor.
      constructor.
      1: constructor.
      constructor.
    + cbn.
      induction (search_sound σ e).
      1: constructor.
      cbn.
      destruct v.
      all: cbn.
      all: auto.
      apply sounde_mon.
      all: cbn.
      2: auto.
      clear IHs.
      induction (verify_sound σ E' v1).
      all: cbn.
      1: constructor.
      cbn.
      econstructor.
      1: auto.
      econstructor.
      all: eauto.
    + cbn.
      induction (search_sound σ e).
      1: constructor.
      cbn.
      apply sounde_mon.
      all: cbn.
      2: auto.
      clear IHs.
      induction (generate t).
      all: cbn.
      1: constructor.
      induction (verify_sound σ E' a).
      all: cbn.
      1: auto.
      cbn.
      destruct v.
      all: cbn.
      all: auto.
      econstructor.
      1: auto.
      constructor.
      all: auto.
    + cbn.
      induction (search_sound σ e).
      1: constructor.
      cbn.
      apply sounde_mon.
      2: auto.
      clear IHs.
      destruct v.
      1: constructor.
      cbn.
      repeat rewrite List.app_nil_r.
      induction (generate t).
      cbn.
      1: constructor.
      cbn.
      apply sounde_mon.
      all: cbn.
      2: auto.
      induction (verify_sound (((x ↦ v1 ∪ y ↦ v2) ∪ σ)) E' a).
      1: constructor.
      cbn.
      apply sounde_mon.
      all: auto.
      all: cbn.
      destruct (Map.find x (σ1 \ y)) eqn:q.
      2: constructor.
      destruct (Map.find y σ1) eqn:q'.
      2: constructor.
      destruct eq_intro.
      2: constructor.
      subst.
      destruct eq_intro.
      2: constructor.
      subst.
      constructor.
      constructor.
      econstructor.
      all: repeat rewrite Map.add_minus.
      all: eauto.
      constructor.
    + cbn.
      induction (generate t).
      1: constructor.
      cbn.
      apply sounde_mon.
      2: auto.
      induction (verify_sound σ E a).
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
  π2: s → intro ;
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
