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
  decide equality.
  destruct a as [x u], p as [y u'].
  destruct (eq_var x y), (eq_use u u').
  all: subst.
  all: auto.
  all: right.
  all: intro p.
  all: inversion p.
  all: auto.
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

Section Typecheck.
  Import OptionNotations.

  Function lookup x Δ :=
    if Δ is cons (y, u) Δ'
    then
        if eq_var x y
        then
          if u is u_unused
          then
             Some (cons (y, u_used) Δ')
          else
            None
        else
          do Δ'' ← lookup x Δ' ;
          Some (cons (y, u) Δ'')
  else
    None.

  Function usecheck Δ E: option usage :=
    match E with
    | E_lam x E =>
        do ' ((y, u_used) :: Δ') ← usecheck ((x, u_unused) :: Δ) E ;
        if eq_var x y
        then
          Some Δ'
        else
          None

    | E_tt => Some Δ

    | E_fanout E E' =>
        do Δ1 ← usecheck Δ E ;
        usecheck Δ1 E'

    | E_neu e =>
        useinfer Δ e

    end
      %list
  with useinfer Δ e: option usage :=
    match e with
    | e_var x => lookup x Δ

    | e_app e E' =>
        do Δ1 ← useinfer Δ e ;
        usecheck Δ1 E'

    | e_step e E' t =>
        do Δ1 ← useinfer Δ e ;
        usecheck Δ1 E'

    | e_let x y e E' t3 =>
        do Δ1 ← useinfer Δ e ;
        do ' ((y', u_used) :: (x', u_used) :: Δ2) ← usecheck ((y, u_unused) :: (x, u_unused) :: Δ1) E' ;
        match eq_var x x', eq_var y y' with
        | left _, left _ => Some Δ2
        | _, _ => None
        end

    | e_cut E t => usecheck Δ E
    end
      %list.

  Function typecheck Γ E t: bool :=
    match E, t with
    | E_lam x E, t1 * t2 =>
        typecheck ((x, t1) :: Γ) E t2

    | E_tt, t_unit => true

    | E_fanout E E', t1 * t2 =>
        typecheck Γ E t1
        && typecheck Γ E' t2

    | E_neu e, _ =>
        if typeinfer Γ e is Some t'
        then
          if eq_type t t' then true else false
        else
          false

    | _, _ => false
    end
     %bool %list
  with typeinfer Γ e: option type :=
    match e with
    | e_var x => find x Γ

    | e_app e E' =>
        do ' (t1 * t2) ← typeinfer Γ e ;
        if typecheck Γ E' t1
        then
          Some t2
        else
          None

    | e_step e E' t =>
        if typecheck Γ E' t
        then
          do ' t_unit ← typeinfer Γ e ;
          Some t
        else
          None

    | e_let x y e E' t3 =>
        do ' (t1 * t2) ← typeinfer Γ e ;
        if typecheck ((y, t2) :: (x, t1) :: Γ) E' t3
        then
          Some t3
        else
          None

    | e_cut E t =>
        if typecheck Γ E t
        then
          Some t
        else
          None
    end
      %list.
End Typecheck.

Fixpoint
  usecheck_sound {E} {struct E}:
  ∀ {Δ Δ'}, usecheck Δ E = Some Δ' → Δ ⊢ E ⊠ Δ'
    with
  useinfer_sound {e} {struct e}:
  ∀ {Δ Δ'}, useinfer Δ e = Some Δ' → se Δ e Δ'
.
Proof using.
  - destruct E.
    all: cbn.
    all: intros ? ? p.
    all: inversion p.
    all: subst.
    all: clear p.
    + destruct usecheck eqn:q.
      2: discriminate.
      destruct u.
      1: discriminate.
      destruct p.
      destruct u0.
      2: discriminate.
      destruct eq_var.
      2: discriminate.
      inversion H0.
      subst.
      constructor.
      auto.
    + constructor.
    + destruct usecheck eqn:q1.
      2: discriminate.
      econstructor.
      all: eauto.
    + constructor.
      apply useinfer_sound.
      auto.
  - destruct e.
    all: cbn.
    all: intros ? ? p.
    all: inversion p.
    all: subst.
    all: clear p.
    + constructor.
      generalize dependent Δ'.
      functional induction (lookup x Δ).
      all: cbn.
      all: intros ? p.
      all: inversion p.
      all: subst.
      all: constructor.
      all: eauto.
    + destruct useinfer eqn:q1.
      2: discriminate.
      econstructor.
      all: eauto.
    + destruct useinfer eqn:q1.
      2: discriminate.
      econstructor.
      all: eauto.
    + destruct useinfer eqn:q1.
      2: discriminate.
      destruct usecheck eqn:q2.
      2: discriminate.
      destruct u0.
      1: discriminate.
      destruct p.
      destruct u1.
      2: discriminate.
      destruct u0.
      1: discriminate.
      destruct p.
      destruct u1.
      2: discriminate.
      destruct eq_var.
      2: discriminate.
      destruct eq_var.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
    + constructor.
      eauto.
Qed.

Fixpoint
  typecheck_sound {E} {struct E}:
  ∀ {Γ t}, Bool.Is_true (typecheck Γ E t) → check Γ E t
    with
  typeinfer_sound {e} {struct e}:
  ∀ {Γ t}, typeinfer Γ e = Some t → infer Γ e t.
Proof using.
  - destruct E.
    all: cbn.
    all: intros ? ? p.
    all: try contradiction.
    + destruct t.
      all: try contradiction.
      destruct typecheck eqn:q.
      2: contradiction.
      constructor.
      apply typecheck_sound.
      rewrite q.
      auto.
    + destruct t.
      all: try contradiction.
      constructor.
    + destruct t.
      all: try contradiction.
      destruct typecheck eqn:q1.
      2: contradiction.
      destruct typecheck eqn:q2 in p.
      2: contradiction.
      constructor.
      * apply typecheck_sound.
        rewrite q1.
        auto.
      * apply typecheck_sound.
        rewrite q2.
        auto.
    + constructor.
      destruct typeinfer eqn:q.
      2: contradiction.
      destruct eq_type.
      2: contradiction.
      subst.
      auto.
  - destruct e.
    all: cbn.
    all: intros ? ? p.
    all: inversion p.
    all: subst.
    all: clear p.
    + constructor.
      apply find_sound.
      auto.
    + destruct typeinfer eqn:q1.
      2: discriminate.
      destruct t0.
      all: try discriminate.
      destruct typecheck eqn:q2.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
      apply typecheck_sound.
      rewrite q2.
      cbv.
      auto.
    + destruct typecheck eqn:q2.
      2: discriminate.
      destruct typeinfer eqn:q1.
      2: discriminate.
      destruct t1.
      all: try discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
      apply typecheck_sound.
      rewrite q2.
      cbv.
      auto.
    + destruct typeinfer eqn:q1.
      2: discriminate.
      destruct t1.
      all: try discriminate.
      destruct typecheck eqn:q2.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
      apply typecheck_sound.
      rewrite q2.
      cbv.
      auto.
    + destruct typecheck eqn:q.
      2: discriminate.
      inversion H0.
      subst.
      constructor.
      apply typecheck_sound.
      rewrite q.
      apply I.
Qed.

Fixpoint usecheck_complete {E Δ Δ'} (p: Δ ⊢ E ⊠ Δ'):
  usecheck Δ E = Some Δ'
with useinfer_complete {e Δ Δ'} (p: se Δ e Δ'):
  useinfer Δ e = Some Δ'.
Proof using.
  - destruct p.
    all: cbn.
    all: try rewrite (usecheck_complete _ _ _ p).
    all: try rewrite (usecheck_complete _ _ _ p1).
    all: try rewrite (usecheck_complete _ _ _ p2).
    all: try rewrite (useinfer_complete _ _ _ H).
    all: auto.
    destruct eq_var.
    2: contradiction.
    auto.
  - destruct p.
    all: cbn.
    all: try rewrite (useinfer_complete _ _ _ p).
    all: try rewrite (usecheck_complete _ _ _ H).
    all: auto.
    + induction H.
      all: cbn.
      * destruct eq_var.
        2: contradiction.
        auto.
      * destruct eq_var.
        1: subst; contradiction.
        rewrite IHlmem.
        auto.
    + destruct eq_var.
      2: contradiction.
      destruct eq_var.
      2: contradiction.
      auto.
Qed.

Fixpoint typecheck_complete {Γ E t} (p: check Γ E t):
  typecheck Γ E t = true
with typeinfer_complete {Γ e t} (p: infer Γ e t):
  typeinfer Γ e = Some t.
Proof using.
  - destruct p.
    all: cbn.
    all: try rewrite (typecheck_complete _ _ _ p).
    all: try rewrite (typecheck_complete _ _ _ p1).
    all: try rewrite (typecheck_complete _ _ _ p2).
    all: try rewrite (typeinfer_complete _ _ _ H).
    all: auto.
    destruct eq_type.
    2: contradiction.
    auto.
  - destruct p.
    all: cbn.
    all: try rewrite (typeinfer_complete _ _ _ p).
    all: try rewrite (typecheck_complete _ _ _ H).
    all: auto.
    apply find_complete.
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

Definition useonce Γ u: usage := List.map (λ '(x, t), (x, u)) Γ.

Definition oftype Γ t :=
  { E |
    Bool.Is_true (
        typecheck Γ E t
        && if usecheck (useonce Γ u_unused) E is Some Δ
           then
             if eq_usage Δ (useonce Γ u_used) then true else false
           else
             false)
  }.

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
