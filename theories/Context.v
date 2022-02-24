Require Blech.Map.
Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Blech.OptionNotations.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Coq.Lists.List.

Require Import FunInd.

Import List.ListNotations.
Import IfNotations.

Implicit Type Δ: linear.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types X Y: cvar.
Implicit Type σ: store.

Import Map.MapNotations.

Section Typecheck.
  Import OptionNotations.

  Function typecheck Δ E: option (linear * type) :=
    match E with
    | E_var X =>
        do t ← Map.find X Δ ;
        Some (X ↦ t, t)
    | E_lam X t1 E =>
        do (Δ', t2) ← typecheck (X ↦ t1 ∪ Δ) E ;
        do t1' ← Map.find X Δ' ;
        if eq_type t1 t1'
        then
          Some (Δ' \ X, t1 * t2)
        else
          None
    | E_app E E' =>
        do (Δ', t1 * t2) ← typecheck Δ E ;
        do (Δ, t1') ← typecheck Δ E' ;
        if eq_type t1 t1'
        then
          Some (Δ' ∪ Δ, t2)
        else
          None

    | E_tt => Some (∅, t_unit)
    | E_step E E' =>
        do (Δ', t_unit) ← typecheck Δ E ;
        do (Δ, t) ← typecheck Δ E' ;
        Some (Δ' ∪ Δ, t)

    | E_fanout E E' =>
        do (Δ', t1) ← typecheck Δ E ;
        do (Δ, t2) ← typecheck Δ E' ;
        Some (Δ' ∪ Δ, t1 * t2)

    | E_let X Y E E' =>
        do (Δ', t1 * t2) ← typecheck Δ E ;
        do (Δ, t3) ← typecheck (X ↦ t1 ∪ Y ↦ t2 ∪ Δ) E' ;
        do t1' ← Map.find X (Δ \ Y) ;
        do t2' ← Map.find Y Δ ;
        if eq_type t1 t1'
        then
          if eq_type t2 t2'
          then
            Some (Δ' ∪ ((Δ \ Y) \ X), t3)
          else
            None
        else
          None
    end
      %list %map.
End Typecheck.

Notation "'do' x ← e0 ; e1" :=
  (List.flat_map (λ x, e1) e0)
    (x pattern, at level 200, left associativity): list_scope.

Fixpoint generate t :=
  match t with
  | t_unit => [N_tt]
  | t * t' =>
      do N ← generate t ;
      do N' ← generate t' ;
      [N_fanout N N']
  end%list.

Fixpoint search σ E: list span :=
  match E with
  | E_var X => if Map.find X σ is Some N then [X ↦ N |- N] else []

  | E_lam X t E =>
      do N0 ← generate t ;
      do (σ' |- N1) ← search (X ↦ N0 ∪ σ) E ;
      if Map.find X σ' is Some N0'
      then
        if eq_normal N0 N0'
        then
          [σ' \ X |- N_fanout N0 N1]
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

  | E_let X Y E E' =>
      do (σ1 |- N) ← search σ E ;
      do (a, b) ← (if N is N_fanout a b then [(a, b)] else []) ;
      do (σ2 |- N') ← search ((X ↦ a) ∪ (Y ↦ b) ∪ σ) E' ;
      if Map.find X (σ2 \ Y) is Some a'
      then
        if eq_normal a a'
        then
          if Map.find Y σ2 is Some b'
          then
            if eq_normal b b'
            then
              [σ1 ∪ ((σ2 \ Y) \ X) |- N']
            else
              []
          else
            []
        else
          []
      else
        []
  end%list %map.

Theorem typecheck_sound:
  ∀ Δ {E Δ' t}, typecheck Δ E = Some (Δ', t) → Δ' ⊢ E ? t.
Proof using.
  intros Δ E.
  functional induction (typecheck Δ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
  - apply IHo.
    rewrite Map.add_minus.
    all: auto.
  - rewrite Map.add_minus.
    all: auto.
    1: rewrite Map.add_minus.
    all: auto.
Qed.

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
    destruct (Map.find X σ) eqn:q.
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
    induction (IHE (X ↦ a ∪ σ)).
    1: constructor.
    cbn.
    destruct (Map.find X σ0) eqn:q.
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
    clear IHs0.
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
    induction (IHE2 (((X ↦ N1 ∪ Y ↦ N2) ∪ σ))).
    1: constructor.
    cbn.
    destruct (Map.find X (σ1 \ Y)) eqn:q.
    2: auto.
    destruct (eq_normal N1 n).
    2: auto.
    subst.
    destruct (Map.find Y σ1) eqn:q'.
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

Theorem search_sound_sat:
  ∀ {σ E N}, List.In (σ |- N) (search σ E) → sat σ E N.
Proof using.
  intros σ E.
  induction (search_sound σ E).
  all: cbn.
  1: contradiction.
  intros N' p.
  destruct p.
  2: auto.
  inversion H0.
  subst.
  auto.
Defined.


Inductive one :=
| o_hole
| o_lam (X: cvar) (t: type) (o: one)

| o_app_l (o: one) (E: context)
| o_app_r (E: context) (o: one)

| o_step_l (o: one) (E: context)
| o_step_r (E: context) (o: one)

| o_fanout_l (o: one) (E: context)
| o_fanout_r (E: context) (o: one)

| o_let_l (X Y: cvar) (o: one) (E: context)
| o_let_r (X Y: cvar) (E: context) (o: one)
.

Function D X E :=
  match E with
  | E_var Y => if eq_cvar X Y then Some o_hole else None

  | E_lam Y t E0 =>
      if eq_cvar X Y
      then
        None
      else
        if D X E0 is Some o'
        then
          Some (o_lam Y t o')
        else
          None

  | E_app E0 E1 =>
      match D X E0, D X E1 with
      | Some o, None => Some (o_app_l o E1)
      | None, Some o => Some (o_app_r E0 o)
      | _, _ => None
      end

  | E_tt => None

  | E_step E0 E1 =>
      match D X E0, D X E1 with
      | Some o, None => Some (o_step_l o E1)
      | None, Some o => Some (o_step_r E0 o)
      | _, _ => None
      end

  | E_fanout E0 E1 =>
      match D X E0, D X E1 with
      | Some o, None => Some (o_fanout_l o E1)
      | None, Some o => Some (o_fanout_r E0 o)
      | _, _ => None
      end

  | E_let Y0 Y1 E0 E1 =>
      if eq_cvar X Y0
      then
        if D X E0 is Some E0'
        then
          Some (o_let_l Y0 Y1 E0' E1)
        else
          None
      else
        if eq_cvar X Y1
        then
          if D X E0 is Some E0'
          then
            Some (o_let_l Y0 Y1 E0' E1)
          else
            None
        else
          match D X E0, D X E1 with
          | Some E0', None => Some (o_let_l Y0 Y1 E0' E1)
          | None, Some E1' => Some (o_let_r Y0 Y1 E0 E1')
          | _, _ => None
          end
  end.

Function I ES o :=
  match o with
  | o_hole => ES

  | o_lam X t o => E_lam X t (I ES o)

  | o_app_l o E => E_app (I ES o) E
  | o_app_r E o => E_app E (I ES o)

  | o_step_l o E => E_step (I ES o) E
  | o_step_r E o => E_step E (I ES o)

  | o_fanout_l o E => E_fanout (I ES o) E
  | o_fanout_r E o => E_fanout E (I ES o)

  | o_let_l X Y o E => E_let X Y (I ES o) E
  | o_let_r X Y E o => E_let X Y E (I ES o)
  end.

Lemma DI_preserve:
  ∀ {Δ' E' t},
    Δ' ⊢ E' ? t →
    ∀ {X E o Δ t'},
      Map.merge (Map.one X t) Δ ⊢ E ? t' →
      D X E = Some o →
      Map.merge Δ' Δ ⊢ I E' o ? t'.
Proof using.
  intros Δ' E' t p X.
  intros E.
  induction E.
  all: cbn.
  all: intros.
  - cbn.
    destruct eq_cvar.
    2: discriminate.
    subst.
    inversion H0.
    subst.
    inversion H.
    subst.
    cbn.
    set (H2' := Map.weaken H2 X0).
    rewrite Map.find_one in H2'.
    rewrite Map.find_add in H2'.
    destruct PeanoNat.Nat.eq_dec.
    2: contradiction.
    inversion H2'.
    subst.
    auto.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma subst_preserve:
  ∀ {Δ' E' t},
    Δ' ⊢ E' ? t →
    ∀ {X E Δ t'},
      Map.merge (Map.one X t) Δ ⊢ E ? t' →
      Map.merge Δ' Δ ⊢ subst_context E' X E ? t'.
Proof using.
  intros Δ' E' t p X.
  intros E.
  induction E.
  all: cbn.
  all: admit.
Admitted.

Lemma subst_var {X E}:
  subst_context (E_var X) X E = E.
Proof.
  induction E.
  all: cbn.
  all: auto.
  - destruct eq_cvar.
    all: auto.
  - rewrite IHE.
    destruct eq_cvar.
    all: auto.
  - rewrite IHE1, IHE2.
    auto.
  - rewrite IHE1, IHE2.
    auto.
  - rewrite IHE1, IHE2.
    auto.
  - rewrite IHE1, IHE2.
    destruct eq_cvar.
    1: auto.
    destruct eq_cvar.
    1: auto.
    auto.
Qed.

Lemma subst_assoc {X f g h}:
  subst_context (subst_context h X g) X f = subst_context h X (subst_context g X f).
Proof.
  induction f.
  all: cbn.
  all: auto.
  - destruct eq_cvar eqn:q.
    1: auto.
    cbn.
    rewrite q.
    auto.
  - rewrite IHf.
    destruct eq_cvar eqn:q.
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
    destruct eq_cvar.
    1: auto.
    destruct eq_cvar.
    1: auto.
    auto.
Qed.

Definition oftype Δ t := { E | Δ ⊢ E ? t }.

Definition equiv {Δ t}: Relation_Definitions.relation (oftype Δ t) :=
  λ a b,
    ∀ N,
      (* FIXME substitute in contexts *)
      sat Map.empty (proj1_sig a) N ↔ sat Map.empty (proj1_sig b) N.

Instance equiv_Reflexive Δ t: Reflexive (@equiv Δ t).
Proof using.
  unfold equiv.
  unfold Reflexive.
  intros.
  reflexivity.
Qed.

Instance equiv_Symmetric Δ t: Symmetric (@equiv Δ t).
Proof using.
  unfold equiv.
  unfold Symmetric.
  intros.
  symmetry.
  auto.
Qed.

Instance equiv_Transitive Δ t: Transitive (@equiv Δ t).
Proof using.
  unfold equiv.
  unfold Transitive.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Instance equiv_Equivalence Δ t: Equivalence (@equiv Δ t) := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid Δ t: Setoid (oftype Δ t) := {
    equiv := equiv ;
}.


Import RelNotations.

#[program]
 Definition id t: oftype Map.empty (t * t) :=
  let X: cvar := 0 in
   <{ λ X : t, X }>.

Next Obligation.
Proof.
  constructor.
  rewrite Map.merge_empty_r.
  constructor.
Qed.

#[program]
Definition conv {t t'} (E: oftype Map.empty (t * t')): oftype Map.empty (t' * t) :=
  let X: cvar := 0 in
  let Y: cvar := 1 in
  <{ let (X, Y) := E in (Y, X) }>.

Next Obligation.
Proof.
  destruct E.
  cbn.
  rewrite <- (@Map.merge_empty_l _ Map.empty).
  econstructor.
  all: eauto.
  constructor.
  - constructor.
  - rewrite Map.merge_empty_r.
    constructor.
Qed.

Lemma weaken {m m': store}:
  m = m' → ∀ k, Map.find k m = Map.find k m'.
Proof.
  intros.
  subst.
  auto.
Qed.

Lemma conv_id t:
  conv (id t) == id t.
Proof.
  unfold conv, id.
  cbn.
  unfold equiv.
  cbn.
  intros.
  split.
  - intros p.
    inversion p.
    subst.
    rewrite H.
    destruct (Map.merge_empty H).
    subst.
    rewrite Map.merge_empty_r in H6.
    inversion H5.
    subst.
    rewrite Map.merge_empty_r in H2.
    inversion H2.
    subst.
    destruct (Map.one_inj H1).
    subst.
    inversion H6.
    subst.
    constructor.
    rewrite Map.merge_empty_r.
    admit.
  - intros p.
    inversion p.
    subst.
    inversion H4.
    subst.
    rewrite <- (@Map.merge_empty_l _ Map.empty).
    econstructor.
    all: eauto.
    rewrite <- H0.
    rewrite Map.merge_empty_r in H0.
    destruct (Map.one_inj H0).
    subst.
    constructor.
    + constructor.
    + constructor.
Admitted.
