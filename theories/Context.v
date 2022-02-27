Require Blech.Map.
Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Blech.OptionNotations.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Import Coq.Logic.PropExtensionality.

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

Function find X Δ :=
  if Δ is ((Y, t) :: T)%list
  then
    if eq_cvar X Y
    then
      Some t
    else
      find X T
  else
    None.

Variant occurs := zero | one | many.

Definition add a b :=
  match a, b with
  | zero, zero => zero
  | many, _ => many
  | _, many => many
  | one, one => many
  | _, _ => one
  end.

Infix "+" := add.

Function count X E :=
  match E with
  | E_var Y => if eq_cvar X Y then one else zero

  | E_lam Y t E =>
      if eq_cvar X Y then zero else count X E

  | E_app E E' => count X E + count X E'

  | E_tt => zero

  | E_step E E' => count X E + count X E'

  | E_fanout E E' => count X E + count X E'

  | E_let Y Y' E E' =>
      if eq_cvar X Y
      then
        count X E
      else
        if eq_cvar X Y'
        then
          count X E
        else
          count X E + count X E'
  end.

Section Typecheck.
  Import OptionNotations.

  Function typecheck Δ E: option type :=
    match E with
    | E_var X => find X Δ

    | E_lam X t1 E =>
        do t2 ← typecheck ((X, t1) :: Δ) E ;
        if count X E is one
        then
          Some (t1 * t2)
        else
          None
    | E_app E E' =>
        do (t1 * t2) ← typecheck Δ E ;
        do t1' ← typecheck Δ E' ;
        if eq_type t1 t1'
        then
          Some t2
        else
          None

    | E_tt => Some t_unit
    | E_step E E' =>
        do t_unit ← typecheck Δ E ;
        do t ← typecheck Δ E' ;
        Some t

    | E_fanout E E' =>
        do t1 ← typecheck Δ E ;
        do t2 ← typecheck Δ E' ;
        Some (t1 * t2)

    | E_let X Y E E' =>
        do (t1 * t2) ← typecheck Δ E ;
        do t3 ← typecheck ((Y, t2) :: (X, t1) :: Δ) E' ;
        if count X E' is one
        then
          if count Y E' is one
          then
            Some t3
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

Theorem count_complete_never:
  ∀ {X E}, never X E → count X E = zero.
Proof using.
  intros ? ? p.
  induction p.
  all: cbn.
  all: try destruct eq_cvar.
  all: subst.
  all: try contradiction.
  all: auto.
  all: try rewrite IHp.
  all: cbn.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: cbn.
  all: auto.
  all: try destruct eq_cvar.
  all: subst.
  all: try contradiction.
  all: auto.
Qed.

Theorem count_complete_one:
  ∀ {X E}, once X E → count X E = one.
Proof using.
  intros ? ? p.
  induction p.
  all: cbn.
  all: try destruct eq_cvar.
  all: subst.
  all: try contradiction.
  all: auto.
  all: try rewrite IHp.
  all: cbn.
  all: try destruct eq_cvar.
  all: subst.
  all: try contradiction.
  all: try rewrite count_complete_never.
  all: auto.
Qed.

Theorem count_sound:
  ∀ {X E}, match count X E with
           | one => once X E
           | zero => never X E
           | many => True
           end.
Proof using.
  intros X E.
  functional induction (count X E).
  - constructor.
  - constructor.
    auto.
  - constructor.
  - destruct (count X E0).
    all: auto.
    + constructor.
      all: auto.
    + constructor.
      all: auto.
  - destruct (count X E0), (count X E').
    all: cbn.
    all: auto.
    + constructor.
      all: auto.
    + apply once_app_r.
      all: auto.
    + apply once_app_l.
      all: auto.
  - constructor.
  - destruct (count X E0), (count X E').
    all: cbn.
    all: auto.
    + constructor.
      all: auto.
    + apply once_step_r.
      all: auto.
    + apply once_step_l.
      all: auto.
  - destruct (count X E0), (count X E').
    all: cbn.
    all: auto.
    + constructor.
      all: auto.
    + apply once_fanout_r.
      all: auto.
    + apply once_fanout_l.
      all: auto.
  - destruct (count X E0).
    all: auto.
    + apply never_let_eq_1.
      auto.
    + apply once_let_l1.
      auto.
  - destruct (count X E0).
    all: auto.
    + apply never_let_eq_2.
      auto.
    + apply once_let_l2.
      auto.
  - destruct (count X E0), (count X E').
    all: cbn.
    all: auto.
    + constructor.
      all: auto.
    + apply once_let_r.
      all: auto.
    + apply once_let_l.
      all: auto.
Qed.

Corollary count_once:
  ∀ {X E}, count X E = one → once X E.
Proof.
  intros ? ? p.
  set (H := @count_sound X E).
  rewrite p in H.
  auto.
Qed.

Corollary count_never:
  ∀ {X E}, count X E = zero → never X E.
Proof.
  intros ? ? p.
  set (H := @count_sound X E).
  rewrite p in H.
  auto.
Qed.

Lemma find_sound:
  ∀ {X Δ t},
    find X Δ = Some t → Emem X t Δ.
Proof.
  intros X Δ.
  functional induction (find X Δ).
  all: intros ? p.
  - inversion p.
    subst.
    constructor.
  - constructor.
    all: auto.
  - discriminate.
Qed.

Lemma find_complete:
  ∀ {X Δ t},
    Emem X t Δ → find X Δ = Some t .
Proof.
  intros X Δ t p.
  induction p.
  all: cbn.
  all: destruct eq_cvar.
  all: subst.
  all: try contradiction.
  all: auto.
Qed.

Theorem typecheck_sound:
  ∀ Δ {E t}, typecheck Δ E = Some t → JE Δ E t.
Proof using.
  intros Δ E.
  functional induction (typecheck Δ E).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
  - apply find_sound.
    auto.
  - apply count_once.
    auto.
  - apply count_once.
    auto.
  - apply count_once.
    auto.
Qed.

Theorem typecheck_complete:
  ∀ {Δ E t}, JE Δ E t → typecheck Δ E = Some t.
Proof using.
  intros Δ E t p.
  induction p.
  all: cbn.
  all: auto.
  - apply find_complete.
    auto.
  - rewrite IHp.
    rewrite count_complete_one.
    all: auto.
  - rewrite IHp1, IHp2.
    destruct eq_type.
    2: contradiction.
    auto.
  - rewrite IHp1, IHp2.
    auto.
  - rewrite IHp1, IHp2.
    auto.
  - rewrite IHp1, IHp2.
    rewrite count_complete_one.
    2: auto.
    rewrite count_complete_one.
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

Definition oftype Δ t := { E | JE Δ E t }.

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
