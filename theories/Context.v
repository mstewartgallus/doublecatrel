Require Blech.Map.
Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.Environment.
Require Blech.OptionNotations.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Import Coq.Logic.PropExtensionality.

Require Import FunInd.

Import List.ListNotations.
Import IfNotations.

Implicit Type Γ: environment.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types x y: var.
Implicit Type σ: store.

Import Map.MapNotations.

Variant occurs := zero | one | many.

Definition add a b :=
  match a, b with
  | zero, zero => zero
  | many, _ => many
  | _, many => many
  | one, one => many
  | _, _ => one
  end.

Section count.
  Infix "+" := add.

  Function count x E :=
    match E with
    | E_var y => if eq_var x y then one else zero
    | E_lam y t E => if eq_var x y then zero else count x E
    | E_app E E' => count x E + count x E'
    | E_tt => zero
    | E_step E E' => count x E + count x E'
    | E_fanout E E' => count x E + count x E'
    | E_let y y' E E' =>
        if eq_var x y
        then
          count x E
        else
          if eq_var x y'
          then
            count x E
          else
            count x E + count x E'
    end.
End count.

Section Typecheck.
  Import OptionNotations.

  Function typecheck Γ E: option type :=
    match E with
    | E_var x => find x Γ

    | E_lam x t1 E =>
        do t2 ← typecheck ((x, t1) :: Γ) E ;
        Some (t1 * t2)
    | E_app E E' =>
        do (t1 * t2) ← typecheck Γ E ;
        do t1' ← typecheck Γ E' ;
        if eq_type t1 t1'
        then
          Some t2
        else
          None

    | E_tt => Some t_unit
    | E_step E E' =>
        do t_unit ← typecheck Γ E ;
        do t ← typecheck Γ E' ;
        Some t

    | E_fanout E E' =>
        do t1 ← typecheck Γ E ;
        do t2 ← typecheck Γ E' ;
        Some (t1 * t2)

    | E_let x y E E' =>
        do (t1 * t2) ← typecheck Γ E ;
        do t3 ← typecheck ((y, t2) :: (x, t1) :: Γ) E' ;
        Some t3
    end
      %list %map.
End Typecheck.

Function lincheck E :=
  match E with
  | E_var _ => true

  | E_lam x _ E =>
      lincheck E &&
        if count x E is one then true else false
  | E_app E E' =>
      lincheck E && lincheck E'

  | E_tt => true

  | E_step E E' =>
      lincheck E && lincheck E'

  | E_fanout E E' =>
      lincheck E && lincheck E'

  | E_let x y E E' =>
      lincheck E &&
        lincheck E' &&
        (if count x E' is one then true else false) &&
        (if count y E' is one then true else false)
  end
    %bool %list.

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

Theorem count_complete_never {x E}: never x E → count x E = zero.
Proof using.
  intros p.
  induction p.
  all: cbn.
  all: try destruct eq_var.
  all: subst.
  all: try contradiction.
  all: auto.
  all: try rewrite IHp.
  all: cbn.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: cbn.
  all: auto.
  all: try destruct eq_var.
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
  all: try destruct eq_var.
  all: try destruct eq_var.
  all: subst.
  all: try contradiction.
  all: auto.
  all: try rewrite IHp.
  all: cbn.
  all: try contradiction.
  all: try rewrite count_complete_never.
  all: auto.
Qed.

Theorem count_sound:
  ∀ {x E}, match count x E with
           | one => once x E
           | zero => never x E
           | many => True
           end.
Proof using.
  intros x E.
  functional induction (count x E).
  - constructor.
  - constructor.
    auto.
  - constructor.
  - destruct (count x E0).
    all: auto.
    + constructor.
      all: auto.
    + constructor.
      all: auto.
  - destruct (count x E0), (count x E').
    all: cbn.
    all: auto.
    + constructor.
      all: auto.
    + apply once_app_r.
      all: auto.
    + apply once_app_l.
      all: auto.
  - constructor.
  - destruct (count x E0), (count x E').
    all: cbn.
    all: auto.
    + constructor.
      all: auto.
    + apply once_step_r.
      all: auto.
    + apply once_step_l.
      all: auto.
  - destruct (count x E0), (count x E').
    all: cbn.
    all: auto.
    + constructor.
      all: auto.
    + apply once_fanout_r.
      all: auto.
    + apply once_fanout_l.
      all: auto.
  - destruct (count x E0).
    all: auto.
    + apply never_let_eq_1.
      all: auto.
    + apply once_let_l1.
      all: auto.
  - destruct (count x E0).
    all: auto.
    + apply never_let_eq_2.
      all: auto.
    + apply once_let_l2.
      all: auto.
  - destruct (count x E0), (count x E').
    all: cbn.
    all: auto.
    + constructor.
      all: auto.
    + apply once_let_r.
      all: auto.
    + apply once_let_l.
      all: auto.
Qed.

Corollary count_once {x E}: count x E = one → once x E.
Proof using.
  intros p.
  set (H := @count_sound x E).
  rewrite p in H.
  auto.
Qed.

Corollary count_never {x E}: count x E = zero → never x E.
Proof using.
  intros p.
  set (H := @count_sound x E).
  rewrite p in H.
  auto.
Qed.

Theorem lincheck_sound:
  ∀ {E}, lincheck E = true → JL E.
Proof using.
  intros E.
  induction E.
  all: cbn.
  all: intros p.
  all: try discriminate.
  all: subst.
  - constructor.
  - destruct (lincheck E), (count x E) eqn:q.
    all: try discriminate.
    constructor.
    all: auto.
    apply count_once.
    auto.
  - destruct (lincheck E1), (lincheck E2).
    all: try discriminate.
    constructor.
    all: auto.
  - constructor.
  - destruct (lincheck E1), (lincheck E2).
    all: try discriminate.
    constructor.
    all: auto.
  - destruct (lincheck E1), (lincheck E2).
    all: try discriminate.
    constructor.
    all: auto.
  - destruct (lincheck E1), (lincheck E2), (count x E2) eqn:qx, (count y E2) eqn:qy.
    all: try discriminate.
    constructor.
    all: auto.
    all: apply count_once.
    all: auto.
Qed.

Theorem lincheck_complete:
  ∀ {E}, JL E → lincheck E = true.
Proof using.
  intros ? p.
  induction p.
  all: cbn.
  all: auto.
  all: try rewrite IHp.
  all: cbn.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: cbn.
  all: auto.
  all: rewrite count_complete_one.
  all: auto.
  all: rewrite count_complete_one.
  all: auto.
Qed.

Theorem typecheck_sound:
  ∀ Γ {E t}, typecheck Γ E = Some t → JE Γ E t.
Proof using.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
  apply find_sound.
  auto.
Qed.

Theorem typecheck_complete:
  ∀ {Γ E t}, JE Γ E t → typecheck Γ E = Some t.
Proof using.
  intros Γ E t p.
  induction p.
  all: cbn.
  all: auto.
  - apply find_complete.
    auto.
  - rewrite IHp.
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
    auto.
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

Lemma map:
  ∀ {E t Γ Δ},
    (∀ x t, mem x t Γ → mem x t Δ) →
    JE Γ E t →
    JE Δ E t.
Proof.
  intro E.
  induction E.
  all: intros ? ? ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
  - refine (IHE _ _ _ _ H5).
    intros ? ? q.
    inversion q.
    all: subst.
    all: constructor.
    all: auto.
  - refine (IHE2 _ _ _ _ H7).
    intros ? ? q.
    inversion q.
    all: subst.
    all: constructor.
    all: auto.
    inversion H8.
    all: subst.
    all: constructor.
    all: auto.
Qed.

Definition shadow {E Γ x t0 t1 t2}:
  JE ((x, t0) :: Γ)%list E t2 → JE ((x, t0) :: (x, t1) :: Γ)%list E t2 :=
  map Environment.shadow.

Definition unshadow {E Γ x t0 t1 t2}:
  JE ((x, t0) :: (x, t1) :: Γ)%list E t2 → JE ((x, t0) :: Γ)%list E t2 :=
  map Environment.unshadow.

Lemma subst_linear_never {E' x E}:
  never x E → never x (subst_context E' x E).
Proof.
  intros p.
  induction E.
  all: cbn.
  all: inversion p.
  all: subst.
  - destruct eq_var.
    all: auto.
    subst.
    contradiction.
  - destruct eq_var.
    + subst.
      constructor.
    + constructor.
      all: auto.
  - destruct eq_var.
    all: subst.
    + constructor.
    + constructor.
      all: auto.
  - constructor.
    all: auto.
  - constructor.
    all: auto.
  - constructor.
    all: auto.
  - constructor.
    all: auto.
  - destruct eq_var.
    all: try destruct eq_var.
    all: subst.
    + apply never_let_eq_1.
      all: auto.
    + apply never_let_eq_2.
      all: auto.
    + constructor.
      all: auto.
  - destruct eq_var.
    all: try destruct eq_var.
    all: subst.
    + apply never_let_eq_1.
      all: auto.
    + apply never_let_eq_2.
      all: auto.
    + contradiction.
  - destruct eq_var.
    all: try destruct eq_var.
    all: subst.
    + apply never_let_eq_1.
      all: auto.
    + apply never_let_eq_2.
      all: auto.
    + contradiction.
Qed.

Lemma subst_linear {E' x E}:
  once x E' →
  once x E → once x (subst_context E' x E).
Proof.
  intro q.
  induction E.
  all: cbn.
  all: intros p.
  all: inversion p.
  all: subst.
  - destruct eq_var.
    2: contradiction.
    auto.
  - destruct eq_var.
    1: subst; contradiction.
    constructor.
    all: auto.
  - apply once_app_l.
    all: auto.
    apply subst_linear_never.
    auto.
  - apply once_app_r.
    all: auto.
    apply subst_linear_never.
    auto.
  - apply once_step_l.
    all: auto.
    apply subst_linear_never.
    auto.
  - apply once_step_r.
    all: auto.
    apply subst_linear_never.
    auto.
  - apply once_fanout_l.
    all: auto.
    apply subst_linear_never.
    auto.
  - apply once_fanout_r.
    all: auto.
    apply subst_linear_never.
    auto.
  - destruct eq_var.
    all: subst.
    1: contradiction.
    destruct eq_var.
    all: subst.
    1: contradiction.
    apply once_let_l.
    all: auto.
    apply subst_linear_never.
    auto.
  - destruct eq_var.
    all: subst.
    2: contradiction.
    apply once_let_l1.
    all: auto.
  - destruct eq_var.
    all: subst.
    + apply once_let_l1.
      all: auto.
    + destruct eq_var.
      all: subst.
      2: contradiction.
      apply once_let_l2.
      auto.
  - destruct eq_var.
    all: subst.
    1: contradiction.
    destruct eq_var.
    all: subst.
    1: contradiction.
    apply once_let_r.
    all: auto.
    apply subst_linear_never.
    auto.
Qed.

Lemma subst_preserve:
  ∀ {Γ E' t x},
    Γ ⊢ E' ? t →
  ∀ {E t'},
    cons (x, t) Γ ⊢ E ? t' →
    Γ ⊢ subst_context E' x E ? t'.
Proof using.
  intros Γ E' t x p E.
  induction E.
  all: cbn.
  all: intros t' q.
  all: admit.
Admitted.

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

Definition oftype Γ t := { E | JE Γ E t ∧ JL E }.

Definition equiv {Γ t}: Relation_Definitions.relation (oftype Γ t) :=
  λ a b,
    ∀ N,
      (* FIXME substitute in contexts *)
      sat Map.empty (proj1_sig a) N ↔ sat Map.empty (proj1_sig b) N.

Instance equiv_Reflexive Γ t: Reflexive (@equiv Γ t).
Proof using.
  unfold equiv.
  unfold Reflexive.
  intros.
  reflexivity.
Qed.

Instance equiv_Symmetric Γ t: Symmetric (@equiv Γ t).
Proof using.
  unfold equiv.
  unfold Symmetric.
  intros.
  symmetry.
  auto.
Qed.

Instance equiv_Transitive Γ t: Transitive (@equiv Γ t).
Proof using.
  unfold equiv.
  unfold Transitive.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Instance equiv_Equivalence Γ t: Equivalence (@equiv Γ t) := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid Γ t: Setoid (oftype Γ t) := {
    equiv := equiv ;
}.
