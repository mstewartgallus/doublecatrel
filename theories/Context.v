Require Blech.Map.
Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.Environment.
Require Import Blech.Category.
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
Implicit Types x y: var.
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
        do (Δ, t3) ← typecheck (X ↦ t1 ∪ (Y ↦ t2 ∪ Δ)) E' ;
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

  Definition env Δ E :=
    do (Δ', _) ← typecheck Δ E ;
    Some Δ'.
End Typecheck.

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

Module Dec.
  Inductive context: Map.map type → type → Set :=
  | E_var x t: context (Map.one x t) t
  | E_lam {Δ t'} x t (E: context (Map.one x t ∪ Δ) t'): context Δ (t * t')
  | E_app {Δ Δ' t t'} (E: context Δ (t * t')) (E': context Δ' t): context (Δ ∪ Δ') t'
  | E_tt: context Map.empty t_unit
  | E_step {Δ Δ' t} (E: context Δ t_unit) (E': context Δ' t): context (Δ ∪ Δ') t
  | E_fanout {Δ Δ' t t'} (E: context Δ t) (E': context Δ' t'): context (Δ ∪ Δ') (t * t')
  | E_let {Δ Δ' t t' t2} x y (E: context Δ (t * t')) (E': context (Map.one y t' ∪ (Map.one x t ∪ Δ')) t2): context (Δ ∪ Δ') t2.

  Program Fixpoint dec Δ Δ' t E (p: typecheck Δ E = Some (Δ', t)): context Δ' t :=
    match E with
    | Spec.E_var x => E_var x _

    | Spec.E_lam x t E =>
        if typecheck (Map.one x t ∪ Δ) E is Some (Δ', t')
        then
            @E_lam (Δ' \ x) t' x t (dec (Map.one x t ∪ Δ) Δ' t' E _)
        else
          match _: False with end
    | Spec.E_app E E' =>
        match typecheck Δ E, typecheck Δ E' with
        | Some (Δ1, t1 * t2), Some (Δ2, t1') =>
            @E_app _ _ t1 t2 (dec Δ Δ1 (t1 * t2) E _) (dec Δ Δ2 t1' E' _)
        | _, _ => match _: False with end
        end

    | Spec.E_tt => E_tt

    | Spec.E_step E E' =>
        match typecheck Δ E, typecheck Δ E' with
        | Some (Δ1, t_unit), Some (Δ2, t) =>
            E_step (dec Δ Δ1 t_unit E _) (dec Δ Δ2 t E' _)
        | _, _ => match _: False with end
        end

    | Spec.E_fanout E E' =>
        match typecheck Δ E, typecheck Δ E' with
        | Some (Δ1, t), Some (Δ2, t') =>
            @E_fanout _ _ t t' (dec Δ Δ1 t E _) (dec Δ Δ2 t' E' _)
        | _, _ => match _: False with end
        end

    | Spec.E_let x y E E' =>
        if typecheck Δ E is Some (Δ1, t1 * t2)
        then
          if typecheck (Map.one x t1 ∪ (Map.one y t2 ∪ Δ)) E' is Some (Δ2, t3)
          then
            @E_let Δ1 ((Δ2 \ y) \ x) t1 t2 t3 x y
                   (dec Δ Δ1 (t1 * t2) E _)
                   (dec (Map.one x t1 ∪ (Map.one y t2 ∪ Δ)) Δ2 t3 E' _)
          else
            match _: False with end
        else
          match _: False with end
    end %map.

  Next Obligation.
  Proof.
    cbn in p.
    destruct (Map.find x Δ).
    all: inversion p.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous in p.
    destruct (Map.find x Δ') eqn:q.
    2: discriminate.
    destruct eq_type.
    2: discriminate.
    subst.
    inversion p.
    subst.
    rewrite Map.add_minus.
    all: auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous in p.
    destruct (Map.find x Δ') eqn:q.
    2: discriminate.
    destruct eq_type.
    2: discriminate.
    subst.
    inversion p.
    subst.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous in p.
    destruct (Map.find x Δ') eqn:q.
    2: discriminate.
    destruct eq_type.
    2: discriminate.
    subst.
    inversion p.
    subst.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    destruct typecheck eqn:q.
    2: discriminate.
    destruct p0.
    destruct Map.find eqn:r.
    2: discriminate.
    set (H' := H l t1).
    contradiction.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous in p.
    rewrite <- Heq_anonymous0 in p.
    destruct eq_type.
    2: discriminate.
    inversion p.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous in p.
    rewrite <- Heq_anonymous0 in p.
    destruct eq_type.
    2: discriminate.
    inversion p.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous in p.
    rewrite <- Heq_anonymous0 in p.
    destruct eq_type.
    2: discriminate.
    inversion p.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    destruct typecheck eqn:q in p.
    2: discriminate.
    destruct p0.
    destruct t0.
    1: discriminate.
    destruct typecheck eqn:q' in p.
    2: discriminate.
    destruct p0.
    destruct eq_type.
    2: discriminate.
    inversion p.
    subst.
    set (H' := H l t0 t l0 t0).
    rewrite q in H'.
    rewrite q' in H'.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous in p.
    rewrite <- Heq_anonymous0 in p.
    inversion p.
    subst.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous in p.
    rewrite <- Heq_anonymous0 in p.
    inversion p.
    subst.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    destruct typecheck eqn:q in p.
    2: discriminate.
    destruct p0.
    destruct t0.
    2: discriminate.
    destruct typecheck eqn:q' in p.
    2: discriminate.
    destruct p0.
    inversion p.
    subst.
    set (H' := H l l0 t).
    rewrite q in H'.
    rewrite q' in H'.
    apply H'.
    all: split.
    all: auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous in p.
    rewrite <- Heq_anonymous0 in p.
    inversion p.
    subst.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous in p.
    rewrite <- Heq_anonymous0 in p.
    inversion p.
    subst.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    destruct typecheck eqn:q in p.
    2: discriminate.
    destruct p0.
    destruct typecheck eqn:q' in p.
    2: discriminate.
    destruct p0.
    set (H' := H l t0 l0 t1).
    rewrite q in H'.
    rewrite q' in H'.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous0 in p.
    rewrite <- Heq_anonymous in p.
    apply Map.extensional.
    intro k.
    repeat rewrite Map.find_merge.
    repeat rewrite Map.find_one.
    repeat rewrite Map.find_minus.
    rewrite Map.find_minus in p.
    destruct Nat.eq_dec in p.
    1: discriminate.
    destruct Map.find eqn:q in p.
    2: discriminate.
    destruct Map.find eqn:q' in p.
    2: discriminate.
    destruct eq_type in p.
    2: discriminate.
    subst.
    destruct eq_type in p.
    2: discriminate.
    subst.
    inversion p.
    subst.
    destruct Nat.eq_dec.
    2: destruct Nat.eq_dec.
    all: subst.
    all: auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous0 in p.
    rewrite <- Heq_anonymous in p.
    apply Map.extensional.
    intro k.
    repeat rewrite Map.find_merge.
    repeat rewrite Map.find_one.
    repeat rewrite Map.find_minus.
    rewrite Map.find_minus in p.
    destruct Nat.eq_dec in p.
    1: discriminate.
    destruct Map.find eqn:q in p.
    2: discriminate.
    destruct Map.find eqn:q' in p.
    2: discriminate.
    destruct eq_type in p.
    2: discriminate.
    subst.
    destruct eq_type in p.
    2: discriminate.
    subst.
    inversion p.
    subst.
    repeat rewrite Map.find_merge.
    repeat rewrite Map.find_minus.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous0 in p.
    rewrite <- Heq_anonymous in p.
    rewrite Map.find_minus in p.
    destruct Nat.eq_dec in p.
    1: discriminate.
    destruct Map.find eqn:q in p.
    2: discriminate.
    destruct Map.find eqn:q' in p.
    2: discriminate.
    destruct eq_type in p.
    2: discriminate.
    subst.
    destruct eq_type in p.
    2: discriminate.
    subst.
    inversion p.
    subst.
    auto.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    rewrite <- Heq_anonymous0 in p.
    destruct typecheck eqn:q in p.
    2: discriminate.
    destruct p0.
    rewrite Map.find_minus in p.
    destruct Nat.eq_dec in p.
    1: discriminate.
    destruct Map.find eqn:q' in p.
    2: discriminate.
    destruct Map.find eqn:q'' in p.
    2: discriminate.
    destruct eq_type in p.
    2: discriminate.
    subst.
    destruct eq_type in p.
    2: discriminate.
    subst.
    set (H' := H l t0).
    rewrite q in H'.
    contradiction.
  Defined.

  Next Obligation.
  Proof.
    cbn in p.
    destruct typecheck eqn:q in p.
    2: discriminate.
    destruct p0.
    destruct t0.
    1: discriminate.
    destruct typecheck eqn:q' in p.
    2: discriminate.
    destruct p0.
    rewrite Map.find_minus in p.
    destruct Nat.eq_dec in p.
    1: discriminate.
    destruct Map.find eqn:q'' in p.
    2: discriminate.
    destruct Map.find eqn:q''' in p.
    2: discriminate.
    destruct eq_type in p.
    2: discriminate.
    subst.
    destruct eq_type in p.
    2: discriminate.
    subst.
    inversion p.
    subst.
    set (H' := H l t1 t2).
    rewrite q in H'.
    contradiction.
  Defined.

  Fixpoint undec {Δ t} (E: context Δ t) :=
    match E with
    | E_var x _ => Spec.E_var x
    | E_lam x t E => Spec.E_lam x t (undec E)
    | E_app E E' => Spec.E_app (undec E) (undec E')
    | E_tt => Spec.E_tt
    | E_step E E' => Spec.E_step (undec E) (undec E')
    | E_fanout E E' => Spec.E_fanout (undec E) (undec E')
    | E_let x y E E' => Spec.E_let x y (undec E) (undec E')
    end.

  Definition wf {Δ t} (E: context Δ t): Δ ⊢ undec E ? t.
  Proof.
    induction E.
    all: cbn.
    all: econstructor.
    all: eauto.
  Qed.
End Dec.

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

Definition oftype Δ t := { E | Δ ⊢ E ? t }.

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
