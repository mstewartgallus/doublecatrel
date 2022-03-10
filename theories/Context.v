Require Blech.Map.
Require Blech.Sets.
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

Implicit Type Γ: environment.
Implicit Type Δ: linear.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types x y: var.
Implicit Type σ: store.

Import Map.MapNotations.
Import Sets.SetNotations.

Section Typecheck.
  Import OptionNotations.

  Function typecheck Γ E: option (linear * type) :=
    match E with
    | E_var x =>
        do t ← find x Γ ;
        Some (Sets.one x, t)
    | E_lam x t1 E =>
        do (Δ', t2) ← typecheck ((x, t1) :: Γ) E ;
        if Sets.find x Δ'
        then
          Some (Δ' \ x, t1 * t2)
        else
          None
    | E_app E E' =>
        do (Δ', t1 * t2) ← typecheck Γ E ;
        do (Δ, t1') ← typecheck Γ E' ;
        if eq_type t1 t1'
        then
          Some (Δ' ∪ Δ, t2)
        else
          None

    | E_tt => Some (∅, t_unit)
    | E_step E E' =>
        do (Δ', t_unit) ← typecheck Γ E ;
        do (Δ, t) ← typecheck Γ E' ;
        Some (Δ' ∪ Δ, t)

    | E_fanout E E' =>
        do (Δ', t1) ← typecheck Γ E ;
        do (Δ, t2) ← typecheck Γ E' ;
        Some (Δ' ∪ Δ, t1 * t2)

    | E_let x y E E' =>
        do (Δ', t1 * t2) ← typecheck Γ E ;
        do (Δ, t3) ← typecheck ((y, t2) :: (x, t1) :: Γ) E' ;
        if (Sets.find x (Δ \ y) && Sets.find y Δ) %bool
        then
          Some (Δ' ∪ ((Δ \ y) \ x), t3)
        else
          None
    end
      %list %set.
End Typecheck.

Theorem typecheck_sound:
  ∀ Γ {E Δ' t}, typecheck Γ E = Some (Δ', t) → JE Γ Δ' E t.
Proof using.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
  - apply find_sound.
    auto.
  - rewrite Sets.add_minus.
    all: auto.
  - destruct Sets.find eqn:qx in e2.
    2: discriminate.
    destruct Sets.find eqn:qy in e2.
    2: discriminate.
    repeat rewrite Sets.add_minus.
    all: auto.
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

Inductive notin {A} (a: A): list A → Prop :=
| notin_empty: notin a nil
| notin_cons a' T: a ≠ a' → notin a T → notin a (cons a' T).

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

Fixpoint useall Γ: linear :=
  if Γ is cons (x, _) T
  then
    Sets.merge (Sets.one x) (useall T)
  else
    Sets.empty.

Definition oftype Γ t := { E | JE Γ (useall Γ) E t }.
