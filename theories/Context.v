Require Import Blech.Spec.
Require Blech.Map.
Require Import Blech.SpecNotations.

Require Import Coq.Classes.SetoidClass.
Require Coq.Lists.List.

Require Import FunInd.

Import List.ListNotations.
Import IfNotations.

Function typecheck (Γ: linear) (E: context): option (linear * type) :=
  match E with
  | E_var x =>
      if Map.find x Γ is Some t
      then
          Some (Map.one x t, t)
      else
        None
  | E_lam x t1 E =>
      if typecheck (Map.add x t1 Γ) E is Some (Γ', t2)
      then
        if Map.find x Γ' is Some t1'
        then
          if eq_type t1 t1'
          then
              Some (Map.minus x Γ', t1 * t2)
          else
            None
        else
          None
      else
        None
  | E_app E E' =>
      if typecheck Γ E is Some (Γ', t1 * t2)
      then
        if typecheck Γ E' is Some (Δ, t1')
        then
          if eq_type t1 t1'
          then
            Some (Map.merge Γ' Δ, t2)
          else
            None
        else
          None
      else
        None

  | E_tt => Some (Map.empty, t_unit)
  | E_step E E' =>
      if typecheck Γ E is Some (Γ', t_unit)
      then
        if typecheck Γ E' is Some (Δ, t)
        then
          Some (Map.merge Γ' Δ, t)
        else
          None
      else
        None

  | E_fanout E E' =>
      if typecheck Γ E is Some (Γ', t1)
      then
        if typecheck Γ E' is Some (Δ, t2)
        then
          Some (Map.merge Γ' Δ, t_prod t1 t2)
        else
          None
      else
        None

  | E_let x y E E' =>
      if typecheck Γ E is Some (Γ', t1 * t2)
      then
        if typecheck (Map.add x t1 (Map.add y t2 Γ)) E' is Some (Δ, t3)
        then
          if Map.find x (Map.minus y Δ) is Some t1'
          then
            if eq_type t1 t1'
            then
              if Map.find y Δ is Some t2'
              then
                if eq_type t2 t2'
                then
                  Some (Map.merge Γ' (Map.minus x (Map.minus y Δ)), t3)
                else
                  None
              else
                None
            else
              None
          else
            None
        else
          None
      else
        None
  end
    %list.

Theorem typecheck_sound:
  forall Γ {E Δ t}, typecheck Γ E = Some (Δ, t) -> Δ ⊢ E ? t.
Proof using.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
  - apply IHo.
    rewrite (Map.add_minus x t1 Γ').
    2: auto.
    auto.
  - rewrite Map.add_minus.
    all: auto.
    1: rewrite Map.add_minus.
    all: auto.
Qed.

Definition eq_normal (x y: normal): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Notation "'do' x <- e0 ; e1" := (List.flat_map (fun x => e1) e0) (x pattern, at level 200, left associativity).

Fixpoint app {A B} (f: list (A -> B)) x: list _ :=
  if f is cons H T
  then
    List.app (List.map H x) (app T x)
  else
    nil%list.

Infix "<*>" := app (at level 30).

Fixpoint generate (t: type): list normal :=
  match t with
  | t_unit => [N_tt]
  | A * B => [N_fanout] <*> generate A <*> generate B
  end%list.

Fixpoint search (σ: Map.map normal) E: list span :=
  match E with
  | E_var x => if Map.find x σ is Some N then [Map.one x N |- N] else []

  | E_lam x t E =>
      do N0 <- generate t ;
      do (σ' |- N1) <- search (Map.add x N0 σ) E ;
      if Map.find x σ' is Some N0'
      then
        if eq_normal N0 N0'
        then
          [Map.minus x σ' |- N_fanout N0 N1]
        else
          []
      else
        []

  | E_app E E' =>
      do (σ1 |- N) <- search σ E ;
      do (σ2 |- N0) <- search σ E' ;
      if N is N_fanout N0' N1
      then
        if eq_normal N0 N0'
        then
          [Map.merge σ1 σ2 |- N1]
        else
          []
      else
        []

  | E_tt => [Map.empty |- N_tt]

  | E_step E E' =>
      do (σ1 |- N) <- search σ E ;
      if N is N_tt
      then
        [fun '(σ2 |- N') => Map.merge σ1 σ2 |- N'] <*> search σ E'
      else
        []

  | E_fanout E E' =>
      [fun '(σ1 |- N) '(σ2 |- N') => Map.merge σ1 σ2 |- N_fanout N N'] <*> search σ E <*> search σ E'

  | E_let x y E E' =>
      do (σ1 |- N) <- search σ E ;
      do (a, b) <- (if N is N_fanout a b then [(a, b)] else []) ;
      do (σ2 |- N') <- search (Map.add x a (Map.add y b σ)) E' ;
      if Map.find x (Map.minus y σ2)is Some a'
      then
        if eq_normal a a'
        then
          if Map.find y σ2 is Some b'
          then
            if eq_normal b b'
            then
              [Map.merge σ1 (Map.minus x (Map.minus y σ2)) |- N']
            else
              []
          else
            []
        else
          []
      else
        []
  end%list.

Lemma sound_pure {E S N}: sat E S N -> sound E ([S |- N]%list).
Proof.
  intro.
  constructor.
  1: constructor.
  auto.
Defined.

Lemma sound_mon {E p p'}:
  sound E p -> sound E p' ->
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
  forall σ E, sound E (search σ E).
Proof using.
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
    induction (IHE (Map.add X a σ)).
    1: constructor.
    cbn.
    destruct (Map.find X S) eqn:q.
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
    destruct N.
    2: constructor.
    induction (IHE2 σ).
    1: constructor.
    cbn.
    rewrite List.app_nil_r in *.
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
    induction (IHE2 (Map.add X N1 (Map.add Y N2 σ))).
    1: constructor.
    cbn.
    destruct (Map.find X (Map.minus Y S0)) eqn:q.
    2: auto.
    cbn in q.
    rewrite q.
    destruct (eq_normal N1 n).
    2: auto.
    subst.
    destruct (Map.find Y S0) eqn:q'.
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
    cbn in q.
    rewrite q.
    cbn.
    auto.
Qed.

Definition oftype Γ A := { E | Γ ⊢ E ? A }.

Definition equiv: Relation_Definitions.relation context :=
  fun E E' =>
    forall σ N,
      sat E σ N <-> sat E' σ N.

Instance equiv_Reflexive: Reflexive equiv.
Proof using.
  unfold equiv.
  unfold Reflexive.
  intros.
  reflexivity.
Qed.

Instance equiv_Symmetric: Symmetric equiv.
Proof using.
  unfold equiv.
  unfold Symmetric.
  intros.
  symmetry.
  auto.
Qed.

Instance equiv_Transitive: Transitive equiv.
Proof using.
  unfold equiv.
  unfold Transitive.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Instance equiv_Equivalence: Equivalence equiv := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid: Setoid context := {
    equiv := equiv ;
}.

Example id t :=
  let x := 0 in
  E_lam x t (E_var x).

Example conv E :=
  let x := 0 in
  let y := 1 in
  E_let x y E (E_fanout (E_var y) (E_var x)).

Theorem conv_id t: conv (id t) == id t.
Proof.
  admit.
Admitted.
