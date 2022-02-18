Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Import Coq.Classes.SetoidClass.

Import IfNotations.

Require Import FunInd.

Fixpoint toterm (v: normal): term :=
  match v with
  | N_tt => v_tt
  | N_fanout v0 v1 => v_fanout (toterm v0) (toterm v1)
  end.

Coercion toterm: normal >-> term.

Function typecheck Γ (v: term): option type :=
  match v with
  | v_var x => Map.find x Γ
  | v_tt => Some t_unit
  | v_fst v =>
      if typecheck Γ v is Some (t0 * _)
      then
        Some t0
      else
        None
  | v_snd v =>
      if typecheck Γ v is Some (_ * t1)
      then
        Some t1
      else
        None
  | v_fanout v0 v1 =>
      if typecheck Γ v0 is Some t0
      then
        if typecheck Γ v1 is Some t1
        then
          Some (t0 * t1)
        else
          None
      else
        None
  end.

Theorem typecheck_sound:
  forall {Γ v t}, typecheck Γ v = Some t -> Γ ⊢ v in t.
Proof using .
  intros Γ v.
  functional induction (typecheck Γ v).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
Qed.

Theorem typecheck_complete:
  forall {Γ v t}, Γ ⊢ v in t -> typecheck Γ v = Some t.
Proof using .
  intros Γ ? ? p.
  induction p.
  all: cbn.
  all: try (destruct (typecheck G v) as [[]|]).
  all: try (destruct (typecheck G v1)).
  all: try (destruct (typecheck G v2)).
  all: try inversion IHp.
  all: subst.
  all: try inversion IHp1.
  all: subst.
  all: try inversion IHp2.
  all: subst.
  all: auto.
Qed.

Function eval v :=
  match v with
  | v_var _ => None
  | v_tt => Some N_tt
  | v_fst v => if eval v is Some (N_fanout a _) then Some a else None
  | v_snd v => if eval v is Some (N_fanout _ a) then Some a else None
  | v_fanout v0 v1 =>
      if eval v0 is Some v0'
      then
        if eval v1 is Some v1'
        then
          Some (N_fanout v0' v1')
        else
          None
      else
        None
  end.

Theorem eval_sound:
  forall {v N}, eval v = Some N -> v ⇓ N.
Proof using.
  intros v.
  functional induction (eval v).
  all: intros ? p.
  all: inversion p.
  all: subst.
  - constructor.
  - econstructor.
    apply IHo.
    eauto.
  - econstructor.
    apply IHo.
    eauto.
  - econstructor.
    1: apply IHo.
    2: apply IHo0.
    all:  eauto.
Qed.

Theorem eval_complete:
  forall {v v'}, v ⇓ v' -> eval v = Some v'.
Proof using.
  intros ? ? p.
  induction p.
  all: cbn.
  all: try rewrite IHp.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: reflexivity.
Qed.

Theorem eval_preserve:
  forall {v v'},
    v ⇓ v' ->
    forall Γ t, Γ ⊢ v in t -> Γ ⊢ v' in t.
Proof using.
  intros v v' p.
  induction p.
  all: intros ? ? q.
  all: inversion q.
  all: subst.
  all: auto.
  - econstructor.
    all: eauto.
  - set (p' := IHp _ _ H1).
    inversion p'.
    subst.
    auto.
  - set (p' := IHp _ _ H1).
    inversion p'.
    subst.
    auto.
Qed.

Theorem normalize:
  forall {v t},
   Map.empty ⊢ v in t ->
   exists N, v ⇓ N.
Proof using.
  remember Map.empty as G.
  intros ? ? p.
  induction p.
  all: subst.
  - discriminate.
  - exists N_tt.
    constructor.
  - destruct (IHp1 (eq_refl _)) as [v1' s1].
    destruct (IHp2 (eq_refl _)) as [v2' s2].
    exists (N_fanout v1' v2').
    constructor.
    all: auto.
  - destruct (IHp (eq_refl _)) as [v' s].
    set (vwf := eval_preserve s _ _ p).
    destruct v'.
    all: cbn in *.
    all: try discriminate.
    all: inversion vwf.
    all: subst.
    all: cbn in *.
    exists v'1.
    econstructor.
    all: eauto.
  - destruct (IHp (eq_refl _)) as [v' s].
    set (vwf := eval_preserve s _ _ p).
    destruct v'.
    all: cbn in *.
    all: try discriminate.
    all: inversion vwf.
    all: subst.
    all: cbn in *.
    exists v'2.
    econstructor.
    all: eauto.
Qed.

Definition oftype Γ A := { v | Γ ⊢ v in A }.

Inductive compat: Map.map type -> list (var * normal) -> Prop :=
| compat_nil: compat Map.empty nil
| compat_cons x t N Γ σ: compat Γ σ -> compat (Map.add x t Γ) (cons (x, N) σ)
.

Definition msubst (Γ: list (var * normal)): term -> term.
Proof.
  refine (List.fold_left _ Γ).
  intros v xN.
  apply (subst_term (snd xN) (fst xN) v).
Defined.

Definition equiv {Γ A} (v v': oftype Γ A) :=
  forall σ,
    compat Γ σ ->
    exists N, (msubst σ (proj1_sig v) ⇓ N) /\ (msubst σ (proj1_sig v') ⇓ N).
