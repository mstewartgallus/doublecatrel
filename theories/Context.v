Require Import Blech.Spec.
Require Import Blech.Map.
Require Import Blech.SpecNotations.

Require Import Coq.Classes.SetoidClass.
Require Coq.Lists.List.

Require Import FunInd.

Import List.ListNotations.
Import IfNotations.

Definition eq_type (x y: type): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Function typecheck (Γ: environment) (E: context): option (environment * type) :=
  match E with
  | E_var x =>
      if Env.find x Γ is Some t
      then
        if Env.is_empty (Env.remove x Γ)
        then
          Some (Map.one x t, t)
        else
          None
      else
        None
  | E_all x t1 E =>
      if typecheck (Map.add x t1 Γ) E is Some (Γ', t2)
      then
        if Env.find x Γ' is Some t1'
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
  end
    %list.

Lemma env_add_minus:
  forall x (t: type) Γ,
    Env.find x Γ = Some t ->
    Map.add x t (Map.minus x Γ) = Γ.
Proof.
  intros x t Γ p.
  unfold add, minus.
  admit.
Admitted.

Lemma find_add:
  forall x (t: type) Γ,
    Env.find x (Env.add x t Γ) = Some t.
Proof.
  intros x t.
  admit.
Admitted.

Lemma always_empty:
  forall x (t: type), Env.is_empty (Env.remove x (Env.add x t (Env.empty _))) = true.
Proof.
  intros ? ?.
  unfold one.
  admit.
Admitted.

Lemma remove_add:
  forall x (t: type) Γ,
    Env.remove x (Env.add x t Γ) = Γ.
Proof.
  intros x t.
  admit.
Admitted.

Theorem typecheck_sound:
  forall Γ E Δ t, typecheck Γ E = Some (Δ, t) -> Δ ⊢ E in t.
Proof using.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
  apply IHo.
  rewrite (env_add_minus x t1 Γ').
  2: auto.
  auto.
Qed.

Theorem typecheck_complete:
  forall E Γ t, Γ ⊢ E in t -> typecheck Γ E = Some (Γ, t).
Proof using.
  intros ? ? ? p.
  induction p.
  - unfold typecheck.
    unfold one.
    unfold empty.
    unfold add.
    rewrite (find_add x t (Env.empty _)).
    rewrite always_empty.
    reflexivity.
  - cbn.
    destruct (typecheck (add x t1 G) E) as [[]|] eqn:q1.
    2: discriminate.
    inversion IHp.
    subst.
    unfold add.
    rewrite (find_add x t1 G).
    destruct (eq_type t1 t1).
    2: contradiction.
    unfold minus.
    rewrite remove_add.
    reflexivity.
  - admit.
Admitted.

Definition of_t t := { E | exists Γ, Env.is_empty Γ = true /\ (Γ ⊢ E in t) }.

Definition tc E: if typecheck (Env.empty _) E is Some (Γ, t)
                   then
                     if Env.is_empty Γ
                     then
                       of_t t
                     else
                       unit
                   else
                     unit.
Proof.
  destruct (typecheck (Env.empty _) E) as [[Γ t]|] eqn:q1.
  2: apply tt.
  destruct (Env.is_empty Γ) eqn:q2.
  2: apply tt.
  exists E.
  exists Γ.
  split.
  1:  auto.
  apply (typecheck_sound (Env.empty _)).
  rewrite q1.
  reflexivity.
Defined.

Definition beta E :=
  match E with
  | E_app (E_all x _ E0) E1 => Some (subst_context E1 x E0)
  | _ => None
  end.

Function eval E :=
  if beta E is Some E'
  then
    Some E'
  else
    match E with
    | E_all x t E =>
        if eval E is Some E'
        then
          Some (E_all x t E')
        else
          None
    | E_app E0 E1 =>
        if eval E0 is Some E0'
        then
          Some (E_app E0' E1)
        else
          if eval E1 is Some E1'
          then
            Some (E_app E0 E1')
          else
            None
    | _ => None
    end.

Theorem eval_sound:
  forall E E', eval E = Some E' -> step_E E E'.
Proof using.
  intros E.
  functional induction (eval E).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  - destruct E.
    all: cbn in *.
    all: inversion e.
    destruct E1.
    all: inversion e.
    econstructor.
  - apply (stepE_ctx (e_forall _ _)).
    auto.
  - apply (stepE_ctx (e_app_r _)).
    auto.
  - apply (stepE_ctx (e_app_l _)).
    auto.
Qed.

Theorem stepE_preserve:
  forall E E',
    step_E E E' ->
    forall Γ t, Γ ⊢ E in t -> Γ ⊢ E' in t.
Proof.
  intros E E' p.
  intros Γ ? q.
  generalize dependent Γ.
  generalize dependent t.
  induction p.
  all: intros ? Γ q.
  - inversion q.
    subst.
    admit.
  - induction e.
    all: cbn in *.
    + inversion q.
      subst.
      admit.
    + inversion q.
      subst.
      econstructor.
      all: eauto.
    + inversion q.
      subst.
      econstructor.
      all: eauto.
Admitted.

Instance multiE_Reflexive: Reflexive multi_E.
Proof.
  econstructor.
Qed.

Instance multiE_trans: Transitive multi_E.
Proof.
  intros v1 v2 v3 p.
  generalize v3.
  induction p.
  1: auto.
  intros.
  econstructor.
  1: apply H.
  apply IHp.
  auto.
Qed.

Lemma multiE_ctx:
  forall E E', multi_E E E' -> forall e, multi_E (appctx_context_ctx_context e E) (appctx_context_ctx_context e E').
Proof.
  intros ? ? p.
  induction p.
  all: intros.
  1: constructor.
  econstructor.
  - econstructor.
    eauto.
  - apply IHp.
Qed.

Lemma multiE_preserve:
  forall E E',
    multi_E E E' ->
    forall Γ t, Γ ⊢ E in t -> Γ ⊢ E' in t.
Proof.
  intros E E' p.
  induction p.
  1: auto.
  intros Γ t q.
  apply IHp.
  refine (stepE_preserve _ _ _ _ _ q).
  auto.
Qed.

Theorem stepE_progress:
  forall E t,
    Env.empty _ ⊢ E in t ->
    is_context_whnf_of_context E = false -> exists E', step_E E E'.
Proof using.
  remember (Env.empty _) as Γ.
  intros E t p.
  induction p.
  all: cbn.
  all: subst.
  all: intros q.
  all: try discriminate.
  destruct (is_context_whnf_of_context E1) eqn:q1.
  - destruct E1.
    all: try discriminate.
    exists (subst_context E2 x E1).
    econstructor.
  - destruct IHp1.
    all: auto.
    all: admit.
Admitted.
