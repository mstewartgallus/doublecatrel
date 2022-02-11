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

Function D x E: option (list _) :=
  match E with
  | E_var y =>
      if eq_var x y then Some [] else None
  | E_all y t E =>
      if eq_var x y
      then
        None
      else
        if D x E is Some E'
        then
          Some (e_forall y t :: E')
        else
          None
  | E_app E0 E1 =>
      if D x E0 is Some E'
      then
        Some (e_app_r E1 :: E')
      else
        if D x E1 is Some E'
        then
          Some (e_app_l E0 :: E')
        else
          None
  end%list.

Lemma I_D: forall x E e', D x E = Some e' -> I e' (E_var x) = E.
Proof using.
  intros x E.
  functional induction (D x E).
  all: intros e' p.
  all: inversion p.
  all: cbn.
  all: subst.
  - reflexivity.
  - rewrite (IHo _ e1).
    reflexivity.
  - rewrite (IHo _ e0).
    reflexivity.
  - rewrite (IHo0 _ e1).
    reflexivity.
Qed.

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
      if D x E is Some E'
      then
        if typecheck (Map.merge Γ (Map.one x t1)) E is Some (Γ', t2)
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

Theorem typecheck_sound:
  forall Γ E Δ t, typecheck Γ E = Some (Δ, t) -> Δ ⊢ E in t.
Proof.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: try eauto.
  rewrite <- (I_D _ _ _ e0).
  econstructor.
  1: eauto.
  rewrite (I_D _ _ _ e0).
  auto.
Qed.

Theorem typecheck_complete:
  forall E Γ t, Γ ⊢ E in t -> forall Δ, typecheck Δ E = Some (Γ, t).
Proof.
  intros ? ? ? p.
  induction p.
  all: cbn.
  all: intros ?.
  - admit.
  - rewrite (IHp _).
    unfold find in H.
    rewrite H.
    destruct (eq_type t1 t1).
    2: contradiction.
    destruct (D x (I e_list (E_var x))) eqn:q.
    1: reflexivity.
    admit.
  - rewrite (IHp1 _).
    rewrite (IHp2 _).
    destruct (eq_type t1 t1).
    2: contradiction.
    reflexivity.
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
  apply (typecheck_sound (Env.empty _) E).
  rewrite q1.
  reflexivity.
Defined.

Definition beta E :=
  match E with
  | E_app (E_all x _ E0) E1 =>
      if D x E0 is Some E0'
      then
        Some (I E0' E1)
      else
        None
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
  all: try (econstructor;eauto).
  - destruct E.
    all: cbn in *.
    all: inversion e.
    destruct E1.
    all: inversion e.
    destruct (D x E1) eqn:q.
    2: discriminate.
    rewrite <- (I_D _ _ _ q).
    inversion e.
    subst.
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
  induction p.
  all: intros ? ? q.
  - inversion q.
    subst.
    inversion H2.
    subst.
    auto.
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
