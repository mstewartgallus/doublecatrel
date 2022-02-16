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
      if Map.find x Γ is Some t
      then
        if Env.is_empty (Map.minus x Γ)
        then
          Some (Map.one x t, t)
        else
          None
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
  - apply IHo.
    rewrite (Map.add_minus x t1 Γ').
    2: auto.
    auto.
  - rewrite Map.add_minus.
    all: auto.
    1: rewrite Map.add_minus.
    all: auto.
Qed.

Theorem typecheck_complete:
  forall E Γ t, Γ ⊢ E in t -> typecheck Γ E = Some (Γ, t).
Proof using.
  intros ? ? ? p.
  induction p.
  - unfold typecheck.
    unfold one.
    rewrite (Map.find_add x t Map.empty).
    rewrite always_empty.
    reflexivity.
  - cbn.
    destruct (typecheck (add x t1 G) E) as [[]|] eqn:q1.
    2: discriminate.
    inversion IHp.
    subst.
    rewrite (find_add x t1 G).
    destruct (eq_type t1 t1).
    2: contradiction.
    unfold minus.
    rewrite remove_add.
    reflexivity.
  - admit.
  - reflexivity.
  - admit.
  - admit.
  - admit.
Admitted.
