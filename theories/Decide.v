Require Import Blech.Spec.
Require Import Blech.Map.

Require Import FunInd.


Import IfNotations.

Module Import SpecNotations.
  Infix "*" := t_prod.

  Notation "Γ ⊢ E 'in' t" := (judge_E Γ E t) (at level 90).
End SpecNotations.

Definition eq_type (x y: type): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Function typecheck (Γ: environment) (e: context): option (environment * type) :=
  match e with
  | E_var x =>
      if Env.find x Γ is Some t
      then
        Some (Map.one x t, t)
      else
        None
  | E_all x t1 E =>
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
  forall Γ e Δ t, typecheck Γ e = Some (Δ, t) -> Δ ⊢ e in t.
Proof.
  intros Γ e.
  functional induction (typecheck Γ e).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
Qed.
