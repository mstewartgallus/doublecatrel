Require Import Blech.Spec.
Require Import Blech.Map.

Require Import FunInd.


Import IfNotations.

Module Import SpecNotations.
  Infix "*" := t_prod.

  Notation "Γ ⊢ E 'in' t" := (judge_E Γ E t) (at level 90).
  Notation "⊢ v 'in' t" := (judge_v v t) (at level 90).
End SpecNotations.

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
  forall Γ E Δ t, typecheck Γ E = Some (Δ, t) -> Δ ⊢ E in t.
Proof.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
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
    reflexivity.
  - rewrite (IHp1 _).
    rewrite (IHp2 _).
    destruct (eq_type t1 t1).
    2: contradiction.
    reflexivity.
Admitted.


Function typeof (v: term): option type :=
  match v with
  | v_tt => Some t_unit
  | v_fst v =>
      if typeof v is Some (t0 * _)
      then
        Some t0
      else
        None
  | v_snd v =>
      if typeof v is Some (_ * t1)
      then
        Some t1
      else
        None
  | v_fanout v0 v1 =>
      if typeof v0 is Some t0
      then
        if typeof v1 is Some t1
        then
          Some (t0 * t1)
        else
          None
      else
        None
  end.

Theorem typeof_sound:
  forall v t, typeof v = Some t -> ⊢ v in t.
Proof.
  intros v.
  functional induction (typeof v).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
Qed.

Theorem typeof_complete:
  forall v t, ⊢ v in t -> typeof v = Some t.
Proof.
  intros ? ? p.
  induction p.
  all: cbn.
  all: try (destruct (typeof v) as [[]|]).
  all: try (destruct (typeof v1)).
  all: try (destruct (typeof v2)).
  all: try inversion IHp.
  all: subst.
  all: try inversion IHp1.
  all: subst.
  all: try inversion IHp2.
  all: subst.
  all: reflexivity.
Qed.

Definition E_of_t t := { E | exists Γ, Env.is_empty Γ = true /\ (Γ ⊢ E in t) }.
Definition v_of_t t := { v | ⊢ v in t }.

Definition v_tc v: if typeof v is Some t
                   then
                     v_of_t t
                   else
                     unit.
Proof.
  destruct (typeof v) eqn:q.
  2: apply tt.
  exists v.
  apply typeof_sound.
  auto.
Defined.

Definition E_tc E: if typecheck (Env.empty _) E is Some (Γ, t)
                   then
                     if Env.is_empty Γ
                     then
                       E_of_t t
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
