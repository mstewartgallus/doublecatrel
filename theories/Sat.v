Require Import Blech.Spec.
Require Blech.Map.
Require Import Blech.SpecNotations.

Require Blech.Context.
Require Blech.Term.

Require Import FunInd.

Import IfNotations.

Definition eq_type (x y: type): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition eq_term (x y: term): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Function typecheck (Γ: environment) (Δ: seq) (c: command): option (environment * context * term) :=
  match c with
  | c_var y =>
      if Map.Env.find y Δ is Some (E, v)
      then
        Some (Γ, E, v)
      else
        None
  | c_abs x t y v c =>
      if typecheck (Map.add x t Γ) (Map.add y (E_var x, v) Δ) c is Some (Γ', E', v')
      then
        if Term.typecheck v is Some t'
        then
          if eq_type t t'
          then
            if Term.typecheck v' is Some t1
            then
              if Context.typecheck (Map.add x t Γ) E' is Some (Γ'', t1')
              then
                if eq_type t1 t1'
                then
                  Some (Map.minus x Γ', E_all x t E', v_fanout v v')
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
  | c_app c0 c1 =>
      (* FIXME normalize ? *)
      if typecheck Γ Δ c0 is Some (Γ', E0, v_fanout v0 v1)
      then
        if typecheck Γ Δ c1 is Some (Γ'', E1, v0')
        then
          if eq_term v0 v0'
          then
            Some (Map.merge Γ' Γ'', E_app E0 E1, v1)
          else
            None
        else
          None
      else
        None
  end.

Theorem typecheck_sound:
  forall Γ Δ c Γ' E v,
    typecheck Γ Δ c = Some (Γ', E, v) -> Jsat Γ Δ c E v.
Proof.
  intros Γ Δ c.
  generalize dependent Δ.
  generalize dependent Γ.
  induction c.
  all: cbn.
  all: intros ? ? ? ? ? p.
  - destruct (Map.Env.find y Δ).
    2: discriminate.
    destruct p0.
    inversion p.
    subst.
    admit.
  - destruct (typecheck (Map.add x t Γ) (Map.add y (E_var x, v0) Δ) c) eqn:q0.
    2: discriminate.
    destruct p0.
    destruct p0.
    destruct (Term.typecheck v0) eqn:q1.
    2: discriminate.
    destruct (eq_type t t1).
    2: discriminate.
    subst.
    destruct (Term.typecheck t0) eqn:q2.
    2: discriminate.
    destruct (Context.typecheck (Map.add x t1 Γ) c0) eqn:q3.
    2: discriminate.
    destruct p0.
    destruct (eq_type t t2).
    2: discriminate.
    subst.
    inversion p.
    subst.
    econstructor.
    all: eauto.
    all: try apply Term.typecheck_sound.
    all: eauto.
    apply (Context.typecheck_sound (Map.add x t1 Γ)).
    rewrite q3.
    admit.
  - destruct (typecheck Γ Δ c1) eqn:q1.
    2: discriminate.
    destruct p0.
    destruct p0.
    destruct t.
    all: try discriminate.
    destruct (typecheck Γ Δ c2) eqn:q2.
    2: discriminate.
    destruct p0.
    destruct p0.
    destruct (eq_term t1 t).
    2: discriminate.
    subst.
    inversion p.
    subst.
    admit.
Admitted.
