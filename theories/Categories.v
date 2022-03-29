Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Blech.Environment.
Require Blech.Term.
Require Blech.Context.
Require Blech.Assoc.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Program.Tactics.
Require Import Coq.Lists.List.

Import IfNotations.
Import List.ListNotations.

Require Import FunInd.

Implicit Type Γ: environment.
Implicit Type Δ: usage.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type v: intro.
Implicit Type V: elim.
Implicit Types x y: var.
Implicit Type ρ: subst.

Module Import Hor.
  Definition Hor Γ Γ' := { ρ | Jp ρ Γ Γ' }.

  #[program]
  Definition id A: Hor A A := [].

  Next Obligation.
  Proof.
    constructor.
  Qed.

  #[program]
  Definition compose {A B C} (f: Hor B C) (g: Hor A B): Hor A C := g ++ f.

  Next Obligation.
  Proof.
    destruct g as [g gp].
    destruct f as [f fp].
    cbn.
    generalize dependent C.
    generalize dependent B.
    generalize dependent A.
    generalize dependent f.
    generalize dependent g.
    intro g.
    induction g.
    all: cbn.
    all: intros.
    - inversion gp.
      auto.
    - inversion gp.
      subst.
      econstructor.
      1: apply H1.
      eauto.
  Qed.

  Infix "∘" := compose (at level 30).

  #[program]
  Definition pure {x Γ t} (p: { v | Γ ⊢ v ⇐ t}): Hor Γ [(x, t)] := [(x, proj1_sig p)].

  Next Obligation.
  Proof.
    apply (Jp_cut _ _ _ _ _ _ _ H (Jp_id [_])).
  Qed.

  #[program]
  Definition fanout {Γ} {x y z A B}: x ≠ y → Hor ((x, A) :: (y, B) :: Γ) [(z, A * B)] := λ _,
    pure (v_fanout (η A (V_var x)) (η B (V_var y))).

  Next Obligation.
  Proof.
    econstructor.
    all: apply Term.η_preserve.
    all: constructor.
    all: repeat constructor.
    auto.
  Qed.
End Hor.

Module Import Vert.
  #[local]
  Definition x: var := 0.

  Definition Vert t t' := Context.oftype [(x, t)] t'.

  #[program]
  Definition id t: Vert t t := E_neu (e_var x).

  Next Obligation.
  Proof using.
    destruct eq_type.
    2: contradiction.
    cbv.
    auto.
  Qed.

  #[program]
  Definition compose {A B C} (f: Vert B C) (g: Vert A B): Vert A C := subst_context g x f.

  Next Obligation.
  Proof.
    admit.
  Admitted.

  Lemma compose_id_left {A B} (f: Vert A B): compose (id _) f == f.
  Proof.
    destruct f as [f ?].
    cbn.
    reflexivity.
  Qed.

  Lemma compose_id_right {A B} (f: Vert A B): compose f (id _) == f.
  Proof.
    destruct f as [f ?].
    cbn.
    rewrite Context.subst_var.
    reflexivity.
  Qed.

  Lemma compose_assoc {A B C D} (f: Vert C D) (g: Vert B C) (h: Vert A B):
    compose f (compose g h) == compose (compose f g) h.
  Proof.
    destruct f as [f ?], g as [g ?], h as [h ?].
    cbn.
    rewrite Context.subst_assoc.
    reflexivity.
  Qed.
End Vert.
