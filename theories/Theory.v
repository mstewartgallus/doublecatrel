Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Blech.Term.
Require Blech.Context.

Require Import Coq.Unicode.Utf8.
Require Coq.Lists.List.

Import List.ListNotations.
Import IfNotations.

Require Import FunInd.

Implicit Type Γ: environment.
Implicit Type Δ: usage.
Implicit Type E: context.
Implicit Type τ: type.
Implicit Types x y: var.
Implicit Type ρ: subst.
Implicit Type v: intro.

Definition check_sequent (S: sorts) (F: functions) (R: relations) (H: sequent): bool :=
  match H with
  | H_seq Γ c c' =>
      let all := useall Γ in
      let none := usenone Γ in
      Context.typeinfer S F R Γ c
      && (if Context.useinfer none c is Some Δ then if eq_usage Δ all then true else false else false)
      && Context.typeinfer S F R Γ c'
      && (if Context.useinfer none c' is Some Δ then if eq_usage Δ all then true else false else false)
  end %bool.

Function check_theory (S: sorts) (F: functions) (R: relations) (T: theory): bool :=
  if T is cons H T' then
    andb (check_sequent S F R H) (check_theory S F R T')
  else
    true.

Lemma check_sequent_sound {S F R H}: Bool.Is_true (check_sequent S F R H) → JH S F R H.
Proof.
  destruct H.
  cbn.
  intros p.
  destruct
    Context.typeinfer eqn:q1,
    Context.useinfer eqn:q2.
  all: try contradiction.
  destruct eq_usage in p.
  2: contradiction.
  subst.
  cbn in p.
  destruct Context.typeinfer eqn:q3 in p.
  2: contradiction.
  destruct Context.useinfer eqn:q4 in p.
  2: contradiction.
  destruct eq_usage in p.
  2: contradiction.
  subst.
  constructor.
  - apply Context.typeinfer_sound.
    rewrite q1.
    constructor.
  - apply Context.typeinfer_sound.
    rewrite q3.
    constructor.
  - apply Context.useinfer_sound.
    eauto.
  - apply Context.useinfer_sound.
    auto.
Qed.

Lemma check_theory_sound {S F R T}: Bool.Is_true (check_theory S F R T) → JT S F R T.
Proof.
  functional induction (check_theory S F R T).
  all: intros.
  - destruct check_sequent eqn:q1.
    2: contradiction.
    constructor.
    + apply check_sequent_sound.
      rewrite q1.
      constructor.
    + eauto.
  - destruct T.
    2: contradiction.
    constructor.
Qed.
