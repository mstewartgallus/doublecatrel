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
  #[local]
  Definition X: var := 0.

  Definition Hor t t' := Term.oftype [(X, t)] t'.

  #[program]
  Definition id t: Hor t t := η t (V_var X).

  Next Obligation.
  Proof.
    erewrite (Term.typecheck_complete (Term.η_preserve _)).
    cbv.
    auto.
    Unshelve.
    constructor.
    apply Environment.find_sound.
    auto.
  Qed.

  #[program]
   Definition compose {A B C} (f: Hor B C) (g: Hor A B): Hor A C :=
    Term.eval_intro_dfl [(X, proj1_sig g)] (proj1_sig f).

  Next Obligation.
  Proof.
    rewrite Term.typecheck_complete.
    1: cbv.
    1: auto.
    eapply Term.eval_preserve_intro.
    - constructor.
      2:constructor.
      apply (Term.typecheck_sound (proj2_sig g)).
    - apply (Term.typecheck_sound (proj2_sig f)).
  Defined.

  Lemma compose_id_left {A B} (f: Hor A B): compose (id _) f == f.
  Proof.
    destruct f as [f ?].
    cbn.
    unfold Term.equiv.
    cbn.
    admit.
  Admitted.

  Lemma compose_id_right {A B} (f: Hor A B): compose f (id _) == f.
  Proof.
    cbn.
    unfold Term.equiv, compose, id.
    destruct f as [f ?].
    cbn.
    apply (Term.eval_intro_idsubst (Term.typecheck_sound i)).
  Qed.

  Lemma compose_assoc {A B C D} (f: Hor C D) (g: Hor B C) (h: Hor A B):
    compose f (compose g h) == compose (compose f g) h.
  Proof.
    destruct f as [f ?], g as [g ?], h as [h ?].
    cbn.
    unfold Term.equiv, compose.
    cbn.
    eapply Term.eval_intro_assoc.
    all: apply Term.typecheck_sound.
    all: eauto.
  Qed.

  #[program]
  Definition tt A: Hor A t_unit := v_tt.

  #[program]
  Definition fanout {A B C} (f: Hor C A) (g: Hor C B): Hor C (A * B) := v_fanout f g.

  Next Obligation.
  Proof.
    assert (f' := proj2_sig f).
    assert (g' := proj2_sig g).
    cbn in *.
    destruct Term.typecheck.
    2: contradiction.
    destruct Term.typecheck.
    2: contradiction.
    cbv.
    auto.
  Qed.

  #[program]
  Definition fst {A B}: Hor (A * B) A := η A (V_fst (V_var X)).

  Next Obligation.
  Proof.
    erewrite (Term.typecheck_complete (Term.η_preserve _)).
    cbv.
    auto.
    Unshelve.
    apply Term.typeinfer_sound.
    cbv.
    auto.
  Qed.

  #[program]
  Definition snd {A B}: Hor (A * B) B := η B (V_snd (V_var X)).

  Next Obligation.
  Proof.
    erewrite (Term.typecheck_complete (Term.η_preserve _)).
    cbv.
    auto.
    Unshelve.
    apply Term.typeinfer_sound.
    cbv.
    auto.
  Qed.

  (* Prove a strict terminal object *)
  Lemma compose_tt {A B} (f: Hor A B): compose (tt _) f == tt _.
  Proof.
    destruct f as [f ?].
    cbn.
    unfold compose.
    cbn.
    unfold Term.equiv.
    cbn.
    auto.
  Qed.

  Lemma fst_fanout {C A B} (f: Hor C A) (g: Hor C B): compose fst (fanout f g) == f.
  Proof.
    destruct f as [f qf], g as [g qg].
    cbn.
    unfold Term.equiv, compose, fst, fanout.
    cbn.
    assert (qf' := Term.typecheck_sound qf).
    clear qf.
    assert (qg' := Term.typecheck_sound qg).
    clear qg.
    generalize dependent f.
    generalize dependent g.
    generalize dependent B.
    generalize dependent C.
    generalize dependent A.
    intro A.
    induction A.
    all: cbn.
    all: intros ? ? g qg ? fg.
    all: inversion fg.
    all: subst.
    all: clear fg.
    all: auto.
    assert (H3' := IHA1 _ _ _ qg _ H3).
    assert (H4' := IHA2 _ _ _ qg _ H4).
    admit.
  Admitted.

  Lemma snd_fanout {C A B} (f: Hor C A) (g: Hor C B): compose snd (fanout f g) == g.
  Proof.
    destruct f as [f ?], g as [g ?].
    cbn.
    unfold Term.equiv, compose, fst, fanout.
    cbn.
    admit.
  Admitted.
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
