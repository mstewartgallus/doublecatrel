Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Blech.Environment.
Require Blech.Term.
Require Blech.Context.
Require Blech.Map.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Program.Tactics.

Import IfNotations.
Import Map.MapNotations.

Require Import FunInd.

Implicit Type Γ: environment.
Implicit Type Δ: usage.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type v: term.
Implicit Type N: normal.
Implicit Types x y: var.
Implicit Type σ: store.

Module Import Hor.
  #[local]
  Definition X: var := 0.

  Definition Hor t t' := Term.oftype ((X, t) :: nil) t'.

  #[program]
  Definition id t: Hor t t := Term.η t (V_var X).

  Next Obligation.
  Proof.
    erewrite (Term.typecheck_complete (Term.η_preserve _)).
    cbv.
    auto.
    Unshelve.
    constructor.
    apply Environment.find_sound.
    auto.
  Defined.

  Definition compose {A B C} (f: Hor B C) (g: Hor A B): Hor A C.
  Proof.
    exists (if Term.hsubst_term (proj1_sig g) X (proj1_sig f) is Some v
            then v
            else v_tt).
    destruct (Term.hsubst_term_total (Term.typecheck_sound (proj2_sig f)) (Term.typecheck_sound (proj2_sig g))).
    rewrite H.
    erewrite (Term.typecheck_complete (Term.hsubst_preserve_term _ _ H)).
    cbv.
    auto.
    Unshelve.
    2: eapply (Term.typecheck_sound (proj2_sig g)).
    apply (Term.map_term Environment.shadow).
    apply (Term.typecheck_sound (proj2_sig f)).
  Defined.

  Lemma compose_id_left {A B} (f: Hor A B): compose (id _) f == f.
  Proof.
    destruct f as [f ?].
    cbn.
    unfold Term.equiv.
    cbn.
    unfold compose, id.
    cbn.
    assert (i' := Term.typecheck_sound i).
    assert (j' := Term.typecheck_sound (proj2_sig (id B))).
    cbn in j'.
    destruct (Term.hsubst_term_total j' i').
    rewrite H.
    admit.
  Admitted.

  Lemma compose_id_right {A B} (f: Hor A B): compose f (id _) == f.
  Proof.
    cbn.
    unfold Term.equiv, compose, id.
    destruct f as [f ?].
    cbn.
    admit.
  Admitted.

  Lemma compose_assoc {A B C D} (f: Hor C D) (g: Hor B C) (h: Hor A B):
    compose f (compose g h) == compose (compose f g) h.
  Proof.
    destruct f as [f ?], g as [g ?], h as [h ?].
    cbn.
    unfold Term.equiv, compose.
    cbn.
    admit.
  Admitted.

  #[program]
  Definition tt A: Hor A t_unit := v_tt.

  #[program]
  Definition fanout {A B C} (f: Hor C A) (g: Hor C B): Hor C (A * B) :=
    v_fanout f g.

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
  Definition fst {A B}: Hor (A * B) A := Term.η A (V_fst (V_var X)).

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
  Definition snd {A B}: Hor (A * B) B := Term.η B (V_snd (V_var X)).

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
    cbn.
    destruct f as [f ?].
    unfold Term.equiv.
    cbn.
    auto.
  Qed.

  Lemma fst_fanout {C A B} (f: Hor C A) (g: Hor C B): compose fst (fanout f g) == f.
  Proof.
    destruct f as [f ?], g as [g ?].
    cbn.
    unfold Term.equiv, compose, fst, fanout.
    cbn.
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

  Definition Vert t t' := Context.oftype (cons (x, t) nil) t'.

  Instance Vert_Equivalence t t': Equivalence (λ (x y: Vert t t'), proj1_sig x == proj1_sig y).
  Proof.
    exists.
    - intro.
      reflexivity.
    - intro.
      symmetry.
      auto.
    - intros ? ? ? p.
      rewrite p.
      auto.
  Qed.

  Instance Vert_Setoid t t': Setoid (Vert t t') := {
      equiv a b := proj1_sig a == proj1_sig b ;
    }.

  #[program]
  Definition id t: Vert t t := E_var x.

  Next Obligation.
  Proof using.
    constructor.
    1:constructor.
    cbn.
    constructor.
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

