Require Import Blech.Spec.
Require Import Blech.SpecNotations.

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
Implicit Type E: context.
Implicit Type t: type.
Implicit Type v: term.
Implicit Type N: normal.
Implicit Types x y X Y: var.
Implicit Type σ: store.

Module Import Hor.
  #[local]
  Definition X: var := 0.

  Definition Hor t t' := Term.oftype (cons (X, t) nil) t'.

  #[program]
  Definition id t: Hor t t := v_var X.

  #[program]
  Definition compose {A B C} (f: Hor B C) (g: Hor A B): Hor A C := subst_term g X f.

  #[local]
   Lemma shadow:
    ∀ {v Γ x t0 t1 t2},
      ((x, t0) :: Γ)%list ⊢ v in t2 →
      ((x, t0) :: (x, t1) :: Γ)%list ⊢ v in t2.
  Proof.
    intro v.
    induction v.
    all: intros ? ? ? ? ? p.
    all: inversion p.
    all: subst.
    all: try econstructor.
    all: try eauto.
    inversion H1.
    all: repeat constructor.
    all: auto.
  Qed.

  Next Obligation.
  Proof.
    destruct f as [f ?], g as [g ?].
    cbn.
    eapply Term.subst_preserve.
    all: eauto.
    apply shadow.
    auto.
  Defined.

  Next Obligation.
    repeat constructor.
  Defined.

  Lemma compose_id_left {A B} (f: Hor A B): compose (id _) f == f.
  Proof.
    destruct f as [f ?].
    cbn.
    unfold compose, id.
    cbn.
    intros ? H.
    cbn.
    destruct (Term.normalize (Term.msubst_preserve H j)) as [N ?].
    exists N.
    cbn.
    split.
    all: auto.
  Qed.

  Lemma compose_id_right {A B} (f: Hor A B): compose f (id _) == f.
  Proof.
    destruct f as [f ?].
    cbn.
    intros ? H.
    cbn.
    rewrite Term.subst_var.
    destruct (Term.normalize (Term.msubst_preserve H j)) as [N ?].
    exists N.
    split.
    all: auto.
  Qed.

  Lemma compose_assoc {A B C D} (f: Hor C D) (g: Hor B C) (h: Hor A B):
    compose f (compose g h) == compose (compose f g) h.
  Proof.
    destruct f as [f ?], g as [g ?], h as [h ?].
    cbn.
    intros ? H.
    cbn.
    eset (N := @Term.normalize (msubst p (subst_term (subst_term h X g) X f)) D _).
    destruct N as [N ?].
    Unshelve.
    2: {
      eapply Term.msubst_preserve.
      1: eauto.
      eapply Term.subst_preserve.
      2: apply shadow; eauto.
      eapply Term.subst_preserve.
      2: apply shadow; eauto.
      auto.
    }
    exists N.
    split.
    1: auto.
    rewrite <- Term.subst_assoc.
    auto.
  Qed.

  #[program]
  Definition tt A: Hor A t_unit := v_tt.

  #[program]
   Definition fanout {A B C} (f: Hor C A) (g: Hor C B): Hor C (A * B) := v_fanout f g.

  #[program]
  Definition fst {A B}: Hor (A * B) A := v_fst (v_var X).

  #[program]
  Definition snd {A B}: Hor (A * B) B := v_snd (v_var X).

  Next Obligation.
  Proof.
    destruct f as [f ?], g as [g ?].
    cbn.
    constructor.
    all: auto.
  Defined.

  Next Obligation.
  Proof.
    repeat econstructor.
  Defined.

  Next Obligation.
  Proof.
    repeat econstructor.
  Defined.

  Next Obligation.
  Proof.
    repeat econstructor.
  Defined.

  (* Prove a strict terminal object *)
  Lemma compose_tt {A B} (f: Hor A B): compose (tt _) f == tt _.
  Proof.
    cbn.
    destruct f as [f ?].
    intros p ?.
    cbn.
    eset (N := @Term.normalize (msubst p v_tt) t_unit _).
    destruct N as [N ?].
    Unshelve.
    2: {
      eapply Term.msubst_preserve.
      all: eauto.
      constructor.
    }
    exists N.
    split.
    all: auto.
  Qed.

  Lemma fst_fanout {C A B} (f: Hor C A) (g: Hor C B): compose fst (fanout f g) == f.
  Proof.
    destruct f as [f ?], g as [g ?].
    intros p ?.
    cbn.
    eset (N := @Term.normalize (msubst p f) A _).
    destruct N as [N ?].
    Unshelve.
    2: {
      eapply Term.msubst_preserve.
      all: eauto.
    }
    destruct (Term.normalize (Term.msubst_preserve H j0)).
    exists N.
    split.
    all: auto.
    rewrite Term.msubst_fst.
    rewrite Term.msubst_fanout.
    econstructor.
    econstructor.
    1: auto.
    apply H1.
  Qed.

  Lemma snd_fanout {C A B} (f: Hor C A) (g: Hor C B): compose snd (fanout f g) == g.
  Proof.
    destruct f as [f ?], g as [g ?].
    intros p ?.
    cbn.
    eset (N := @Term.normalize (msubst p g) B _).
    destruct N as [N ?].
    Unshelve.
    2: {
      eapply Term.msubst_preserve.
      all: eauto.
    }
    destruct (Term.normalize (Term.msubst_preserve H j)).
    exists N.
    split.
    all: auto.
    rewrite Term.msubst_snd.
    rewrite Term.msubst_fanout.
    econstructor.
    econstructor.
    1: auto.
    apply H1.
    auto.
  Qed.
End Hor.

Module Import Vert.
  #[local]
  Definition X: var := 0.

  Definition Vert t t' := Context.oftype (cons (X, t) nil) t'.

  #[program]
  Definition id t: Vert t t := E_var X.

  Next Obligation.
  Proof using.
    constructor.
    constructor.
  Qed.

  #[program]
  Definition compose {A B C} (f: Vert B C) (g: Vert A B): Vert A C := subst_context g X f.

  Next Obligation.
  Proof.
    unfold Vert in *.
    unfold compose.
    destruct f as [f ?], g as [g ?].
    cbn.
    admit.
  Admitted.

  Lemma compose_id_right {A B} (f: Vert A B): compose f (id _) == f.
  Proof.
    destruct f as [f ?].
    unfold compose, id.
    cbn.
    intros ?.
    cbn.
    admit.
  Admitted.


  Lemma compose_assoc {A B C D} (f: Vert C D) (g: Vert B C) (h: Vert A B):
    compose f (compose g h) == compose (compose f g) h.
  Proof.
    destruct f as [f ?], g as [g ?], h as [h ?].
    cbn.
    intros ?.
    cbn.
    rewrite Context.subst_assoc.
    reflexivity.
  Qed.
End Vert.
