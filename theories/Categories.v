Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Blech.Environment.
Require Blech.Term.
Require Blech.Context.
Require Blech.Map.
Require Blech.Multiset.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Program.Tactics.

Import IfNotations.
Import Map.MapNotations.
Import Multiset.MultisetNotations.

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

  Definition Hor t t' := Term.oftype (cons (X, t) nil) t'.

  #[program]
  Definition id t: Hor t t := V_var X.

  Next Obligation.
  Proof.
    repeat constructor.
  Defined.

  #[program]
  Definition compose {A B C} (f: Hor B C) (g: Hor A B): Hor A C := subst_expr g X f.

  Next Obligation.
  Proof.
    destruct f as [f ?], g as [g ?].
    cbn.
    eapply Term.subst_preserve_elim.
    all: eauto.
    apply (Term.map_expr Environment.shadow).
    auto.
  Defined.

  Lemma compose_id_left {A B} (f: Hor A B): compose (id _) f == f.
  Proof.
    destruct f as [f ?].
    cbn.
    unfold compose, id.
    cbn.
    intros ? ?.
    cbn.
    destruct (Term.msubst_normal H j) as [N ?].
    exists N.
    split.
    all: auto.
  Qed.

  Lemma compose_id_right {A B} (f: Hor A B): compose f (id _) == f.
  Proof.
    destruct f as [f ?].
    cbn.
    intros ? H.
    cbn.
    rewrite Term.subst_var_elim.
    destruct (Term.msubst_normal H j) as [N ?].
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
    rewrite Term.subst_expr_assoc.
    eset (N := Term.msubst_normal H _).
    destruct N as [N ?].
    exists N.
    split.
    all: eauto.
    Unshelve.
    2: {
      eapply Term.subst_preserve_elim.
      2: apply (Term.map_expr Environment.shadow); eauto.
      eapply Term.subst_preserve_elim.
      2: apply (Term.map_expr Environment.shadow); eauto.
      auto.
    }
  Qed.

  #[program]
  Definition tt A: Hor A t_unit := V_cut v_tt t_unit.

  #[program]
  Definition fanout {A B C} (f: Hor C A) (g: Hor C B): Hor C (A * B) :=
    V_cut (v_fanout (v_neu f) (v_neu g)) (A * B).

  #[program]
  Definition fst {A B}: Hor (A * B) A := V_fst (V_var X).

  #[program]
  Definition snd {A B}: Hor (A * B) B := V_snd (V_var X).

  Next Obligation.
  Proof.
    destruct f as [f ?], g as [g ?].
    cbn.
    constructor.
    constructor.
    all: constructor.
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
    eset (N := Term.msubst_normal H _).
    destruct N as [N ?].
    exists N.
    split.
    all: eauto.
    Unshelve.
    2: {
      constructor.
      constructor.
    }
  Qed.

  Lemma fst_fanout {C A B} (f: Hor C A) (g: Hor C B): compose fst (fanout f g) == f.
  Proof.
    destruct f as [f ?], g as [g ?].
    intros p ?.
    cbn.
    eset (N := Term.msubst_normal H _).
    Unshelve.
    4: eapply j.
    destruct N as [N ?].
    exists N.
    split.
    2: auto.
    rewrite Term.msubst_fst.
    rewrite Term.msubst_cut.
    rewrite Term.msubst_fanout.
    repeat rewrite Term.msubst_neu.
    destruct (Term.msubst_normal H j0).
    all: repeat econstructor.
    all: eauto.
  Qed.

  Lemma snd_fanout {C A B} (f: Hor C A) (g: Hor C B): compose snd (fanout f g) == g.
  Proof.
    destruct f as [f ?], g as [g ?].
    intros p ?.
    cbn.
    eset (N := Term.msubst_normal H _).
    Unshelve.
    4: eapply j0.
    destruct N as [N ?].
    exists N.
    split.
    2: auto.
    rewrite Term.msubst_snd.
    rewrite Term.msubst_cut.
    rewrite Term.msubst_fanout.
    repeat rewrite Term.msubst_neu.
    destruct (Term.msubst_normal H j).
    all: repeat econstructor.
    all: eauto.
  Qed.
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

