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
    apply Environment.shadow.
    auto.
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
  Definition x: var := 0.

  Definition Vert t t' := Context.oftype (cons (x, t) nil) t'.

  #[program]
  Definition id t: Vert t t := E_var x.

  Next Obligation.
  Proof using.
    constructor.
    all: constructor.
    constructor.
  Qed.

  #[program]
  Definition compose {A B C} (f: Vert B C) (g: Vert A B): Vert A C := subst_context g x f.

  (* FIXME figure out how to generalize this *)
  #[local]
  Lemma preserve {f}:
    ∀ g {A B},
    ((x, A) :: nil)%list ⊢ g ? B
    → ∀ {C Γ}, ((x, B) :: Γ)%list ⊢ f ? C
             → ((x, A) :: Γ)%list ⊢ subst_context g x f ? C.
  Proof.
    induction f.
    all: cbn.
    all: try destruct eq_var.
    all: subst.
    all: cbn.
    all: try destruct eq_var.
    all: subst.
    all: cbn.
    all: intros g A B p C Γ q.
    all: inversion q.
    all: subst.
    + inversion H1.
      2: contradiction.
      subst.
      replace ((x, A) :: Γ)%list with (cons (x, A) nil ++ Γ)%list.
      2: auto.
      apply (Context.map Environment.weaken).
      auto.
    + inversion H1.
      all: subst.
      1: contradiction.
      constructor.
      constructor.
      all: auto.
    + constructor.
      apply Context.shadow.
      eapply Context.unshadow.
      eauto.
    + constructor.
      refine (Context.map _ (IHf g _ _ p _ _ _)).
      2: {
        eapply Context.swap.
        2: apply H4.
        auto.
      }
      intros.
      apply Environment.swap.
      all: auto.
    + econstructor.
      all: eauto.
    + constructor.
    + econstructor.
      all: eauto.
    + econstructor.
      all: eauto.
    + econstructor.
      all: eauto.
      refine (Context.map _ H6).
      intros.
      inversion H.
      all: subst.
      1: constructor.
      constructor.
      1: auto.
      apply Environment.shadow.
      eapply Environment.unshadow.
      eauto.
    + econstructor.
      all: eauto.
      refine (Context.map _ H6).
      intros.
      inversion H.
      all: subst.
      1: constructor.
      constructor.
      1: auto.
      inversion H8.
      all: subst.
      1: constructor.
      constructor.
      all: auto.
      constructor.
      all: auto.
      inversion H10.
      all: subst.
      all: auto.
      contradiction.
    + econstructor.
      all: eauto.
      refine (Context.map _ (IHf2 g _ _ p _ _ _)).
      2: {
        refine (Context.map _ H6).
        intros.
        inversion H.
        all: subst.
        -- constructor.
           all: auto.
           apply H.
        -- inversion H8.
           all: subst.
           ++ constructor.
              all: auto.
           ++ inversion H10.
              all: subst.
              1: constructor.
              constructor.
              all: auto.
      }
      intros.
      inversion H.
      all: subst.
      -- constructor.
         all: auto.
         constructor.
         all: auto.
         constructor.
      -- inversion H8.
         all: subst.
         1: constructor.
         constructor.
         all: auto.
         inversion H10.
         all: subst.
         1: constructor.
         constructor.
         all: auto.
         constructor.
         all: auto.
         inversion H12.
         all: subst.
         all: auto.
         contradiction.
  Qed.

  (* FIXME figure out how to generalize this *)
  #[local]
  Lemma linpreserve {f}:
    ∀ g {A B},
    ((x, A) :: nil)%list ⊢ g ? B
    → ∀ {C Γ}, ((x, B) :: Γ)%list ⊢ f ? C
               → lin f
               → lin g
               → lin (subst_context g x f).
  Proof.
    induction f.
    all: cbn.
    all: intros g ? ? ? ? ? p q ?.
    all: try destruct eq_var.
    all: subst.
    all: try destruct eq_var.
    all: subst.
    all: auto.
    all: inversion p.
    all: subst.
    all: inversion q.
    all: subst.
    + constructor.
      2: eapply IHf.
      all: eauto.
      2: {
        eapply Context.swap.
        2: apply H6.
        auto.
      }
      admit.
    + constructor.
      all: eauto.
    + constructor.
      all: eauto.
    + constructor.
      all: eauto.
    + constructor.
      all: auto.
      eapply IHf1.
      all: auto.
      2: apply H7.
      eauto.
    + constructor.
      all: auto.
      eapply IHf1.
      all: auto.
      2: apply H7.
      eauto.
    + constructor.
      all: eauto.
      3: eapply IHf2.
      all: eauto.
      3: refine (Context.map _ H8).
      3: {
        intros.
        inversion H1.
        all: subst.
        1: constructor.
        all: eauto.
        inversion H14.
        all: subst.
        1: constructor.
        all:auto.
        inversion H16.
        all: subst.
        1: constructor.
        constructor.
        all: auto.
      }
      all: admit.
  Admitted.

  Next Obligation.
  Proof.
    unfold Vert in *.
    unfold compose.
    destruct f as [f [? ?]], g as [g [? ?]].
    cbn.
    split.
    - eapply preserve.
      all: eauto.
    - eapply linpreserve.
      all: eauto.
  Qed.

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
