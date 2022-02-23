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
Implicit Type Δ: linear.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type v: term.
Implicit Type N: normal.
Implicit Types x y: vvar.
Implicit Types X Y: cvar.
Implicit Type σ: store.

Module Import Hor.
  Definition Hor t t' := Term.oftype (cons (0, t) nil) t'.

  #[program]
  Definition id t: Hor t t := v_var 0.
  Next Obligation.
    repeat constructor.
  Defined.

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
    - subst.
      constructor.
    - subst.
      constructor.
      all: auto.
      constructor.
      all: auto.
  Qed.

  #[program]
  Definition compose {A B C} (f: Hor B C) (g: Hor A B): Hor A C := subst_term g 0 f.

  Next Obligation.
  Proof.
    destruct f as [f ?], g as [g ?].
    cbn.
    eapply Term.subst_preserve.
    all: eauto.
    apply shadow.
    auto.
  Defined.
End Hor.

Module Import Vert.
  Definition Vert t t' := Context.oftype (t * t').

  #[program]
  Definition id t: Vert t t := E_lam 0 t (E_var 0).

  Next Obligation.
  Proof using.
    unfold Vert.
    constructor.
    rewrite Map.merge_empty_r.
    constructor.
  Qed.

  #[program]
  Definition compose {A B C} (f: Vert B C) (g: Vert A B): Vert A C := E_lam 0 A (E_app f (E_app g (E_var 0))).

  Next Obligation.
  Proof.
    unfold Vert in *.
    unfold compose.
    destruct f as [f ?], g as [g ?].
    constructor.
    cbn.
    rewrite <- Map.merge_empty_l.
    econstructor.
    1: eauto.
    rewrite <- Map.merge_empty_l.
    econstructor.
    1: eauto.
    rewrite Map.merge_empty_r.
    constructor.
  Qed.
End Vert.
