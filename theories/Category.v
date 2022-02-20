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
    constructor.
    cbn.
    reflexivity.
  Defined.

  #[program]
  Definition compose {A B C} (f: Hor B C) (g: Hor A B): Hor A C := subst_term g 0 f.

  Next Obligation.
  Proof.
    destruct f as [f ?], g as [g ?].
    cbn in *.
    generalize dependent C.
    generalize dependent B.
    generalize dependent A.
    generalize dependent g.
    induction f.
    all: cbn.
    all: intros g A B p C q.
    - destruct (eq_vvar x 0).
      + subst.
        inversion q.
        subst.
        cbn in H1.
        inversion H1.
        subst.
        auto.
      + inversion q.
        subst.
        unfold find in H1.
        cbn in H1.
        destruct (eq_vvar x 0).
        1: contradiction.
        discriminate.
    - inversion q.
      subst.
      constructor.
    - inversion q.
      subst.
      econstructor.
      eapply IHf.
      all: eauto.
    - inversion q.
      subst.
      econstructor.
      eapply IHf.
      all: eauto.
    - inversion q.
      subst.
      econstructor.
      all: try eapply IHf1 ; try eapply IHf2.
      all: eauto.
  Defined.
End Hor.

Module Import Vert.
  Definition Vert t t' := Context.oftype (t * t').

  #[program]
  Definition id t: Vert t t := E_lam 0 t (E_var 0).

  Next Obligation.
  Proof using.
    unfold Vert.
    apply (Context.typecheck_sound Map.empty).
    cbn.
    destruct (eq_type t t).
    2: contradiction.
    cbn.
    unfold Map.one.
    replace (Map.minus 0 _) with (@Map.empty type).
    1: reflexivity.
    admit.
  Admitted.

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
