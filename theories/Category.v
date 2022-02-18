Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Blech.Term.
Require Blech.Context.
Require Blech.Map.

Require Import Coq.Classes.SetoidClass.
Require Import Coq.Program.Tactics.

Import IfNotations.

Module Import Hor.
  Definition Hor (A B: type) := Term.oftype (cons (0, A) nil) B.

  #[program]
  Definition id A: Hor A A := v_var 0.
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
  Definition Vert (A B: type) := Context.oftype (A * B).

  #[program]
  Definition id A: Vert A A := E_lam 0 A (E_var 0).

  Next Obligation.
  Proof using.
    unfold Vert.
    apply (Context.typecheck_sound Map.empty).
    cbn.
    destruct (eq_type A A).
    2: contradiction.
    cbn.
    unfold Map.one.
    rewrite Map.minus_add.
    reflexivity.
  Defined.

  #[program]
  Definition compose {A B C} (f: Vert B C) (g: Vert A B): Vert A C := E_lam 0 A (E_app f (E_app g (E_var 0))).

  Next Obligation.
  Proof.
    unfold Vert in *.
    unfold compose.
    destruct f as [f ?], g as [g ?].
    constructor.
    replace (Map.add 0 A _) with (Map.merge Map.empty (Map.one 0 A)).
    2: {
      rewrite Map.merge_empty_l.
      reflexivity.
    }
    econstructor.
    1: eauto.
    replace (Map.one 0 A) with (Map.merge Map.empty (Map.one 0 A)).
    2: {
      rewrite Map.merge_empty_l.
      reflexivity.
    }
    econstructor.
    1: eauto.
    constructor.
  Defined.
End Vert.
