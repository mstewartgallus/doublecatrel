Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Blech.Term.
Require Blech.Context.
Require Blech.Sat.
Require Blech.Map.

Import IfNotations.

Module Import Hor.
  (* FIXME preserve behaviour as well *)
  Definition Hor (A B: type) v :=
    Map.one 0 A ⊢ v in B.
  Existing Class Hor.

  Definition id: term := v_var 0.
  Instance id_Hor A: Hor A A id.
  Proof using.
    unfold Hor.
    constructor.
    cbn.
    reflexivity.
  Defined.

  Definition compose f g := subst_term g 0 f.
  Instance compose_Hor f g {A B C} `{Hor B C f} `{Hor A B g}: Hor A C (compose f g).
  Proof.
    unfold Hor in *.
    generalize dependent C.
    generalize dependent B.
    generalize dependent A.
    generalize dependent g.
    induction f.
    all: cbn.
    all: intros g A B p C q.
    - destruct (eq_var x 0).
      + subst.
        inversion q.
        subst.
        unfold Map.one in H1.
        rewrite Map.find_add in H1.
        inversion H1.
        subst.
        auto.
      + inversion q.
        subst.
        rewrite Map.find_one_ne in H1.
        1: discriminate.
        auto.
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

  Instance tt_Hor A: Hor A t_unit v_tt.
  Proof.
    constructor.
  Defined.

  Instance fanout_Hor f g {A B C} `{Hor C A f} `{Hor C B g}: Hor C (A * B) (v_fanout f g).
  Proof.
    constructor.
    all: auto.
  Defined.

  Instance fst_Hor A B : Hor (A * B) A (v_fst (v_var 0)).
  Proof.
    econstructor.
    constructor.
    cbn.
    reflexivity.
  Defined.

  Instance snd_Hor A B : Hor (A * B) B (v_snd (v_var 0)).
  Proof.
    econstructor.
    constructor.
    cbn.
    reflexivity.
  Defined.

  (* FIXME define setoid equality and prove laws *)
End Hor.

Module Import Vert.
  Definition Vert (A B: type) f :=
    Map.empty ⊢ f ? A * B.
  Existing Class Vert.

  Definition id A := E_lam 0 A (E_var 0).
  Instance id_Vert A: Vert A A (id A).
  Proof using.
    unfold Vert.
    apply (Context.typecheck_sound Map.empty).
    cbn.
    destruct (Context.eq_type A A).
    2: contradiction.
    cbn.
    unfold Map.one.
    rewrite Map.minus_add.
    reflexivity.
  Defined.

  Definition compose (f g: context) A := E_lam 0 A (E_app f (E_app g (E_var 0))).
  Instance compose_Vert f g {A B C} `{Vert B C f} `{Vert A B g}: Vert A C (compose f g A).
  Proof.
    unfold Vert in *.
    unfold compose.
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
