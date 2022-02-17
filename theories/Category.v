Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Blech.Term.
Require Blech.Context.
Require Blech.Sat.
Require Blech.Map.

Import IfNotations.

Definition X: var := 0.

Definition Hor (A B: type) v := Map.one X A ⊢ v in B.
Definition Vert (A B: type) E := Map.one X A ⊢ E ? B.

Definition Hor_id := v_var X.

Definition Hor_id_Hor A: Hor A A Hor_id.
Proof.
  unfold Hor.
  apply Term.typecheck_sound.
  reflexivity.
Qed.

Definition Vert_id := E_var X.

Definition Vert_id_Vert A: Vert A A Vert_id.
Proof.
  unfold Vert.
  apply (Context.typecheck_sound (Map.one X A)).
  reflexivity.
Qed.

Definition Hor_compose f g := subst_term g X f.
Definition Vert_compose f g := subst_context g X f.

Definition Hor_compose_Hor:
  forall {f g A B C},
  Hor B C f ->
  Hor A B g ->
  Hor A C (Hor_compose f g).
Proof.
  intros f.
  unfold Hor.
  unfold Hor_compose.
  induction f.
  all: intros g A B C p q.
  - cbn.
    inversion p.
    subst.
    destruct (eq_var x X).
    + subst.
      unfold Map.one in H1.
      cbn in H1.
      inversion H1.
      subst.
      auto.
    + induction x.
      * contradiction.
      * discriminate.
  - cbn.
    inversion p.
    subst.
    constructor.
  - cbn.
    inversion p.
    subst.
    econstructor.
    all: eauto.
  - cbn.
    inversion p.
    subst.
    econstructor.
    all: eauto.
  - cbn.
    inversion p.
    subst.
    econstructor.
    all: eauto.
Qed.

Definition Vert_compose_Hor:
  forall {f g A B C},
  Vert B C f ->
  Vert A B g ->
  Vert A C (Vert_compose f g).
Proof.
  intros f.
  unfold Vert.
  unfold Vert_compose.
  induction f.
  all: intros g A B C p q.
  - cbn.
    inversion p.
    subst.
    destruct (eq_var X X).
    2:contradiction.
    auto.
  - cbn.
    inversion p.
    subst.
    econstructor.
    destruct (eq_var x X).
    + subst.
      unfold Map.one in *.
      cbn.
      replace (Map.add X t (Map.add X A Map.empty)) with (Map.one X t).
      2: {
        cbv.
        admit.
      }
      replace (Map.add X t (Map.add X B Map.empty)) with (Map.one X t) in X0.
      2: {
        cbv.
        admit.
      }
      auto.
    + admit.
  - cbn.
    inversion p.
    subst.
    admit.
  - cbn.
    inversion p.
  - cbn.
    admit.
  - cbn.
    admit.
  - cbn.
    admit.
Admitted.
