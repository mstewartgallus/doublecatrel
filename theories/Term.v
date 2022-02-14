Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Import Coq.Classes.SetoidClass.

Import IfNotations.

Require Import FunInd.

Instance multi_Reflexive: Reflexive multi.
Proof using.
  econstructor.
Qed.

Instance multi_trans: Transitive multi.
Proof using.
  intros v1 v2 v3 p.
  generalize  v3.
  induction p.
  1: auto.
  intros.
  econstructor.
  1: apply H.
  apply IHp.
  auto.
Qed.

Instance fst_Proper: Proper (step ==> step) v_fst.
Proof.
  intros ? ? p.
  induction p.
  all: constructor.
  all: constructor.
  all: auto.
Defined.

Instance snd_Proper: Proper (step ==> step) v_fst.
Proof.
  intros ? ? p.
  induction p.
  all: constructor.
  all: constructor.
  all: auto.
Defined.

Instance fanout_l_Proper x: Proper (step ==> step) (v_fanout x).
Proof.
  intros ? ? p.
  induction p.
  all: constructor.
  all: constructor.
  all: auto.
Qed.

Instance fanout_r_Proper: Proper (step ==> eq ==> step) v_fanout.
Proof.
  intros ? ? p.
  induction p.
  all: intros ? ? q.
  all: subst.
  all: constructor.
  all: constructor.
  all: auto.
Defined.

Instance fst_multi_Proper: Proper (multi ==> multi) v_fst.
Proof.
  intros ? ? p.
  induction p.
  1: reflexivity.
  econstructor.
  2: apply IHp.
  constructor.
  auto.
Defined.

Instance snd_multi_Proper: Proper (multi ==> multi) v_snd.
Proof.
  intros ? ? p.
  induction p.
  1: reflexivity.
  econstructor.
  2: apply IHp.
  constructor.
  auto.
Defined.

Instance fanout_multi_Proper: Proper (multi ==> multi ==> multi) v_fanout.
Proof.
  intros ? ? p.
  induction p.
  - intros ? ? q.
    induction q.
    + reflexivity.
    + econstructor.
      * eapply step_fanoutr.
        eauto.
      * auto.
  - intros ? ? q.
    induction q.
    + econstructor.
      2: eapply IHp.
      1: econstructor.
      1: auto.
      reflexivity.
    + econstructor.
      2: apply IHq.
      eapply step_fanoutr.
      auto.
Qed.

Instance equiv_Reflexive: Reflexive Spec.equiv.
Proof.
  intros.
  econstructor.
  all: reflexivity.
Defined.

Instance equiv_Symmetric: Symmetric Spec.equiv.
Proof.
  intros ? ? [p q s].
  exists s.
  all: auto.
Defined.

(* FIXME seems like a big hole *)
Instance equiv_Transitive: Transitive Spec.equiv.
Proof.
  admit.
Admitted.

Instance equiv_Equivalence: Equivalence Spec.equiv := { Equivalence_Reflexive := _ }.

Instance term_Setoid: Setoid term := { equiv := Spec.equiv }.

  Function typecheck (v: term): option type :=
  match v with
  | v_tt => Some t_unit
  | v_fst v =>
      if typecheck v is Some (t0 * _)
      then
        Some t0
      else
        None
  | v_snd v =>
      if typecheck v is Some (_ * t1)
      then
        Some t1
      else
        None
  | v_fanout v0 v1 =>
      if typecheck v0 is Some t0
      then
        if typecheck v1 is Some t1
        then
          Some (t0 * t1)
        else
          None
      else
        None
  end.

Theorem typecheck_sound:
  forall v t, typecheck v = Some t -> ⊢ v in t.
Proof using .
  intros v.
  functional induction (typecheck v).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
Qed.

Theorem typecheck_complete:
  forall v t, ⊢ v in t -> typecheck v = Some t.
Proof using .
  intros ? ? p.
  induction p.
  all: cbn.
  all: try (destruct (typecheck v) as [[]|]).
  all: try (destruct (typecheck v1)).
  all: try (destruct (typecheck v2)).
  all: try inversion IHp.
  all: subst.
  all: try inversion IHp1.
  all: subst.
  all: try inversion IHp2.
  all: subst.
  all: reflexivity.
Qed.

Definition of_t t := { v | ⊢ v in t }.

Definition tc v: if typecheck v is Some t
                 then
                   of_t t
                 else
                   unit.
Proof.
  destruct (typecheck v) eqn:q.
  2: apply tt.
  exists v.
  apply typecheck_sound.
  auto.
Defined.

Function beta v :=
  match v with
  | v_fst (v_fanout v _) => Some v
  | v_snd (v_fanout _ v) => Some v

  | v_tt => None
  | _ => None
  end.

Lemma beta_sound:
  forall v v', beta v = Some v' -> Spec.beta v v'.
Proof using.
  intros v.
  functional induction (beta v).
  all: intros ? p.
  all: inversion p.
  all: constructor.
Qed.

Lemma beta_complete:
  forall v v', Spec.beta v v' -> beta v = Some v'.
Proof using.
  intros ? ? p.
  induction p.
  all: reflexivity.
Qed.

Function eval v :=
  match v with
  | v_fst v => if eval v is Some v' then Some (v_fst v') else None
  | v_snd v => if eval v is Some v' then Some (v_snd v') else None
  | v_fanout v0 v1 =>
      if eval v0 is Some v0'
      then
        Some (v_fanout v0' v1)
      else
          if eval v1 is Some v1'
          then
            Some (v_fanout v0 v1')
          else
            None
  | _ => beta v
  end.

Lemma beta_normal:
  forall v, is_term_norm_of_term v = true -> beta v = None.
Proof.
  intros v.
  functional induction (beta v).
  all: cbn.
  all: intros p.
  all: inversion p.
  all: reflexivity.
Qed.

Theorem eval_sound:
  forall v v', eval v = Some v' -> v ~> v'.
Proof using.
  intros v.
  functional induction (eval v).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
  apply beta_sound.
  auto.
Qed.

Theorem beta_preserve:
  forall v v',
    Spec.beta v v' ->
    forall t, ⊢ v in t -> ⊢ v' in t.
Proof using.
  intros v v' p.
  induction p.
  all: intros ? q.
  all: inversion q.
  all: subst.
  - inversion H0.
    subst.
    auto.
  - inversion H0.
    subst.
    auto.
Qed.

Theorem step_preserve:
  forall v v',
    v ~> v' ->
    forall t, ⊢ v in t -> ⊢ v' in t.
Proof using.
  intros v v' p.
  induction p.
  all: intros ? q.
  - inversion q.
    subst.
    econstructor.
    eauto.
  - inversion q.
    subst.
    econstructor.
    eauto.
  - inversion q.
    subst.
    econstructor.
    all: eauto.
  - inversion q.
    subst.
    econstructor.
    all: eauto.
  - eapply beta_preserve.
    all: eauto.
Qed.

Lemma multi_preserve:
  forall v v',
    v *~> v' ->
    forall t, ⊢ v in t -> ⊢ v' in t.
Proof using.
  intros v v' p.
  induction p.
  1: auto.
  intros t q.
  apply IHp.
  refine (step_preserve _ _ _ _ q).
  auto.
Qed.

Theorem step_progress:
  forall v t,
    ⊢ v in t ->
    is_term_norm_of_term v = false -> exists v', v ~> v'.
Proof using.
  intros v t p.
  induction p.
  all: cbn.
  all: intros q.
  all: try discriminate.
  - destruct (is_term_norm_of_term v1) eqn:q1,
        (is_term_norm_of_term v2) eqn:q2.
    all: try discriminate.
    + destruct (IHp2 (eq_refl _)) as [v2' s2].
      exists (v_fanout v1 v2').
      constructor.
      auto.
    + destruct (IHp1 (eq_refl _)) as [v1' s1].
      exists (v_fanout v1' v2).
      constructor.
      auto.
    + destruct (IHp1 (eq_refl _)) as [v1' s1].
      exists (v_fanout v1' v2).
      constructor.
      auto.
  - destruct v.
    all: cbn in IHp.
    all: inversion p.
    all: subst.
    + destruct (IHp (eq_refl _)) as [v' s].
      exists (v_fst v').
      constructor.
      auto.
    + destruct (IHp (eq_refl _)) as [v' s].
      exists (v_fst v').
      constructor.
      auto.
    + exists v1.
      econstructor.
      constructor.
  - destruct v.
    all: cbn in IHp.
    all: inversion p.
    all: subst.
    + destruct (IHp (eq_refl _)) as [v' s].
      exists (v_snd v').
      constructor.
      auto.
    + destruct (IHp (eq_refl _)) as [v' s].
      exists (v_snd v').
      constructor.
      auto.
    + exists v2.
      econstructor.
      constructor.
Qed.

Theorem multi_normalizing:
  forall v t,
    ⊢ v in t ->
   exists v', (v *~> v') /\ is_term_norm_of_term v' = true .
Proof using.
  intros v t p.
  induction p.
  - exists v_tt.
    split.
    all: reflexivity.
  - destruct IHp1 as [v1' [s1 n1]].
    destruct IHp2 as [v2' [s2 n2]].
    exists (v_fanout v1' v2').
    split.
    + rewrite s1, s2.
      reflexivity.
    + cbn.
      rewrite n1, n2.
      cbn.
      reflexivity.
  - destruct IHp as [v' [s n]].
    destruct v'.
    all: cbn in *.
    all: try discriminate.
    + set (p1 := multi_preserve _ _ s _ p).
      inversion p1.
    + set (p1 := multi_preserve _ _ s _ p).
      inversion p1.
      subst.
      exists v'1.
      split.
      * rewrite s.
        cbn.
        econstructor.
        2: reflexivity.
        econstructor.
        econstructor.
      * destruct (is_term_norm_of_term v'1) eqn:q2.
        2: discriminate.
        reflexivity.
  - destruct IHp as [v' [s n]].
    destruct v'.
    all: cbn in *.
    all: try discriminate.
    + set (p1 := multi_preserve _ _ s _ p).
      inversion p1.
    + set (p1 := multi_preserve _ _ s _ p).
      inversion p1.
      subst.
      exists v'2.
      split.
      * rewrite s.
        cbn.
        econstructor.
        2: reflexivity.
        econstructor.
        econstructor.
      * destruct (is_term_norm_of_term v'1) eqn:q1.
        2: discriminate.
        destruct (is_term_norm_of_term v'2) eqn:q2.
        2: discriminate.
        reflexivity.
Qed.
