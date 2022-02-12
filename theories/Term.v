Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Import Coq.Classes.SetoidClass.

Import IfNotations.

Require Import FunInd.

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

Function eval v :=
  match v with
  | v_fst (v_fanout v _) => Some v
  | v_snd (v_fanout _ v) => Some v

  | v_tt => None
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
  end.

Theorem eval_sound:
  forall v v', eval v = Some v' -> v ~> v'.
Proof using.
  intros v.
  functional induction (eval v).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: try (econstructor;eauto).
  - apply (stepv_ctx V_fst).
    auto.
  - apply (stepv_ctx V_snd).
    auto.
  - apply (stepv_ctx (V_fanout_r _)).
    auto.
  - apply (stepv_ctx (V_fanout_l _)).
    auto.
Qed.

Theorem stepv_preserve:
  forall v v',
    v ~> v' ->
    forall t, ⊢ v in t -> ⊢ v' in t.
Proof using.
  intros v v' p.
  induction p.
  all: intros ? q.
  - inversion q.
    subst.
    inversion H0.
    subst.
    auto.
  - inversion q.
    subst.
    inversion H0.
    subst.
    auto.
  - induction V.
    all: cbn in *.
    + inversion q.
      subst.
      econstructor.
      apply (IHp _ H0).
    + inversion q.
      subst.
      econstructor.
      apply (IHp _ H0).
    + inversion q.
      subst.
      econstructor.
      all: eauto.
    + inversion q.
      subst.
      econstructor.
      all: eauto.
Qed.

Instance multiv_Reflexive: Reflexive multi_v.
Proof using.
  econstructor.
Qed.

Instance multiv_trans: Transitive multi_v.
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

Lemma multiv_ctx:
  forall (v v' : term), v *~> v' -> forall V, appctx_term_ctx_term V v *~> appctx_term_ctx_term V v'.
Proof using.
  intros ? ? p.
  induction p.
  all: intros.
  1: constructor.
  econstructor.
  - econstructor.
    eauto.
  - apply IHp.
Qed.

Lemma multiv_preserve:
  forall v v',
    v *~> v' ->
    forall t, ⊢ v in t -> ⊢ v' in t.
Proof using.
  intros v v' p.
  induction p.
  1: auto.
  intros t q.
  apply IHp.
  refine (stepv_preserve _ _ _ _ q).
  auto.
Qed.

Theorem eval_nonnormal:
  forall v t,
    ⊢ v in t ->
    forall v', eval v = Some v' -> is_term_norm_of_term v = false.
Proof using.
  intros v.
  functional induction (eval v).
  all: cbn.
  all: intros t p.
  all: inversion p.
  all: subst.
  all: try discriminate.
  all: intros ? q.
  all: try reflexivity.
  all: inversion q.
  all: subst.
  - rewrite (IHo _ H1 _ e0).
    reflexivity.
  - rewrite (IHo0 _ H3 _ e1).
    destruct (is_term_norm_of_term v0).
    all: reflexivity.
Qed.

Theorem stepv_progress:
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
      apply (stepv_ctx (V_fanout_l v1)).
      auto.
    + destruct (IHp1 (eq_refl _)) as [v1' s1].
      exists (v_fanout v1' v2).
      apply (stepv_ctx (V_fanout_r v2)).
      auto.
    + destruct (IHp1 (eq_refl _)) as [v1' s1].
      exists (v_fanout v1' v2).
      apply (stepv_ctx (V_fanout_r v2)).
      auto.
  - destruct v.
    all: cbn in IHp.
    all: inversion p.
    all: subst.
    + destruct (IHp (eq_refl _)) as [v' s].
      exists (v_fst v').
      apply (stepv_ctx V_fst).
      auto.
    + destruct (IHp (eq_refl _)) as [v' s].
      exists (v_fst v').
      apply (stepv_ctx V_fst).
      auto.
    + exists v1.
      econstructor.
  - destruct v.
    all: cbn in IHp.
    all: inversion p.
    all: subst.
    + destruct (IHp (eq_refl _)) as [v' s].
      exists (v_snd v').
      apply (stepv_ctx V_snd).
      auto.
    + destruct (IHp (eq_refl _)) as [v' s].
      exists (v_snd v').
      apply (stepv_ctx V_snd).
      auto.
    + exists v2.
      econstructor.
Qed.

Theorem multiv_normalizing:
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
    + rewrite (multiv_ctx _ _ s1 (V_fanout_r v2)).
      rewrite (multiv_ctx _ _ s2 (V_fanout_l v1')).
      reflexivity.
    + cbn.
      rewrite n1, n2.
      cbn.
      reflexivity.
  - destruct IHp as [v' [s n]].
    destruct v'.
    all: cbn in *.
    all: try discriminate.
    + set (p1 := multiv_preserve _ _ s _ p).
      inversion p1.
    + set (p1 := multiv_preserve _ _ s _ p).
      inversion p1.
      subst.
      exists v'1.
      split.
      * rewrite (multiv_ctx _ _ s V_fst).
        cbn.
        econstructor.
        2: reflexivity.
        econstructor.
      * destruct (is_term_norm_of_term v'1) eqn:q2.
        2: discriminate.
        reflexivity.
  - destruct IHp as [v' [s n]].
    destruct v'.
    all: cbn in *.
    all: try discriminate.
    + set (p1 := multiv_preserve _ _ s _ p).
      inversion p1.
    + set (p1 := multiv_preserve _ _ s _ p).
      inversion p1.
      subst.
      exists v'2.
      split.
      * rewrite (multiv_ctx _ _ s V_snd).
        cbn.
        econstructor.
        2: reflexivity.
        econstructor.
      * destruct (is_term_norm_of_term v'1) eqn:q1.
        2: discriminate.
        destruct (is_term_norm_of_term v'2) eqn:q2.
        2: discriminate.
        reflexivity.
Qed.
