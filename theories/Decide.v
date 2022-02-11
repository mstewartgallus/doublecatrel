Require Import Blech.Spec.
Require Import Blech.Map.

Require Import Coq.Classes.SetoidClass.
Require Coq.Lists.List.

Require Import FunInd.

Import List.ListNotations.
Import IfNotations.

Module Import SpecNotations.
  Infix "*" := t_prod.

  Notation "Γ ⊢ E 'in' t" := (judge_E Γ E t) (at level 90).
  Notation "⊢ v 'in' t" := (judge_v v t) (at level 90).

  Notation "v0 ~> v1" := (step_v v0 v1) (at level 90).
  Notation "v0 *~> v1" := (multi_v v0 v1) (at level 90).
End SpecNotations.

Definition eq_type (x y: type): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Function D x E: option (list _) :=
  match E with
  | E_var y =>
      if eq_var x y then Some [] else None
  | E_all y t E =>
      if eq_var x y
      then
        None
      else
        if D x E is Some E'
        then
          Some (e_forall y t :: E')
        else
          None
  | E_app E0 E1 =>
      if D x E0 is Some E'
      then
        Some (e_app_r E1 :: E')
      else
        if D x E1 is Some E'
        then
          Some (e_app_l E0 :: E')
        else
          None
  end%list.

Lemma I_D: forall x E e', D x E = Some e' -> I e' (E_var x) = E.
Proof using.
  intros x E.
  functional induction (D x E).
  all: intros e' p.
  all: inversion p.
  all: cbn.
  all: subst.
  - reflexivity.
  - rewrite (IHo _ e1).
    reflexivity.
  - rewrite (IHo _ e0).
    reflexivity.
  - rewrite (IHo0 _ e1).
    reflexivity.
Qed.

Function typecheck (Γ: environment) (E: context): option (environment * type) :=
  match E with
  | E_var x =>
      if Env.find x Γ is Some t
      then
        if Env.is_empty (Env.remove x Γ)
        then
          Some (Map.one x t, t)
        else
          None
      else
        None
  | E_all x t1 E =>
      if D x E is Some E'
      then
        if typecheck (Map.merge Γ (Map.one x t1)) E is Some (Γ', t2)
        then
          if Env.find x Γ' is Some t1'
          then
            if eq_type t1 t1'
            then
              Some (Map.minus x Γ', t1 * t2)
            else
              None
          else
            None
        else
          None
      else
        None
  | E_app E E' =>
      if typecheck Γ E is Some (Γ', t1 * t2)
      then
        if typecheck Γ E' is Some (Δ, t1')
        then
          if eq_type t1 t1'
          then
            Some (Map.merge Γ' Δ, t2)
          else
            None
        else
          None
      else
        None
  end
    %list.

Theorem typecheck_sound:
  forall Γ E Δ t, typecheck Γ E = Some (Δ, t) -> Δ ⊢ E in t.
Proof.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: try eauto.
  rewrite <- (I_D _ _ _ e0).
  econstructor.
  1: eauto.
  rewrite (I_D _ _ _ e0).
  auto.
Qed.

Theorem typecheck_complete:
  forall E Γ t, Γ ⊢ E in t -> forall Δ, typecheck Δ E = Some (Γ, t).
Proof.
  intros ? ? ? p.
  induction p.
  all: cbn.
  all: intros ?.
  - admit.
  - rewrite (IHp _).
    unfold find in H.
    rewrite H.
    destruct (eq_type t1 t1).
    2: contradiction.
    destruct (D x (I e_list (E_var x))) eqn:q.
    1: reflexivity.
    admit.
  - rewrite (IHp1 _).
    rewrite (IHp2 _).
    destruct (eq_type t1 t1).
    2: contradiction.
    reflexivity.
Admitted.


Function typeof (v: term): option type :=
  match v with
  | v_tt => Some t_unit
  | v_fst v =>
      if typeof v is Some (t0 * _)
      then
        Some t0
      else
        None
  | v_snd v =>
      if typeof v is Some (_ * t1)
      then
        Some t1
      else
        None
  | v_fanout v0 v1 =>
      if typeof v0 is Some t0
      then
        if typeof v1 is Some t1
        then
          Some (t0 * t1)
        else
          None
      else
        None
  end.

Theorem typeof_sound:
  forall v t, typeof v = Some t -> ⊢ v in t.
Proof using .
  intros v.
  functional induction (typeof v).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
Qed.

Theorem typeof_complete:
  forall v t, ⊢ v in t -> typeof v = Some t.
Proof using .
  intros ? ? p.
  induction p.
  all: cbn.
  all: try (destruct (typeof v) as [[]|]).
  all: try (destruct (typeof v1)).
  all: try (destruct (typeof v2)).
  all: try inversion IHp.
  all: subst.
  all: try inversion IHp1.
  all: subst.
  all: try inversion IHp2.
  all: subst.
  all: reflexivity.
Qed.

Definition E_of_t t := { E | exists Γ, Env.is_empty Γ = true /\ (Γ ⊢ E in t) }.
Definition v_of_t t := { v | ⊢ v in t }.

Definition v_tc v: if typeof v is Some t
                   then
                     v_of_t t
                   else
                     unit.
Proof.
  destruct (typeof v) eqn:q.
  2: apply tt.
  exists v.
  apply typeof_sound.
  auto.
Defined.

Definition E_tc E: if typecheck (Env.empty _) E is Some (Γ, t)
                   then
                     if Env.is_empty Γ
                     then
                       E_of_t t
                     else
                       unit
                   else
                     unit.
Proof.
  destruct (typecheck (Env.empty _) E) as [[Γ t]|] eqn:q1.
  2: apply tt.
  destruct (Env.is_empty Γ) eqn:q2.
  2: apply tt.
  exists E.
  exists Γ.
  split.
  1:  auto.
  apply (typecheck_sound (Env.empty _) E).
  rewrite q1.
  reflexivity.
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
Proof.
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
Proof.
  econstructor.
Qed.

Instance multiv_trans: Transitive multi_v.
Proof.
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
Proof.
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
Proof.
  intros v v' p.
  induction p.
  1: auto.
  intros t q.
  apply IHp.
  refine (stepv_preserve _ _ _ _ q).
  auto.
Qed.

Theorem multiv_normalizing:
  forall v t,
    ⊢ v in t ->
    exists v', (v *~> v') /\ is_term_norm_of_term v' = true .
Proof.
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

Definition beta E :=
  match E with
  | E_app (E_all x _ E0) E1 =>
      if D x E0 is Some E0'
      then
        Some (I E0' E1)
      else
        None
  | _ => None
  end.

Function E_eval E :=
  if beta E is Some E'
  then
    Some E'
  else
    match E with
    | E_all x t E =>
        if E_eval E is Some E'
        then
          Some (E_all x t E')
        else
          None
    | E_app E0 E1 =>
        if E_eval E0 is Some E0'
        then
          Some (E_app E0' E1)
        else
          if E_eval E1 is Some E1'
          then
            Some (E_app E0 E1')
          else
            None
    | _ => None
    end.

Theorem E_eval_sound:
  forall E E', E_eval E = Some E' -> step_E E E'.
Proof using.
  intros E.
  functional induction (E_eval E).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: try (econstructor;eauto).
  - destruct E.
    all: cbn in *.
    all: inversion e.
    destruct E1.
    all: inversion e.
    destruct (D x E1) eqn:q.
    2: discriminate.
    rewrite <- (I_D _ _ _ q).
    inversion e.
    subst.
    econstructor.
  - apply (stepE_ctx (e_forall _ _)).
    auto.
  - apply (stepE_ctx (e_app_r _)).
    auto.
  - apply (stepE_ctx (e_app_l _)).
    auto.
Qed.
