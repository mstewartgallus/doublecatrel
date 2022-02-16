Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Import Coq.Classes.SetoidClass.

Import IfNotations.

Require Import FunInd.

Fixpoint toterm (v: normal): term :=
  match v with
  | N_tt => v_tt
  | N_fanout v0 v1 => v_fanout (toterm v0) (toterm v1)
  end.

Coercion toterm: normal >-> term.

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

Inductive tr A: Prop := tr_intro (_: A).
Definition of_t t := { v | tr (⊢ v in t) }.

Definition tc v: if typecheck v is Some t
                 then
                   of_t t
                 else
                   unit.
Proof.
  destruct (typecheck v) eqn:q.
  2: apply tt.
  exists v.
  exists.
  apply typecheck_sound.
  auto.
Defined.

Function big v :=
  match v with
  | v_tt => Some N_tt
  | v_fst v => if big v is Some (N_fanout a _) then Some a else None
  | v_snd v => if big v is Some (N_fanout _ a) then Some a else None
  | v_fanout v0 v1 =>
      if big v0 is Some v0'
      then
        if big v1 is Some v1'
        then
          Some (N_fanout v0' v1')
        else
          None
      else
        None
  end.

Theorem big_sound:
  forall v N, big v = Some N -> v ⇓ N.
Proof using.
  intros v.
  functional induction (big v).
  all: intros ? p.
  all: inversion p.
  all: subst.
  - constructor.
  - econstructor.
    apply IHo.
    eauto.
  - econstructor.
    apply IHo.
    eauto.
  - econstructor.
    1: apply IHo.
    2: apply IHo0.
    all:  eauto.
Qed.

Theorem big_complete:
  forall v v', v ⇓ v' -> big v = Some v'.
Proof using.
  intros ? ? p.
  induction p.
  all: cbn.
  all: try rewrite IHp.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: reflexivity.
Qed.

Theorem big_preserve:
  forall v v',
    v ⇓ v' ->
    forall t, ⊢ v in t -> ⊢ v' in t.
Proof using.
  intros v v' p.
  induction p.
  all: intros ? q.
  all: inversion q.
  all: subst.
  all: auto.
  - econstructor.
    all: eauto.
  - set (p' := IHp _ H0).
    inversion p'.
    subst.
    auto.
  - set (p' := IHp _ H0).
    inversion p'.
    subst.
    auto.
Qed.

Theorem normalize:
  forall v t,
   ⊢ v in t ->
   { v' & v ⇓ v' }.
Proof using.
  intros ? ? p.
  induction p.
  - exists N_tt.
    constructor.
  - destruct IHp1 as [v1' s1].
    destruct IHp2 as [v2' s2].
    exists (N_fanout v1' v2').
    constructor.
    all: auto.
  - destruct IHp as [v' s].
    set (vwf := big_preserve _ _ s _ p).
    destruct v'.
    all: cbn in *.
    all: try discriminate.
    all: inversion vwf.
    all: subst.
    all: cbn in *.
    exists v'1.
    econstructor.
    all: eauto.
  - destruct IHp as [v' s].
    set (vwf := big_preserve _ _ s _ p).
    destruct v'.
    all: cbn in *.
    all: try discriminate.
    all: inversion vwf.
    all: subst.
    all: cbn in *.
    exists v'2.
    econstructor.
    all: eauto.
Qed.
