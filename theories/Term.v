Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Import Coq.Classes.SetoidClass.
Require Coq.Lists.List.

Import IfNotations.

Require Import FunInd.

Function typecheck (Γ: list (vvar * type)) (v: term): option type :=
  match v with
  | v_var x => find x Γ
  | v_tt => Some t_unit
  | v_fst v =>
      if typecheck Γ v is Some (t0 * _)
      then
        Some t0
      else
        None
  | v_snd v =>
      if typecheck Γ v is Some (_ * t1)
      then
        Some t1
      else
        None
  | v_fanout v0 v1 =>
      if typecheck Γ v0 is Some t0
      then
        if typecheck Γ v1 is Some t1
        then
          Some (t0 * t1)
        else
          None
      else
        None
  end.

Theorem typecheck_sound:
  forall {Γ v t}, typecheck Γ v = Some t -> Γ ⊢ v in t.
Proof using .
  intros Γ v.
  functional induction (typecheck Γ v).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
Qed.

Theorem typecheck_complete:
  forall {Γ v t}, Γ ⊢ v in t -> typecheck Γ v = Some t.
Proof using .
  intros Γ ? ? p.
  induction p.
  all: cbn.
  all: try (destruct (typecheck G v) as [[]|]).
  all: try (destruct (typecheck G v1)).
  all: try (destruct (typecheck G v2)).
  all: try inversion IHp.
  all: subst.
  all: try inversion IHp1.
  all: subst.
  all: try inversion IHp2.
  all: subst.
  all: auto.
Qed.

Function eval v :=
  match v with
  | v_var _ => None
  | v_tt => Some N_tt
  | v_fst v => if eval v is Some (N_fanout a _) then Some a else None
  | v_snd v => if eval v is Some (N_fanout _ a) then Some a else None
  | v_fanout v0 v1 =>
      if eval v0 is Some v0'
      then
        if eval v1 is Some v1'
        then
          Some (N_fanout v0' v1')
        else
          None
      else
        None
  end.

Theorem eval_sound:
  forall {v N}, eval v = Some N -> v ⇓ N.
Proof using.
  intros v.
  functional induction (eval v).
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

Theorem eval_complete:
  forall {v v'}, v ⇓ v' -> eval v = Some v'.
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
  forall {v v'},
    v ⇓ v' ->
    forall Γ t, Γ ⊢ v in t -> Γ ⊢ v' in t.
Proof using.
  intros v v' p.
  induction p.
  all: intros ? ? q.
  all: inversion q.
  all: subst.
  all: auto.
  - econstructor.
    all: eauto.
  - set (p' := IHp _ _ H1).
    inversion p'.
    subst.
    auto.
  - set (p' := IHp _ _ H1).
    inversion p'.
    subst.
    auto.
Qed.

Theorem big_unique:
  forall {v N N'},
    v ⇓ N -> v ⇓ N' -> N = N'.
Proof using.
  intros v N N' p q.
  set (p' := eval_complete p).
  set (q' := eval_complete q).
  rewrite p' in q'.
  inversion q'.
  auto.
Qed.

Theorem normalize:
  forall {v t},
   nil ⊢ v in t ->
   exists N, v ⇓ N.
Proof using.
  remember nil as G.
  intros ? ? p.
  induction p.
  all: subst.
  - discriminate.
  - exists N_tt.
    constructor.
  - destruct (IHp1 (eq_refl _)) as [v1' s1].
    destruct (IHp2 (eq_refl _)) as [v2' s2].
    exists (N_fanout v1' v2').
    constructor.
    all: auto.
  - destruct (IHp (eq_refl _)) as [v' s].
    set (vwf := big_preserve s _ _ p).
    destruct v'.
    all: cbn in *.
    all: try discriminate.
    all: inversion vwf.
    all: subst.
    all: cbn in *.
    exists v'1.
    econstructor.
    all: eauto.
  - destruct (IHp (eq_refl _)) as [v' s].
    set (vwf := big_preserve s _ _ p).
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

Lemma big_normal:
  forall {N: normal}, N ⇓ N.
Proof using.
  intro N.
  induction N.
  all: cbn.
  all: constructor.
  all: auto.
Qed.

Definition oftype Γ A := { v | Γ ⊢ v in A }.

Lemma subst_normal:
  forall v x {N: normal},
    subst_term v x N = N.
Proof using.
  intros ? ? N.
  induction N.
  1: reflexivity.
  cbn.
  rewrite IHN1, IHN2.
  reflexivity.
Qed.

Lemma msubst_normal:
  forall {p} {N: normal},
    msubst p N = N.
Proof using.
  intros.
  induction p.
  1: reflexivity.
  cbn.
  destruct a.
  rewrite subst_normal.
  auto.
Qed.

Lemma msubst_v_fst:
  forall {p v},
    msubst p (v_fst v) = v_fst (msubst p v).
Proof using.
  intro p.
  induction p.
  1: reflexivity.
  intro v.
  cbn.
  destruct a.
  rewrite IHp.
  cbn.
  reflexivity.
Qed.

Lemma msubst_v_snd:
  forall {p v},
    msubst p (v_snd v) = v_snd (msubst p v).
Proof using.
  intro p.
  induction p.
  1: reflexivity.
  intro v.
  cbn.
  destruct a.
  rewrite IHp.
  cbn.
  reflexivity.
Qed.

Lemma msubst_v_fanout:
  forall {p v v'},
    msubst p (v_fanout v v') = v_fanout (msubst p v) (msubst p v').
Proof using.
  intro p.
  induction p.
  1: reflexivity.
  intros ? ?.
  cbn.
  destruct a.
  rewrite IHp.
  cbn.
  reflexivity.
Qed.

Lemma msubst_preserve:
  forall {v Γ p t},
    Jp p Γ ->
    Γ ⊢ v in t ->
    nil ⊢ msubst p v in t.
Proof using.
  intros v.
  induction v.
  all: intros Γ p t q q'.
  - induction q.
    1: cbn.
    1: inversion q'.
    1: subst.
    1: discriminate.
    cbn.
    1: inversion q'.
    subst.
    unfold find in H2.
    cbn in H2.
    destruct (eq_vvar x x0).
    1: subst.
    1: rewrite msubst_normal.
    1: inversion H2.
    1: subst.
    1: auto.
    apply IHq.
    constructor.
    auto.
  - replace v_tt with (N_tt : term).
    2: reflexivity.
    rewrite msubst_normal.
    inversion q'.
    subst.
    constructor.
  - inversion q'.
    subst.
    rewrite msubst_v_fst.
    econstructor.
    apply (IHv _ _ _ q H1).
  - inversion q'.
    subst.
    rewrite msubst_v_snd.
    econstructor.
    apply (IHv _ _ _ q H1).
  - inversion q'.
    subst.
    rewrite msubst_v_fanout.
    econstructor.
    all: eauto.
Qed.

Definition equiv {Γ A}: Relation_Definitions.relation (oftype Γ A) := fun v v' =>
  forall p,
    Jp p Γ ->
    exists N, (msubst p (proj1_sig v) ⇓ N) /\ (msubst p (proj1_sig v') ⇓ N).

Instance equiv_Reflexive Γ A: Reflexive (@equiv Γ A).
Proof using.
  unfold equiv.
  intros [x p].
  cbn.
  intros σ ?.
  destruct (@normalize (msubst σ x) A).
  - eapply msubst_preserve.
    all: eauto.
  - exists x0.
    split.
    all: auto.
Qed.

Instance equiv_Symmetric Γ A: Symmetric (@equiv Γ A).
Proof using.
  unfold equiv.
  intros [x p] [y q].
  cbn.
  intros t σ r.
  destruct (t σ r).
  destruct H.
  exists x0.
  split.
  all: auto.
Qed.

Instance equiv_Transitive Γ A: Transitive (@equiv Γ A).
Proof using.
  unfold equiv.
  intros [x p] [y q] [z r].
  cbn.
  intros s t σ u.
  destruct (s σ u), (t σ u).
  destruct H, H0.
  set (q' := big_unique H1 H0).
  repeat rewrite q' in *.
  exists x1.
  split.
  all: auto.
Qed.

Instance equiv_Equivalence Γ A: Equivalence (@equiv Γ A) := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid Γ A: Setoid (oftype Γ A) := {
    equiv := equiv ;
}.
