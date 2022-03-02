Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.OptionNotations.
Require Import Blech.Environment.
Require Import Blech.Category.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Coq.Lists.List.

Import IfNotations.

Require Import FunInd.

Implicit Type Γ: environment.
Implicit Type v: term.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types x y: var.

Function typecheck Γ v :=
  match v with
  | v_var x => find x Γ
  | v_tt => Some t_unit
  | v_fst v =>
      do t0 * _ ← typecheck Γ v ;
      Some t0
  | v_snd v =>
      do _ * t1 ← typecheck Γ v ;
      Some t1
  | v_fanout v0 v1 =>
      do t0 ← typecheck Γ v0 ;
      do t1 ← typecheck Γ v1 ;
      Some (t0 * t1)
  end.

Function eval v :=
  match v with
  | v_var _ => None
  | v_tt => Some N_tt
  | v_fst v =>
      do N_fanout a _ ← eval v ;
      Some a
  | v_snd v =>
      do N_fanout _ a ← eval v ;
      Some a
  | v_fanout v0 v1 =>
      do v0' ← eval v0 ;
      do v1' ← eval v1 ;
      Some (N_fanout v0' v1')
  end.

Theorem typecheck_sound:
  ∀ {Γ v t}, typecheck Γ v = Some t → Γ ⊢ v in t.
Proof using .
  intros Γ v.
  functional induction (typecheck Γ v).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
  apply find_sound.
  auto.
Qed.

Theorem typecheck_complete:
  ∀ {Γ v t}, Γ ⊢ v in t → typecheck Γ v = Some t.
Proof using .
  intros Γ ? ? p.
  induction p.
  all: cbn.
  all: cbn in *.
  all: try (destruct (typecheck Γ v) as [[]|]).
  all: try (destruct (typecheck Γ v1)).
  all: try (destruct (typecheck Γ v2)).
  all: auto.
  all: try inversion IHp.
  all: subst.
  all: try inversion IHp1.
  all: subst.
  all: try inversion IHp2.
  all: subst.
  all: auto.
  apply find_complete.
  auto.
Qed.

Theorem eval_sound:
  ∀ {v N}, eval v = Some N → v ⇓ N.
Proof using.
  intros v.
  functional induction (eval v).
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
Qed.

Theorem eval_complete:
  ∀ {v N}, v ⇓ N → eval v = Some N.
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
  ∀ {v N},
    v ⇓ N →
    ∀ Γ t, Γ ⊢ v in t → Γ ⊢ N in t.
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
  ∀ {v N N'},
    v ⇓ N → v ⇓ N' → N = N'.
Proof using.
  intros v N N' p q.
  set (p' := eval_complete p).
  set (q' := eval_complete q).
  rewrite p' in q'.
  inversion q'.
  auto.
Qed.

Theorem normalize:
  ∀ {v t},
   nil ⊢ v in t →
   ∃ N, v ⇓ N.
Proof using.
  intros v.
  induction v.
  all: intros ? p.
  all: inversion p.
  all: subst.
  - inversion H1.
  - exists N_tt.
    constructor.
  - destruct (IHv _ H1) as [v' s].
    set (vwf := big_preserve s _ _ H1).
    destruct v'.
    all: cbn in *.
    all: inversion vwf.
    subst.
    exists v'1.
    econstructor.
    eauto.
  - destruct (IHv _ H1) as [v' s].
    set (vwf := big_preserve s _ _ H1).
    destruct v'.
    all: cbn in *.
    all: inversion vwf.
    subst.
    exists v'2.
    econstructor.
    eauto.
  - destruct (IHv1 _ H2) as [v1' s1].
    destruct (IHv2 _ H4) as [v2' s2].
    exists (N_fanout v1' v2').
    constructor.
    all: auto.
Qed.

Lemma big_normal:
  ∀ {N}, N ⇓ N.
Proof using.
  intro N.
  induction N.
  all: cbn.
  all: constructor.
  all: auto.
Qed.

Definition oftype Γ A := { v | Γ ⊢ v in A }.

Lemma subst_var {x v}:
  subst_term (v_var x) x v = v.
Proof.
  induction v.
  all: cbn.
  all: auto.
  - destruct (eq_var x0 x).
    all: auto.
  - rewrite IHv.
    auto.
  - rewrite IHv.
    auto.
  - rewrite IHv1, IHv2.
    auto.
Qed.

Lemma subst_normal {v x N}: subst_term v x N = N.
Proof using.
  induction N.
  1: reflexivity.
  cbn.
  rewrite IHN1, IHN2.
  reflexivity.
Qed.

Lemma subst_preserve:
  ∀ {Γ v' t x},
    Γ ⊢ v' in t →
  ∀ {v t'},
    cons (x, t) Γ ⊢ v in t' →
    Γ ⊢ subst_term v' x v in t'.
Proof using.
  intros Γ v' t x p v.
  induction v.
  all: cbn.
  all: intros t' q.
  all: inversion q.
  all: subst.
  all: try (econstructor; eauto).
  destruct eq_var.
  - subst.
    inversion H1.
    2: contradiction.
    subst.
    auto.
  - inversion H1.
    1: contradiction.
    subst.
    constructor.
    auto.
Qed.

Lemma subst_assoc {x f g h}:
  subst_term (subst_term h x g) x f = subst_term h x (subst_term g x f).
Proof.
  induction f.
  all: cbn.
  all: auto.
  - destruct eq_var eqn:q.
    1: auto.
    cbn.
    rewrite q.
    auto.
  - rewrite IHf.
    auto.
  - rewrite IHf.
    auto.
  - rewrite IHf1.
    rewrite IHf2.
    auto.
Qed.

Lemma msubst_normal {p N}: msubst p N = N.
Proof using.
  induction p.
  1: reflexivity.
  cbn.
  destruct a.
  rewrite subst_normal.
  auto.
Qed.

Lemma msubst_preserve:
  ∀ {p Γ v t},
    Jp p Γ →
    Γ ⊢ v in t →
    nil ⊢ msubst p v in t.
Proof using.
  intros p.
  induction p.
  all: cbn.
  all: intros.
  - inversion H.
    subst.
    auto.
  - destruct a.
    inversion H.
    subst.
    eapply IHp.
    2: eapply subst_preserve.
    all: eauto.
Qed.

Lemma msubst_fst {p}:
  ∀ {v}, msubst p (v_fst v) = v_fst (msubst p v).
Proof.
  induction p.
  all: cbn.
  1: auto.
  destruct a.
  intro.
  rewrite IHp.
  reflexivity.
Qed.

Lemma msubst_snd {p}:
  ∀ {v}, msubst p (v_snd v) = v_snd (msubst p v).
Proof.
  induction p.
  all: cbn.
  1: auto.
  destruct a.
  intro.
  rewrite IHp.
  reflexivity.
Qed.

Lemma msubst_fanout {p}:
  ∀ {v v'}, msubst p (v_fanout v v') = v_fanout (msubst p v) (msubst p v').
Proof.
  induction p.
  all: cbn.
  1: auto.
  destruct a.
  intros.
  rewrite IHp.
  reflexivity.
Qed.

Definition equiv {Γ t}: Relation_Definitions.relation (oftype Γ t) :=
  λ o o',
  ∀ p,
    Jp p Γ →
    ∃ N, (msubst p (proj1_sig o) ⇓ N) ∧ (msubst p (proj1_sig o') ⇓ N).

Instance equiv_Reflexive Γ t: Reflexive (@equiv Γ t).
Proof using.
  unfold equiv.
  intros [v p].
  cbn.
  intros σ ?.
  destruct (@normalize (msubst σ v) t).
  - eapply msubst_preserve.
    all: eauto.
  - exists x.
    split.
    all: auto.
Qed.

Instance equiv_Symmetric Γ t: Symmetric (@equiv Γ t).
Proof using.
  unfold equiv.
  intros [v p] [v' q].
  cbn.
  intros f σ r.
  destruct (f σ r).
  destruct H.
  exists x.
  split.
  all: auto.
Qed.

Instance equiv_Transitive Γ t: Transitive (@equiv Γ t).
Proof using.
  unfold equiv.
  intros [x p] [y q] [z r].
  cbn.
  intros f g σ u.
  destruct (f σ u), (g σ u).
  destruct H, H0.
  set (q' := big_unique H1 H0).
  repeat rewrite q' in *.
  exists x1.
  split.
  all: auto.
Qed.

Instance equiv_Equivalence Γ t: Equivalence (@equiv Γ t) := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid Γ t: Setoid (oftype Γ t) := {
    equiv := equiv ;
}.

Lemma map:
  ∀ {v t Γ Δ},
    (∀ x t, mem x t Γ → mem x t Δ) →
    Γ ⊢ v in t →
    Δ ⊢ v in t.
Proof.
  intro v.
  induction v.
  all: intros ? ? ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
Qed.

Definition shadow {v Γ x t0 t1 t2}:
  ((x, t0) :: Γ)%list ⊢ v in t2 → ((x, t0) :: (x, t1) :: Γ)%list ⊢ v in t2 :=
  map Environment.shadow.

Definition unshadow {v Γ x t0 t1 t2}:
  ((x, t0) :: (x, t1) :: Γ)%list ⊢ v in t2 → ((x, t0) :: Γ)%list ⊢ v in t2 :=
  map Environment.unshadow.

Module Dec.
  Inductive term {Γ: environment}: type → Set :=
  | v_var {t} (x: var): mem x t Γ → term t
  | v_tt: term t_unit
  | v_fst {t t'} (v: term (t * t')): term t
  | v_snd {t t'} (v: term (t * t')): term t'
  | v_fanout {t t'} (v: term t) (v': term t'): term (t * t').
  Arguments term: clear implicits.

  Program Fixpoint dec {Γ} t v (p: Γ ⊢ v in t): term Γ t :=
    match v with
    | Spec.v_var x => v_var x _
    | Spec.v_tt => v_tt
    | Spec.v_fst v =>
        if typecheck Γ v is Some (t * t')
        then
          v_fst (dec (t * t') v _)
        else
          match _: False with end
    | Spec.v_snd v =>
        if typecheck Γ v is Some (t * t')
        then
          v_snd (dec (t * t') v _)
        else
          match _: False with end
    | Spec.v_fanout v v' =>
        if t is t * t'
        then
          v_fanout (dec t v _) (dec t' v' _)
        else
          match _: False with end
    end.

  Next Obligation.
  Proof.
    inversion p.
    subst.
    auto.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    auto.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    subst.
    set (H1' := typecheck_complete H1).
    rewrite H1' in Heq_anonymous.
    inversion Heq_anonymous.
    subst.
    auto.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    subst.
    set (H1' := typecheck_complete H1).
    rewrite H1' in Heq_anonymous.
    inversion Heq_anonymous.
    subst.
    auto.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    subst.
    set (H' := H t t2).
    set (H2' := typecheck_complete H2).
    rewrite H2' in H'.
    contradiction.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    subst.
    set (H1' := typecheck_complete H1).
    rewrite H1' in Heq_anonymous.
    inversion Heq_anonymous.
    subst.
    auto.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    subst.
    set (H1' := typecheck_complete H1).
    rewrite H1' in Heq_anonymous.
    inversion Heq_anonymous.
    subst.
    auto.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    subst.
    set (H' := H t1 t).
    set (H2' := typecheck_complete H2).
    rewrite H2' in H'.
    contradiction.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    subst.
    auto.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    subst.
    auto.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    subst.
    set (H' := H t1 t2).
    contradiction.
  Qed.
End Dec.

Section Cartesian.
  Import CategoryNotations.

  Context {C: Category}.

  Context {unit: C}.
  Context {prod: C → C → C}.

  Context {bang: ∀ c, C c unit}.
  Context {fst: ∀ a b, C (prod a b) a}.
  Context {snd: ∀ a b, C (prod a b) b}.
  Context {fanout: ∀ a b c, C c a → C c b → C c (prod a b)}.

  Fixpoint obj t: C :=
    match t with
    | t_unit => unit
    | t_prod t t' => prod (obj t) (obj t')
    end.

  Fixpoint env Γ: C :=
    if Γ is cons ((_, t)) T
    then
      prod (obj t) (env T)
    else
      unit.

  Open Scope category.

  Import Dec.

  Fixpoint mor' {Γ t} (v: Dec.term Γ t) {A} {struct v}: (∀ x t, mem x t Γ → C A (obj t)) → C A (obj t) :=
    match v in term _ t' return (∀ x t, mem x t Γ → C A (obj t)) → C A (obj t') with
    | @v_var _ t' x p => λ h, h x t' p
    | v_tt => λ _, bang _
    | v_fst v => λ h, compose (fst _ _) (mor' v h)
    | v_snd v => λ h, compose (snd _ _) (mor' v h)
    | v_fanout v v' => λ h, fanout _ _ _ (mor' v h) (mor' v' h)
    end.

  Program Fixpoint find x t Γ (p: mem x t Γ): C (env Γ) (obj t) :=
    match Γ with
    | cons (y, t') T =>
        match eq_var x y with
        | left _ =>
          fst (obj t) (env T)
        | right _ =>
            compose (find x t T _) (snd (obj t') (env T))
        end
    | nil => match _: False with end
    end %list.

  Next Obligation.
  Proof.
    inversion p.
    all: subst.
    all: auto.
    contradiction.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    all: subst.
    1: contradiction.
    auto.
  Qed.

  Next Obligation.
  Proof.
    inversion p.
    all: subst.
    all: eapply H.
    all: auto.
  Qed.

  Definition mor {Γ t} v (p: Γ ⊢ v in t) := mor' (Dec.dec t v p) (λ x t, find _ _ _).
End Cartesian.
