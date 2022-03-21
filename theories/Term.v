Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.Opaque.
Require Import Blech.OptionNotations.
Require Import Blech.Environment.
Require Import Blech.Category.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Coq.Bool.Bool.
Require Coq.Lists.List.

Import IfNotations.

Require Import FunInd.

Implicit Type Γ: environment.
Implicit Type v: term.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types x y: var.
Implicit Type ρ: subst.

Function η t V :=
  match t with
  | t_var _ => v_neu V
  | t_unit => v_tt
  | t1 * t2 =>
      v_fanout (η t1 (V_fst V))  (η t2 (V_snd V))
  end.

Theorem η_preserve {t}:
  ∀ {Γ V},
  JV Γ V t →
  Γ ⊢ η t V in t.
Proof.
  induction t.
  all: cbn.
  all: intros ? ? q.
  - intros.
    constructor.
    auto.
  - constructor.
  - constructor.
    + eapply IHt1.
      econstructor.
      eauto.
    + eapply IHt2.
      econstructor.
      eauto.
Qed.

Function lookup x ρ: option term :=
  if ρ is ((y, t) :: ρ')%list
  then
    if eq_var x y
    then Some t
    else lookup x ρ'
  else None.

Function hsubst_expr ρ V :=
  match V with
  | V_var x => lookup x ρ
  | V_fst V =>
      do v_fanout v1 _ ← hsubst_expr ρ V ;
      Some v1
  | V_snd V =>
      do v_fanout _ v2 ← hsubst_expr ρ V ;
      Some v2
  end.

Function hsubst_term ρ v :=
  match v with
  | v_tt => Some v_tt
  | v_fanout v1 v2 =>
      do v1' ← hsubst_term ρ v1 ;
      do v2' ← hsubst_term ρ v2 ;
      Some (v_fanout v1' v2')
  | v_neu V => hsubst_expr ρ V
  end.

Lemma hsubst_preserve_expr {ρ V}:
  ∀ {Γ' Γ},
    Jp Γ' ρ Γ →
  ∀ {t'},
    JV Γ V t' →
    ∀ {vout}, hsubst_expr ρ V = Some vout →
    Γ' ⊢ vout in t'.
Proof.
  functional induction (hsubst_expr ρ V).
  all: intros ? ? q ? p ? r.
  all: inversion p.
  all: subst.
  all: clear p.
  all: try discriminate.
  - generalize dependent r.
    generalize dependent vout.
    generalize dependent H1.
    generalize dependent t'.
    generalize dependent x.
    induction q.
    all: intros ? ? p ? r.
    all: inversion p.
    all: subst.
    + cbn in r.
      destruct eq_var.
      2: contradiction.
      inversion r.
      subst.
      auto.
    + cbn in r.
      destruct eq_var.
      all: subst.
      1: contradiction.
      eapply IHq.
      all: eauto.
  - inversion r.
    subst.
    assert (e0' := IHo _ _ q _ H1 _ e0).
    inversion e0'.
    subst.
    auto.
  - inversion r.
    subst.
    assert (e0' := IHo _ _ q _ H1 _ e0).
    inversion e0'.
    subst.
    auto.
Qed.

Lemma hsubst_preserve_term {ρ v}:
  ∀ {Γ' Γ},
    Jp Γ' ρ Γ →
  ∀ {t'},
    Γ ⊢ v in t' →
    ∀ {vout}, hsubst_term ρ v = Some vout →
    Γ' ⊢ vout in t'.
Proof.
  functional induction (hsubst_term ρ v).
  all: intros ? ? q ? p ? r.
  all: inversion p.
  all: subst.
  all: clear p.
  all: try discriminate.
  - inversion r.
    subst.
    constructor.
  - inversion r.
    subst.
    constructor.
    all: eauto.
  - eapply hsubst_preserve_expr.
    all: eauto.
Qed.

Lemma map_expr {Γ Γ'}:
  (∀ x t, mem x t Γ → mem x t Γ') →
  ∀ {V t}, JV Γ V t → JV Γ' V t.
Proof using.
  intros ? ? ? p.
  induction p.
  all: econstructor.
  all: eauto.
Qed.

Lemma map_term {Γ Γ'}:
  (∀ x t, mem x t Γ → mem x t Γ') →
  ∀ {v t}, Γ ⊢ v in t → Γ' ⊢ v in t.
Proof.
  intros ? ? ? p.
  induction p.
  all: econstructor.
  all: eauto.
  eapply map_expr.
  all: eauto.
Qed.

Lemma hsubst_expr_total {ρ V}:
  ∀ {Γ' Γ},
    Jp Γ' ρ Γ →
  ∀ {t'},
  JV Γ V t' →
  ∃ vout, hsubst_expr ρ V = Some vout.
Proof.
  functional induction (hsubst_expr ρ V).
  all: cbn.
  all: intros ? ? q ? p.
  all: inversion p.
  all: clear p.
  all: subst.
  - generalize dependent x.
    induction q.
    all: cbn in *.
    all: intros ? p.
    all: inversion p.
    all: subst.
    all: cbn in *.
    all: destruct eq_var.
    all: subst.
    all: try contradiction.
    + eexists.
      eauto.
    + eapply IHq.
      auto.
  - eexists.
    eauto.
  - destruct (IHo _ _ q _ H1) as [? e1].
    rewrite e1 in y.
    assert (H1' := hsubst_preserve_expr q H1 e1).
    inversion H1'.
    subst.
    contradiction.
  - eexists.
    eauto.
  - destruct (IHo _ _ q _ H1) as [? e1].
    rewrite e1 in y.
    assert (H1' := hsubst_preserve_expr q H1 e1).
    inversion H1'.
    subst.
    contradiction.
Qed.

Lemma hsubst_term_total {ρ v}:
  ∀ {Γ' Γ},
    Jp Γ' ρ Γ →
  ∀ {t'},
  Γ ⊢ v in t' →
  ∃ vout, hsubst_term ρ v = Some vout.
Proof.
  functional induction (hsubst_term ρ v).
  all: cbn.
  all: intros ? ? q ? p.
  all: inversion p.
  all: clear p.
  all: subst.
  - eexists.
    eauto.
  - eexists.
    eauto.
  - destruct (IHo0 _ _ q _ H4) as [? q2].
    rewrite q2 in y.
    contradiction.
  - destruct (IHo _ _ q _ H2) as [? q1].
    rewrite q1 in y.
    contradiction.
  - eapply hsubst_expr_total.
    all: eauto.
Qed.

Function typeinfer Γ V :=
  match V with
  | V_var x => find x Γ
  | V_fst V =>
      do t0 * _ ← typeinfer Γ V ;
      Some t0
  | V_snd V =>
      do _ * t1 ← typeinfer Γ V ;
      Some t1
  end.

Function typecheck Γ v t: bool :=
  match v, t with
  | v_tt, t_unit => true
  | v_fanout v0 v1, t1 * t2 =>
      typecheck Γ v0 t1 && typecheck Γ v1 t2
  | v_neu v, t_var _ =>
      if typeinfer Γ v is Some t'
      then if eq_type t t' then true else false
      else false
  | _, _ => false
  end %bool.

Fixpoint typeinfer_sound {Γ V t}: typeinfer Γ V = Some t → JV Γ V t.
Proof using .
  - intros p.
    destruct V.
    all: cbn.
    + cbn in p.
      constructor.
      apply find_sound.
      auto.
    + cbn in p.
      destruct typeinfer eqn:q.
      2: discriminate.
      destruct t0.
      all: try discriminate.
      inversion p.
      subst.
      econstructor.
      apply typeinfer_sound.
      eauto.
    + cbn in p.
      destruct typeinfer eqn:q.
      2: discriminate.
      destruct t0.
      all: try discriminate.
      inversion p.
      subst.
      econstructor.
      apply typeinfer_sound.
      eauto.
Qed.

Fixpoint typecheck_sound {Γ v t}:
  Bool.Is_true (typecheck Γ v t) → Γ ⊢ v in t.
  - intros p.
    destruct v.
    all: cbn.
    + destruct t.
      all: try contradiction.
      constructor.
    + destruct t.
      all: try contradiction.
      cbn in p.
      destruct typecheck eqn:q1.
      2: contradiction.
      destruct typecheck eqn:q2 in p.
      2: contradiction.
      constructor.
      * apply typecheck_sound.
        rewrite q1.
        apply I.
      * apply typecheck_sound.
        rewrite q2.
        apply I.
    + cbn in p.
      destruct t.
      all: try contradiction.
      destruct typeinfer eqn:q.
      all: try contradiction.
      destruct eq_type.
      all: try contradiction.
      subst.
      constructor.
      apply typeinfer_sound.
      auto.
Qed.

Fixpoint typeinfer_complete {Γ V t} (p: JV Γ V t): typeinfer Γ V = Some t.
Proof using .
  - destruct p.
    all: cbn in *.
    + apply find_complete.
      auto.
    + rewrite (typeinfer_complete Γ V _ p).
      auto.
    + rewrite (typeinfer_complete Γ V _ p).
      auto.
Qed.

Fixpoint typecheck_complete {Γ v t} (p: Γ ⊢ v in t): typecheck Γ v t = true.
Proof using .
  destruct p.
  all: cbn in *.
  all: auto.
  all: try rewrite typecheck_complete.
  all: try rewrite typecheck_complete.
  all: auto.
  rewrite (typeinfer_complete H).
  destruct eq_tyvar.
  2: contradiction.
  auto.
Qed.

Definition oftype Γ t := { v | Bool.Is_true (typecheck Γ v t) }.

Definition equiv {Γ t} (p q: oftype Γ t): Prop := proj1_sig p = proj1_sig q.

Instance equiv_Reflexive Γ t: Reflexive (@equiv Γ t).
Proof.
  unfold Reflexive.
  reflexivity.
Qed.

Instance equiv_Transitive Γ t: Transitive (@equiv Γ t).
Proof.
  unfold Transitive, equiv.
  intros ? ? ? f g.
  rewrite f, g.
  auto.
Qed.

Instance equiv_Symmetric Γ t: Symmetric (@equiv Γ t).
Proof.
  unfold Symmetric, equiv.
  intros ? ? f.
  auto.
Qed.

Instance equiv_Equivalence Γ t: Equivalence (@equiv Γ t) := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid Γ t: Setoid (oftype Γ t) := {
    equiv := @equiv Γ t ;
}.

Instance subrelation_equiv_eq {Γ t}: subrelation (@equiv Γ t) (@eq _).
Proof.
  intros v v'.
  destruct v as [? p], v' as [? p'].
  cbn.
  unfold equiv.
  cbn.
  intros r.
  subst.
  replace p with p'.
  1: auto.
  generalize dependent p.
  generalize dependent p'.
  destruct typecheck.
  2: contradiction.
  cbn.
  intros.
  destruct p', p.
  auto.
Qed.
