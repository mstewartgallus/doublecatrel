Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.Opaque.
Require Import Blech.OptionNotations.
Require Import Blech.Assoc.
Require Import Blech.Category.
Require Blech.Environment.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Coq.Arith.PeanoNat Nat.
Require Coq.Bool.Bool.
Require Coq.Lists.List.

Import IfNotations.
Import List.ListNotations.

Require Import FunInd.

Implicit Type Γ: environment.
Implicit Type v: intro.
Implicit Type V: elim.
Implicit Type t: type.
Implicit Types x y: var.
Implicit Type ρ: subst.

Theorem η_preserve {t}:
  ∀ {Γ V},
  Γ ⊢ V ⇒ t →
  Γ ⊢ η t V ⇐ t.
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

Function hsubst_elim ρ V :=
  match V with
  | V_var x => find x ρ
  | V_fst V =>
      do v_fanout v1 _ ← hsubst_elim ρ V ;
      Some v1
  | V_snd V =>
      do v_fanout _ v2 ← hsubst_elim ρ V ;
      Some v2
  end.

Function hsubst_intro ρ v :=
  match v with
  | v_tt => Some v_tt
  | v_fanout v1 v2 =>
      do v1' ← hsubst_intro ρ v1 ;
      do v2' ← hsubst_intro ρ v2 ;
      Some (v_fanout v1' v2')
  | v_neu V => hsubst_elim ρ V
  end.

Notation "V · ρ" := (hsubst_elim ρ V) (at level 30).
Notation " v ∘ ρ" := (hsubst_intro ρ v) (at level 30).

Function hsubst_elim_dfl ρ V :=
  match V with
  | V_var x => if find x ρ is Some v then v else v_tt
  | V_fst V =>
      if hsubst_elim_dfl ρ V is v_fanout v1 _ then v1 else v_tt
  | V_snd V =>
      if hsubst_elim_dfl ρ V is v_fanout _ v2 then v2 else v_tt
  end.

Function hsubst_intro_dfl ρ v :=
  match v with
  | v_tt => v_tt
  | v_fanout v1 v2 =>
      v_fanout (hsubst_intro_dfl ρ v1) (hsubst_intro_dfl ρ v2)
  | v_neu V => hsubst_elim_dfl ρ V
  end.

Definition hsubst_elim_valid ρ V := if V · ρ is Some _ then true else false.
Definition hsubst_intro_valid ρ v := if v ∘ ρ is Some _ then true else false.

Lemma hsubst_elim_complete {ρ V v}:
  hsubstsV V ρ v →
  V · ρ = Some v.
Proof.
  intro p.
  induction p.
  all: cbn in *.
  - rewrite H.
    auto.
  - rewrite IHp.
    auto.
  - rewrite IHp.
    auto.
Qed.

Lemma hsubst_intro_complete {ρ v v'}:
  hsubstsv v ρ v' →
  v ∘ ρ = Some v'.
Proof.
  intro p.
  induction p.
  all: cbn in *.
  - auto.
  - rewrite IHp1, IHp2.
    auto.
  - apply hsubst_elim_complete.
    auto.
Qed.

Lemma hsubst_elim_sound {ρ V}:
  ∀ {v},
  V · ρ = Some v →
  hsubstsV V ρ v.
Proof.
  functional induction (V · ρ).
  all: try discriminate.
  all: intros ? p.
  - constructor.
    auto.
  - inversion p.
    subst.
    econstructor.
    eauto.
  - inversion p.
    subst.
    econstructor.
    eauto.
Qed.

Lemma hsubst_intro_sound {ρ v}:
  ∀ {v'},
  v ∘ ρ = Some v' →
  hsubstsv v ρ v'.
Proof.
  functional induction (v ∘ ρ).
  all: try discriminate.
  all: intros ? p.
  - inversion p.
    constructor.
  - inversion p.
    subst.
    econstructor.
    all: eauto.
  - constructor.
    apply hsubst_elim_sound.
    auto.
Qed.

Lemma hsubst_elim_dfl_sound {ρ V}:
  Bool.Is_true (hsubst_elim_valid ρ V) →
  V · ρ = Some (hsubst_elim_dfl ρ V).
Proof.
  unfold hsubst_elim_valid.
  functional induction (V · ρ).
  all: cbn.
  all: try contradiction.
  all: intros p.
  - destruct find.
    2: contradiction.
    auto.
  - rewrite e0 in IHo.
    assert (IHo' := IHo I).
    inversion IHo'.
    auto.
  - rewrite e0 in IHo.
    assert (IHo' := IHo I).
    inversion IHo'.
    auto.
Qed.

Lemma hsubst_intro_dfl_sound {ρ v}:
  Bool.Is_true (hsubst_intro_valid ρ v) →
  v ∘ ρ = Some (hsubst_intro_dfl ρ v).
Proof.
  unfold hsubst_intro_valid.
  functional induction (v ∘ ρ).
  all: cbn.
  all: try contradiction.
  all: intros p.
  all: auto.
  - rewrite e0 in IHo.
    rewrite e1 in IHo0.
    assert (IHo' := IHo I).
    assert (IHo0' := IHo0 I).
    inversion IHo'.
    inversion IHo0'.
    subst.
    auto.
  - apply hsubst_elim_dfl_sound.
    auto.
Qed.

Lemma hsubst_elim_dfl_complete {ρ V}:
  ∀ {v},
  V · ρ = Some v →
  hsubst_elim_dfl ρ V = v.
Proof.
  functional induction (V · ρ).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: clear p.
  all: auto.
  - rewrite H0.
    auto.
  - rewrite e0 in IHo.
    rewrite (IHo _ eq_refl).
    auto.
  - rewrite e0 in IHo.
    rewrite (IHo _ eq_refl).
    auto.
Qed.

Lemma hsubst_intro_dfl_complete {ρ v}:
  ∀ {v'},
  v ∘ ρ = Some v' →
  hsubst_intro_dfl ρ v = v'.
Proof.
  functional induction (v ∘ ρ).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: clear p.
  all: auto.
  - erewrite IHo, IHo0.
    all: eauto.
  - apply hsubst_elim_dfl_complete.
    auto.
Qed.

Lemma hsubst_elim_preserve {ρ V}:
  ∀ {Γ' Γ},
    Jp Γ' ρ Γ →
  ∀ {t'},
    Γ ⊢ V ⇒ t' →
    Γ' ⊢ hsubst_elim_dfl ρ V ⇐ t'.
Proof.
  functional induction (hsubst_elim_dfl ρ V).
  all: intros ? ? q ? p.
  all: inversion p.
  all: subst.
  all: clear p.
  - generalize dependent t'.
    generalize dependent x.
    induction q.
    all: cbn.
    all: intros ? p ? r.
    all: inversion p.
    destruct PeanoNat.Nat.eq_dec.
    all: subst.
    all: inversion H1.
    all: subst.
    all: inversion r.
    all: subst.
    all: try contradiction.
    + auto.
    + eapply IHq.
      all: eauto.
  - generalize dependent x.
    induction q.
    all: cbn.
    all: intros ? ? p.
    all: inversion p.
    all: subst.
    all: destruct PeanoNat.Nat.eq_dec.
    all: subst.
    all: try contradiction.
    eapply IHq.
    all: eauto.
  - assert (e0' := IHi _ _ q _ H1).
    inversion e0'.
    subst.
    rewrite <- H in e0.
    inversion e0.
    subst.
    auto.
  - assert (e0' := IHi _ _ q _ H1).
    inversion e0'.
    subst.
    rewrite <- H in y.
    contradiction.
  - assert (e0' := IHi _ _ q _ H1).
    inversion e0'.
    subst.
    rewrite <- H in e0.
    inversion e0.
    subst.
    auto.
  - assert (e0' := IHi _ _ q _ H1).
    inversion e0'.
    subst.
    rewrite <- H in y.
    contradiction.
Qed.

Lemma hsubst_preserve_intro {ρ v}:
  ∀ {Γ' Γ},
    Jp Γ' ρ Γ →
  ∀ {t'},
    Γ ⊢ v ⇐ t' →
    Γ' ⊢ hsubst_intro_dfl ρ v ⇐ t'.
Proof.
  functional induction (hsubst_intro_dfl ρ v).
  all: intros ? ? q ? p.
  all: inversion p.
  all: subst.
  all: clear p.
  - constructor.
  - constructor.
    all: eauto.
  - eapply hsubst_elim_preserve.
    all: eauto.
Qed.

Lemma map_elim {Γ Γ'}:
  (∀ x t, mem x t Γ → mem x t Γ') →
  ∀ {V t}, Γ ⊢ V ⇒ t → Γ' ⊢ V ⇒ t.
Proof using.
  intros ? ? ? p.
  induction p.
  all: econstructor.
  all: eauto.
Qed.

Lemma map_intro {Γ Γ'}:
  (∀ x t, mem x t Γ → mem x t Γ') →
  ∀ {v t}, Γ ⊢ v ⇐ t → Γ' ⊢ v ⇐ t.
Proof.
  intros ? ? ? p.
  induction p.
  all: econstructor.
  all: eauto.
  eapply map_elim.
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

Fixpoint typeinfer_sound {Γ V t}: typeinfer Γ V = Some t → Γ ⊢ V ⇒ t.
Proof using .
  - intros p.
    destruct V.
    all: cbn.
    + cbn in p.
      constructor.
      apply Environment.find_sound.
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
  Bool.Is_true (typecheck Γ v t) → Γ ⊢ v ⇐ t.
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

Definition typeinfer_complete {Γ V t} (p: Γ ⊢ V ⇒ t): typeinfer Γ V = Some t.
Proof using .
  induction p.
  all: cbn.
  - apply Environment.find_complete.
    auto.
  - rewrite IHp.
    auto.
  - rewrite IHp.
    auto.
Qed.

Definition typecheck_complete {Γ v t} (p: Γ ⊢ v ⇐ t): typecheck Γ v t = true.
Proof using .
  induction p.
  all: cbn in *.
  all: auto.
  all: try rewrite IHp.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
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

Definition idsubst: environment → subst := List.map (λ '(x, t), (x, η t (V_var x))).

Lemma hsubst_elim_idsubst {Γ V t}:
  Γ ⊢ V ⇒ t →
  hsubst_elim_dfl (idsubst Γ) V = η t V.
Proof.
  intros p.
  induction p.
  all: cbn.
  - induction H.
    all: cbn.
    all: destruct PeanoNat.Nat.eq_dec.
    all: subst.
    all: try contradiction.
    + auto.
    + eauto.
  - rewrite IHp.
    cbn.
    auto.
  - rewrite IHp.
    cbn.
    auto.
Qed.

Lemma hsubst_intro_idsubst {Γ v t}:
  Γ ⊢ v ⇐ t →
  hsubst_intro_dfl (idsubst Γ) v = v.
Proof.
  intros p.
  induction p.
  all: cbn.
  1: auto.
  - rewrite IHp1, IHp2.
    auto.
  - cbn.
    apply (hsubst_elim_idsubst H).
Qed.

Lemma hsubst_elim_assoc {x y f}:
  ∀ {g h Γ B C D},
    JV [(x, C)] f D →
    [(y, B)] ⊢ g ⇐ C →
    Γ ⊢ h ⇐ B →
    hsubst_elim_dfl [(x, hsubst_intro_dfl [(y, h)] g)] f = hsubst_intro_dfl [(y, h)] (hsubst_elim_dfl [(x, g)] f).
Proof.
  induction f.
  all: cbn.
  all: intros ? ? ? ? ? ? p q r.
  all: inversion p.
  all: subst.
  all: clear p.
  - inversion H1.
    all: subst.
    2: inversion H6.
    destruct PeanoNat.Nat.eq_dec.
    2: contradiction.
    auto.
  - erewrite IHf.
    all: eauto.
    eassert (H1' := hsubst_elim_preserve _ H1).
    Unshelve.
    4: {
      constructor.
      2: constructor.
      apply q.
    }
    inversion H1'.
    subst.
    symmetry in H.
    destruct hsubst_elim_dfl.
    all: cbn.
    all: auto.
    discriminate.
  - erewrite IHf.
    all: eauto.
    eassert (H1' := hsubst_elim_preserve _ H1).
    Unshelve.
    4: {
      constructor.
      2: constructor.
      apply q.
    }
    inversion H1'.
    subst.
    cbn.
    symmetry in H.
    destruct hsubst_elim_dfl.
    all: auto.
    discriminate.
Qed.

#[local]
Lemma hsubst_intro_assoc {x y f}:
  ∀ {g h Γ B C D},
  [(x, C)] ⊢ f ⇐ D →
  [(y, B)] ⊢ g ⇐ C →
  Γ ⊢ h ⇐ B →
  hsubst_intro_dfl [(x, hsubst_intro_dfl [(y, h)] g)] f = hsubst_intro_dfl [(y, h)] (hsubst_intro_dfl [(x, g)] f).
Proof.
  induction f.
  all: cbn.
  all: intros ? ? ? ? ? ? p q r.
  all: inversion p.
  all: subst.
  all: clear p.
  all: auto.
  - erewrite IHf1, IHf2.
    all: eauto.
  - eapply hsubst_elim_assoc.
    all: eauto.
Qed.
