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

Function typecheck Γ v t: bool :=
  match v, t with
  | v_tt, t_unit => true
  | v_fanout v0 v1, t1 * t2 =>
      typecheck Γ v0 t1 && typecheck Γ v1 t2
  | v_neu v, _ =>
      if typeinfer Γ v is Some t'
      then if eq_type t t' then true else false
      else false
  | _, _ => false
  end %bool
with typeinfer Γ V :=
  match V with
  | V_var x => find x Γ
  | V_fst V =>
      do t0 * _ ← typeinfer Γ V ;
      Some t0
  | V_snd V =>
      do _ * t1 ← typeinfer Γ V ;
      Some t1
  | V_cut v t =>
      if typecheck Γ v t
      then Some t
      else None
  end.

Function intro v :=
  match v with
  | v_tt => Some N_tt
  | v_fanout v0 v1 =>
      do v0' ← intro v0 ;
      do v1' ← intro v1 ;
      Some (N_fanout v0' v1')
  | v_neu V => elim V
  end
with elim (V: expr) :=
  match V with
  | V_var _ => None
  | V_fst V =>
      do N_fanout a _ ← elim V ;
      Some a
  | V_snd V =>
      do N_fanout _ a ← elim V ;
      Some a
  | V_cut v _ => intro v
  end.

Theorem typecheck_sound:
  ∀ {Γ v t}, Bool.Is_true (typecheck Γ v t) → Γ ⊢ v in t
with typeinfer_sound:
  ∀ {Γ V t}, typeinfer Γ V = Some t → JV Γ V t.
Proof using .
  - intros Γ v t p.
    destruct v.
    all: cbn.
    + destruct t.
      2: contradiction.
      constructor.
    + destruct t.
      1: contradiction.
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
      constructor.
      apply typeinfer_sound.
      destruct typeinfer.
      2: contradiction.
      destruct eq_type.
      2: contradiction.
      subst.
      auto.
  - intros Γ V t p.
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
      1: discriminate.
      inversion p.
      subst.
      econstructor.
      apply typeinfer_sound.
      eauto.
    + cbn in p.
      destruct typeinfer eqn:q.
      2: discriminate.
      destruct t0.
      1: discriminate.
      inversion p.
      subst.
      econstructor.
      apply typeinfer_sound.
      eauto.
    + cbn in p.
      destruct typecheck eqn:q.
      2: discriminate.
      inversion p.
      subst.
      constructor.
      apply typecheck_sound.
      rewrite q.
      apply I.
Qed.

Theorem typecheck_complete:
  ∀ {Γ v t}, Γ ⊢ v in t → typecheck Γ v t = true
with typeinfer_complete:
  ∀ {Γ V t}, JV Γ V t → typeinfer Γ V = Some t.
Proof using .
  - intros Γ ? ? p.
    destruct p.
    all: cbn in *.
    all: auto.
    all: try rewrite typecheck_complete.
    all: try rewrite typecheck_complete.
    all: auto.
    rewrite (typeinfer_complete Γ V t).
    2: auto.
    destruct eq_type.
    2: contradiction.
    auto.
  - intros Γ ? ? p.
    destruct p.
    all: cbn in *.
    + apply find_complete.
      auto.
    + rewrite (typeinfer_complete Γ V _ p).
      auto.
    + rewrite (typeinfer_complete Γ V _ p).
      auto.
    + rewrite typecheck_complete.
      all: auto.
Qed.

Theorem intro_sound:
  ∀ {v N}, intro v = Some N → v ⇓ N
with elim_sound:
  ∀ {V N}, elim V = Some N → bigV V N
.
Proof using.
  - intros v N p.
    destruct v.
    all: cbn in p.
    + inversion p.
      constructor.
    + destruct intro eqn:q1.
      2: discriminate.
      destruct intro eqn:q2 in p.
      2: discriminate.
      inversion p.
      constructor.
      all: auto.
    + constructor.
      apply elim_sound.
      auto.
  - intros V N p.
    destruct V.
    all: cbn in p.
    + inversion p.
    + destruct elim eqn:q1.
      2: discriminate.
      destruct n.
      1: discriminate.
      inversion p.
      subst.
      econstructor.
      eauto.
    + destruct elim eqn:q1.
      2: discriminate.
      destruct n.
      1: discriminate.
      inversion p.
      subst.
      econstructor.
      eauto.
    + constructor.
      apply intro_sound.
      auto.
Qed.

Theorem intro_complete:
  ∀ {v N}, v ⇓ N → intro v = Some N
with
elim_complete:
  ∀ {V N},
       bigV V N → elim V = Some N.
Proof using.
  - intros ? ? p.
    destruct p.
    all: cbn.
    + auto.
    + repeat erewrite intro_complete.
      all: eauto.
    + auto.
  - intros ? ? p.
    destruct p.
    all: cbn.
    + repeat erewrite elim_complete.
      all: eauto.
      cbn.
      auto.
    + repeat erewrite elim_complete.
      all: eauto.
      cbn.
      auto.
    + apply intro_complete.
      auto.
Qed.

Theorem intro_preserve:
  ∀ {v N},
    v ⇓ N →
    ∀ Γ t, Γ ⊢ v in t → Γ ⊢ N in t
with elim_preserve:
  ∀ {V N},
    bigV V N →
    ∀ Γ t, JV Γ V t → Γ ⊢ N in t
.
Proof using.
  - intros v N p.
    destruct p.
    all: intros ? ? q.
    all: inversion q.
    all: subst.
    all: cbn.
    + auto.
    + constructor.
      all: eauto.
    + eapply elim_preserve.
      all: eauto.
  - intros V N p.
    destruct p.
    all: intros ? ? q.
    all: inversion q.
    all: subst.
    all: cbn.
    + assert (H1' := elim_preserve _ _ p _ _ H1).
      cbn in H1'.
      inversion H1'.
      auto.
    + assert (H1' := elim_preserve _ _ p _ _ H1).
      cbn in H1'.
      inversion H1'.
      auto.
    + eapply intro_preserve.
      all: eauto.
Qed.

Theorem big_unique:
  ∀ {V N N'},
    bigV V N → bigV V N' → N = N'.
Proof using.
  intros V N N' p q.
  assert (p' := elim_complete p).
  assert (q' := elim_complete q).
  rewrite p' in q'.
  inversion q'.
  auto.
Qed.

Theorem intro_normal:
  ∀ {v t},
   nil ⊢ v in t →
   ∃ N, v ⇓ N
with elim_normal:
  ∀ {V t},
   JV nil V t →
   ∃ N, bigV V N.
Proof using.
  - intros v t p.
    destruct v.
    all: inversion p.
    all: subst.
    + exists N_tt.
      constructor.
    + destruct (intro_normal _ _ H2) as [N1 s1].
      destruct (intro_normal _ _ H4) as [N2 s2].
      exists (N_fanout N1 N2).
      constructor.
      all: auto.
    + destruct (elim_normal _ _ H1) as [N s].
      exists N.
      constructor.
      auto.
  - intros V t p.
    destruct V.
    all: inversion p.
    all: subst.
    + inversion H1.
    + destruct (elim_normal _ _ H1) as [N s].
      assert (wf := elim_preserve s _ _ H1).
      destruct N.
      all: inversion wf.
      subst.
      exists N1.
      econstructor.
      eauto.
    + destruct (elim_normal _ _ H1) as [N s].
      assert (wf := elim_preserve s _ _ H1).
      destruct N.
      all: inversion wf.
      subst.
      exists N2.
      econstructor.
      eauto.
    + destruct (intro_normal _ _ H3) as [N s].
      exists N.
      constructor.
      auto.
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

Lemma subst_var {x v}:
  subst_term (V_var x) x v = v
with
  subst_var_elim {x V}:
  subst_expr (V_var x) x V = V.
Proof.
  - destruct v.
    all: cbn.
    all: auto.
    + repeat rewrite subst_var.
      auto.
    + rewrite subst_var_elim.
      auto.
  - destruct V.
    all: cbn.
    all: auto.
    + destruct (eq_var x0 x).
      all: auto.
    + rewrite subst_var_elim.
      auto.
    + rewrite subst_var_elim.
      auto.
    + rewrite subst_var.
      auto.
Qed.

Lemma subst_normal {V x N}: subst_term V x N = N.
Proof using.
  induction N.
  1: reflexivity.
  cbn.
  rewrite IHN1, IHN2.
  reflexivity.
Qed.

Lemma
  subst_preserve:
  ∀ {Γ V' t x},
    JV Γ V' t →
  ∀ {v t'},
    cons (x, t) Γ ⊢ v in t' →
                         Γ ⊢ subst_term V' x v in t'
with
  subst_preserve_elim:
  ∀ {Γ V' t x},
    JV Γ V' t →
  ∀ {V t'},
    JV (cons (x, t) Γ) V t' →
    JV Γ (subst_expr V' x V) t'
.
Proof using.
  - intros Γ V' t x p v.
    destruct v.
    all: cbn.
    all: intros t' q.
    all: inversion q.
    all: subst.
    all: try (econstructor; eauto).
  - intros Γ V' t x p V.
    destruct V.
    all: cbn.
    all: intros t' q.
    all: inversion q.
    all: subst.
    all: try (econstructor; eauto).
    destruct eq_var.
    + subst.
      inversion H1.
      2: contradiction.
      subst.
      auto.
    + inversion H1.
      1: contradiction.
      subst.
      constructor.
      auto.
Qed.

Lemma
  subst_expr_assoc {x f g h}:
  subst_expr f x (subst_expr g x h) = subst_expr (subst_expr f x g) x h
with
  subst_term_assoc {x f g h}:
  subst_term f x (subst_term g x h) = subst_term (subst_expr f x g) x h
.
Proof using.
  - destruct h.
    all: cbn.
    + destruct eq_var.
      1: auto.
      cbn.
      destruct eq_var.
      1: subst; contradiction.
      auto.
    + rewrite subst_expr_assoc.
      auto.
    + rewrite subst_expr_assoc.
      auto.
    + rewrite subst_term_assoc.
      auto.
  - destruct h.
    all: cbn.
    + auto.
    + repeat rewrite subst_term_assoc.
      auto.
    + rewrite subst_expr_assoc.
      auto.
Qed.

Lemma map_term {Γ Γ'}:
  (∀ x t, mem x t Γ → mem x t Γ') →
  ∀ {v t}, Γ ⊢ v in t → Γ' ⊢ v in t
with map_expr {Γ Γ'}:
  (∀ x t, mem x t Γ → mem x t Γ') →
  ∀ {V t}, JV Γ V t → JV Γ' V t.
Proof.
  - intros f ? ? p.
    destruct v.
    all: inversion p.
    all: subst.
    all: clear p.
    + constructor.
    + constructor.
      * eauto.
      * eauto.
    + constructor.
      eauto.
  - intros f ? ? p.
    destruct V.
    all: inversion p.
    all: subst.
    all: clear p.
    + constructor.
      auto.
    + econstructor.
      eauto.
    + econstructor.
      eauto.
    + econstructor.
      eauto.
Qed.

Fixpoint msubst (ρ: subst) (V: expr): expr :=
  if ρ is cons (x, V') ρ'
  then msubst ρ' (subst_expr V' x V)
  else V.

Fixpoint msubst_term (ρ: subst) (v: term): term :=
  if ρ is cons (x, V') ρ'
  then msubst_term ρ' (subst_term V' x v)
  else v.

Lemma msubst_preserve {ρ}:
  ∀ {Γ},
    Jp ρ Γ →
  ∀ {V t},
    JV Γ V t →
    JV nil (msubst ρ V) t.
Proof.
  induction ρ.
  all: intros Γ q.
  all: inversion q.
  all: subst.
  all: cbn.
  1: auto.
  intros V' ? r.
  eapply IHρ.
  all: eauto.
  eapply subst_preserve_elim.
  all: eauto.
Qed.

Theorem msubst_normal {Γ ρ}:
    Jp ρ Γ →
  ∀ {V t},
    JV Γ V t →
    ∃ N, bigV (msubst ρ V) N.
Proof using.
  intros.
  eapply elim_normal.
  eapply msubst_preserve.
  all: eauto.
Qed.

Definition oftype Γ t := { V | JV Γ V t }.

Definition equiv {Γ t} (p q: oftype Γ t): Prop :=
  ∀ ρ, Jp ρ Γ →
  ∃ N, bigV (msubst ρ (proj1_sig p)) N ∧ bigV (msubst ρ (proj1_sig q)) N.

Instance equiv_Reflexive Γ t: Reflexive (@equiv Γ t).
Proof.
  unfold Reflexive.
  intros V ρ q.
  destruct (msubst_normal q (proj2_sig V)) as [N ?].
  exists N.
  split.
  all: auto.
Qed.

Instance equiv_Transitive Γ t: Transitive (@equiv Γ t).
Proof.
  unfold Transitive.
  intros ? ? ? f g ? q.
  destruct (f _ q) as [f' [? fq]], (g _ q) as [g' [gq ?]].
  assert (eqv := big_unique fq gq).
  subst.
  exists g'.
  split.
  all: auto.
Qed.

Instance equiv_Symmetric Γ t: Symmetric (@equiv Γ t).
Proof.
  unfold Symmetric.
  intros ? ? f ? q.
  destruct (f _ q) as [f' [? ?]].
  exists f'.
  split.
  all: auto.
Qed.

Instance equiv_Equivalence Γ t: Equivalence (@equiv Γ t) := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid Γ t: Setoid (oftype Γ t) := {
    equiv := @equiv Γ t ;
}.

Lemma msubst_fst {ρ}:
  ∀ {V}, msubst ρ (V_fst V) = V_fst (msubst ρ V).
Proof.
  induction ρ.
  1: auto.
  cbn.
  destruct a.
  intros V.
  rewrite IHρ.
  auto.
Qed.

Lemma msubst_snd {ρ}:
  ∀ {V}, msubst ρ (V_snd V) = V_snd (msubst ρ V).
Proof.
  induction ρ.
  1: auto.
  cbn.
  destruct a.
  intros V.
  rewrite IHρ.
  auto.
Qed.

Lemma msubst_cut {ρ}:
  ∀ {v t}, msubst ρ (V_cut v t) = V_cut (msubst_term ρ v) t.
Proof.
  induction ρ.
  1: auto.
  cbn.
  destruct a.
  intros V t.
  rewrite IHρ.
  auto.
Qed.

Lemma msubst_fanout {ρ}:
  ∀ {v1 v2}, msubst_term ρ (v_fanout v1 v2) = v_fanout (msubst_term ρ v1) (msubst_term ρ v2).
Proof.
  induction ρ.
  1: auto.
  cbn.
  destruct a.
  intros V t.
  repeat rewrite IHρ.
  auto.
Qed.

Lemma msubst_neu {ρ}:
  ∀ {V}, msubst_term ρ (v_neu V) = v_neu (msubst ρ V).
Proof.
  induction ρ.
  1: auto.
  cbn.
  destruct a.
  intros V.
  rewrite IHρ.
  auto.
Qed.
