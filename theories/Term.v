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
  ∀ {v N N'},
    v ⇓ N → v ⇓ N' → N = N'.
Proof using.
  intros v N N' p q.
  set (p' := intro_complete p).
  set (q' := intro_complete q).
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

Definition oftype Γ A := { v | Γ ⊢ v in A }.

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
