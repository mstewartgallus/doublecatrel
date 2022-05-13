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
  ∀ {X F Γ V},
  JV X F Γ V t →
  Jv X F Γ (η t V) t.
Proof.
  induction t.
  all: cbn.
  all: intros ? ? ? q.
  - constructor.
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

Function typeinfer Γ V :=
  match V with
  | V_var x => Assoc.find x Γ
  | V_fst V =>
      do ' t0 * _ ← typeinfer Γ V ;
      Some t0
  | V_snd V =>
      do ' _ * t1 ← typeinfer Γ V ;
      Some t1
  end.

Function typecheck X Γ v t: bool :=
  match v, t with
  | v_function f v, t_var B =>
      if Assoc.find f X is Some (τ, A)
      then
        (if eq_var A B then true else false) &&
         typecheck X Γ v τ
      else
        false
  | v_tt, t_unit => true
  | v_fanout v0 v1, t1 * t2 =>
      typecheck X Γ v0 t1 && typecheck X Γ v1 t2
  | v_neu v, t_var _ =>
      if typeinfer Γ v is Some t'
      then if eq_type t t' then true else false
      else false
  | _, _ => false
  end %bool.

Fixpoint typeinfer_sound {X F Γ V t}: typeinfer Γ V = Some t → JV X F Γ V t.
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

Fixpoint typecheck_sound {X F Γ v t}:
  Bool.Is_true (typecheck F Γ v t) → Jv X F Γ v t.
  - intros p.
    destruct v.
    all: cbn.
    + cbn in *.
      destruct t eqn:q in p.
      all: try contradiction.
      destruct find eqn:r in p.
      2: contradiction.
      destruct p0.
      destruct eq_var in p.
      2: contradiction.
      cbn in p.
      subst.
      econstructor.
      all: eauto.
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

Definition typeinfer_complete {X F Γ V t} (p: JV X F Γ V t): typeinfer Γ V = Some t.
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

Definition typecheck_complete {X F Γ v t} (p: Jv X F Γ v t): typecheck F Γ v t = true.
Proof using .
  induction p.
  all: cbn in *.
  all: auto.
  all: try rewrite IHp.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: auto.
  + destruct find.
    2: discriminate.
    destruct p0.
    inversion H.
    subst.
    destruct eq_var.
    2: contradiction.
    cbn.
    auto.
  + rewrite (typeinfer_complete H).
    destruct eq_function.
    2: contradiction.
    auto.
Qed.

Function eval_elim ρ V :=
  match V with
  | V_var x => if Assoc.find x ρ is Some v then v else v_tt
  | V_fst V =>
      if eval_elim ρ V is v_fanout v1 _ then v1 else v_tt
  | V_snd V =>
      if eval_elim ρ V is v_fanout _ v2 then v2 else v_tt
  end.

Function eval ρ v :=
  match v with
  | v_function K v' => v_function K (eval ρ v')
  | v_tt => v_tt
  | v_fanout v1 v2 =>
      v_fanout (eval ρ v1) (eval ρ v2)
  | v_neu V => eval_elim ρ V
  end.

Lemma eval_elim_preserves {X F Γ V t}:
  JV X F Γ V t →
   ∀ {ρ Γ'},
     Jp X F ρ Γ' Γ →
  Jv X F Γ' (eval_elim ρ V) t.
Proof.
  intros p.
  induction p.
  all: cbn.
  all: intros ? ? q.
  - generalize dependent H.
    induction q.
    all: intros.
    1: inversion H.
    cbn in *.
    inversion H0.
    all: subst.
    + destruct PeanoNat.Nat.eq_dec.
      2: contradiction.
      auto.
    + destruct PeanoNat.Nat.eq_dec.
      1: subst; contradiction.
      auto.
  - assert (IHp' := IHp _ _ q).
    inversion IHp'.
    all: eauto.
  - assert (IHp' := IHp _ _ q).
    inversion IHp'.
    auto.
Qed.

Lemma eval_preserves {X F Γ v t}:
  Jv X F Γ v t →
   ∀ {ρ Γ'},
     Jp X  F ρ Γ' Γ →
  Jv X F Γ' (eval ρ v) t.
Proof.
  intros p.
  induction p.
  all: cbn.
  all: intros ? ? q.
  - econstructor.
    all: eauto.
  - constructor.
    all: eauto.
  - constructor.
    all: eauto.
  - eapply eval_elim_preserves.
    all: eauto.
Qed.
