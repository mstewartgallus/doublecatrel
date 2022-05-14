Require Import Blech.Spec.
Require Import Blech.SpecNotations.
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
Implicit Type τ: type.
Implicit Types x y: var.
Implicit Type ρ: subst.

Theorem η_preserve {τ}:
  ∀ {S F Γ V},
  JV S F Γ V τ →
  Jv S F Γ (η τ V) τ.
Proof.
  induction τ.
  all: cbn.
  all: intros.
  - constructor.
    auto.
  - constructor.
  - constructor.
    + eapply IHτ1.
      econstructor.
      eauto.
    + eapply IHτ2.
      econstructor.
      eauto.
Qed.

Function typeinfer Γ V :=
  match V with
  | V_var x => Assoc.find x Γ
  | V_fst V =>
      do ' τ0 * _ ← typeinfer Γ V ;
      Some τ0
  | V_snd V =>
      do ' _ * τ1 ← typeinfer Γ V ;
      Some τ1
  end.

Function typecheck S Γ v τ: bool :=
  match v, τ with
  | v_function f v, t_var B =>
      if Assoc.find f S is Some (τ, A)
      then
        (if eq_var A B then true else false) &&
         typecheck S Γ v τ
      else
        false
  | v_tt, t_unit => true
  | v_fanout v0 v1, t1 * t2 =>
      typecheck S Γ v0 t1 && typecheck S Γ v1 t2
  | v_neu v, t_var A =>
      if typeinfer Γ v is Some (t_var A')
      then if eq_sort A A' then true else false
      else false
  | _, _ => false
  end %bool.

Fixpoint typeinfer_sound {S F Γ V τ}: typeinfer Γ V = Some τ → JV S F Γ V τ.
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
      destruct t.
      all: try discriminate.
      inversion p.
      subst.
      econstructor.
      apply typeinfer_sound.
      eauto.
    + cbn in p.
      destruct typeinfer eqn:q.
      2: discriminate.
      destruct t.
      all: try discriminate.
      inversion p.
      subst.
      econstructor.
      apply typeinfer_sound.
      eauto.
Qed.

Fixpoint typecheck_sound {S F Γ v τ}:
  Bool.Is_true (typecheck F Γ v τ) → Jv S F Γ v τ.
  - intros p.
    destruct v.
    all: cbn.
    + cbn in *.
      destruct τ eqn:q in p.
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
    + destruct τ.
      all: try contradiction.
      constructor.
    + destruct τ.
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
      destruct τ.
      all: try contradiction.
      destruct typeinfer eqn:q.
      all: try contradiction.
      destruct t.
      all: try contradiction.
      destruct eq_sort.
      all: try contradiction.
      subst.
      constructor.
      apply typeinfer_sound.
      auto.
Qed.

Definition typeinfer_complete {S F Γ V τ} (p: JV S F Γ V τ): typeinfer Γ V = Some τ.
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

Definition typecheck_complete {S F Γ v τ} (p: Jv S F Γ v τ): typecheck F Γ v τ = true.
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

Lemma eval_elim_preserves {S F Γ V τ}:
  JV S F Γ V τ →
   ∀ {ρ Γ'},
     Jp S F ρ Γ' Γ →
  Jv S F Γ' (eval_elim ρ V) τ.
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

Lemma eval_preserves {S F Γ v τ}:
  Jv S F Γ v τ →
   ∀ {ρ Γ'},
     Jp S F ρ Γ' Γ →
  Jv S F Γ' (eval ρ v) τ.
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
