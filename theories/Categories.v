Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Blech.Environment.
Require Blech.Term.
Require Blech.Context.
Require Blech.Assoc.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Program.Tactics.
Require Import Coq.Lists.List.
Require Coq.Vectors.Fin.
Require Coq.Vectors.Vector.

Import IfNotations.
Import List.ListNotations.

Require Import FunInd.

Implicit Type Γ: environment.
Implicit Type Δ: usage.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type v: intro.
Implicit Type V: elim.
Implicit Types x y: var.
Implicit Type ρ: subst.

Module Import Hor.
  Fixpoint zip {A B} (l: list A) (r: list B): list (A * B) :=
    match l, r with
    | cons a l', cons b r' => cons (a, b) (zip l' r')
    | _, _ => nil
    end.

  Lemma zip_fst_snd {A B} (l: list (A * B)): zip (List.map fst l) (List.map snd l) = l.
  Proof.
    induction l.
    1: reflexivity.
    cbn.
    rewrite IHl.
    destruct a.
    reflexivity.
  Qed.

  Definition Hor A τ := {
      f: list intro → intro |
      ∀ Γ vs, List.Forall2 (λ v τ, Γ ⊢ v ⇐ τ) vs A → Γ ⊢ f vs ⇐ τ
    } .

  #[refine]
  Instance Hor_Setoid τs τ: Setoid (Hor τs τ) := {
      equiv f g := ∀ vs, proj1_sig f vs = proj1_sig g vs
  }.
  Proof.
    exists.
    - intro.
      reflexivity.
    - intro.
      symmetry.
      eauto.
    - intros ? ? ? p q ?.
      rewrite p, q.
      reflexivity.
  Defined.

  #[program]
   Definition id τ: Hor [τ] τ := λ vs, match vs with
                                       | [v] => v
                                       | _ => v_tt
                                       end.

  Next Obligation.
  Proof.
    inversion H.
    subst.
    inversion H4.
    subst.
    auto.
  Qed.


  #[program]
   Definition cut {A B C} (f: Hor (C :: A) B) (g: Hor A C): Hor A B :=
    λ vs, proj1_sig f (proj1_sig g vs :: vs).

  Next Obligation.
  Proof.
    destruct f as [f fp], g as [g gp].
    cbn.
    apply fp.
    constructor.
    1: apply gp.
    all: auto.
  Qed.

  Infix "∘" := cut (at level 30).

  #[program]
  Definition pure_elim A xs V τ: zip xs A ⊢ V ⇒ τ → Hor A τ := λ _ vs, Term.eval_elim (zip xs vs) V.

  Next Obligation.
  Proof.
    apply (Term.eval_elim_preserves j).
    clear j V.
    generalize dependent xs.
    induction H.
    1: destruct xs.
    1,2: constructor.
    destruct xs.
    1: cbn; constructor.
    cbn.
    constructor.
    1: auto.
    eapply IHForall2.
  Qed.

  #[program]
  Definition pure A xs v τ: zip xs A ⊢ v ⇐ τ → Hor A τ := λ _ vs, Term.eval (zip xs vs) v.

  Next Obligation.
  Proof.
    apply (Term.eval_preserves j).
    clear j v.
    generalize dependent xs.
    induction H.
    1: destruct xs.
    1,2: constructor.
    destruct xs.
    1: cbn; constructor.
    cbn.
    constructor.
    1: auto.
    eapply IHForall2.
  Qed.

  Fixpoint mt (n: nat): list var.
  Proof.
    destruct n.
    - apply [].
    - apply cons.
      + apply 0.
      + auto.
  Defined.

  #[program]
   Definition head τ A: Hor (τ :: A) τ :=
    let x := 0 in
    pure_elim (τ :: A) (x :: mt (length A)) (V_var x) τ _.

  Next Obligation.
  Proof.
    constructor.
    constructor.
  Qed.

  #[program]
  Definition tt A: Hor A t_unit := pure A (mt (length A)) v_tt t_unit _.

  Next Obligation.
  Proof.
    constructor.
  Qed.

  #[program]
  Definition fanout A B C: Hor (A :: B :: C) (A * B) :=
      let x: var := 0 in
      let y: var := 1 in
      pure (A :: B :: C)
           (x :: y:: mt (length C))
           (v_fanout (η A (V_var x)) (η B (V_var y)))
           (A * B)
           _.

  Next Obligation.
  Proof.
    econstructor.
    all: apply Term.η_preserve.
    - repeat constructor.
    - repeat constructor.
      auto.
  Qed.

  #[program]
   Definition fst {A B C}: Hor ((A * B) :: C) A :=
    let x: var := 0 in
    pure_elim (A * B :: C)
         (x :: mt (length C))
         (V_fst (V_var x))
         A
         _.

  Next Obligation.
  Proof.
    repeat econstructor.
  Qed.

  #[program]
   Definition snd {A B C}: Hor ((A * B) :: C) B :=
    let x: var := 0 in
    pure (A * B :: C)
         (x :: mt (length C))
         (η B (V_snd (V_var x)))
         B
         _.

  Next Obligation.
  Proof.
    apply Term.η_preserve.
    repeat econstructor.
  Qed.

  Lemma tt_f {A B} {f: Hor A B}: tt _ ∘ f == tt _.
  Proof.
    destruct f as [f fp].
    cbn.
    intro.
    reflexivity.
  Qed.

  Lemma fst_fanout {A B C}: fst ∘ fanout A B C == head _ _.
  Proof.
  Admitted.
End Hor.

Module Import Vert.
  #[local]
  Definition x: var := 0.

  Definition Vert t t' := Context.oftype [(x, t)] t'.

  #[program]
  Definition id t: Vert t t := E_neu (e_var x).

  Next Obligation.
  Proof using.
    destruct eq_type.
    2: contradiction.
    cbv.
    auto.
  Qed.

  #[program]
  Definition compose {A B C} (f: Vert B C) (g: Vert A B): Vert A C := subst_context g x f.

  Next Obligation.
  Proof.
    admit.
  Admitted.

  Lemma compose_id_left {A B} (f: Vert A B): compose (id _) f == f.
  Proof.
    destruct f as [f ?].
    cbn.
    reflexivity.
  Qed.

  Lemma compose_id_right {A B} (f: Vert A B): compose f (id _) == f.
  Proof.
    destruct f as [f ?].
    cbn.
    rewrite Context.subst_var.
    reflexivity.
  Qed.

  Lemma compose_assoc {A B C D} (f: Vert C D) (g: Vert B C) (h: Vert A B):
    compose f (compose g h) == compose (compose f g) h.
  Proof.
    destruct f as [f ?], g as [g ?], h as [h ?].
    cbn.
    rewrite Context.subst_assoc.
    reflexivity.
  Qed.
End Vert.
