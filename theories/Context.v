Require Import Blech.Spec.
Require Import Blech.Map.
Require Import Blech.SpecNotations.

Require Import Coq.Classes.SetoidClass.
Require Coq.Lists.List.

Require Import FunInd.

Import List.ListNotations.
Import IfNotations.

Definition eq_type (x y: type): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Function typecheck (Γ: environment) (E: context): option (environment * type) :=
  match E with
  | E_var x =>
      if Env.find x Γ is Some t
      then
        if Env.is_empty (Env.remove x Γ)
        then
          Some (Map.one x t, t)
        else
          None
      else
        None
  | E_all x t1 E =>
      if typecheck (Map.add x t1 Γ) E is Some (Γ', t2)
      then
        if Env.find x Γ' is Some t1'
        then
          if eq_type t1 t1'
          then
              Some (Map.minus x Γ', t1 * t2)
          else
            None
        else
          None
      else
        None
  | E_app E E' =>
      if typecheck Γ E is Some (Γ', t1 * t2)
      then
        if typecheck Γ E' is Some (Δ, t1')
        then
          if eq_type t1 t1'
          then
            Some (Map.merge Γ' Δ, t2)
          else
            None
        else
          None
      else
        None
  | _ => None
  end
    %list.

Lemma env_add_minus:
  forall x (t: type) Γ,
    Env.find x Γ = Some t ->
    Map.add x t (Map.minus x Γ) = Γ.
Proof.
  intros x t Γ p.
  unfold add, minus.
  admit.
Admitted.

Lemma find_add:
  forall x (t: type) Γ,
    Env.find x (Env.add x t Γ) = Some t.
Proof.
  intros x t.
  admit.
Admitted.

Lemma always_empty:
  forall x (t: type), Env.is_empty (Env.remove x (Env.add x t (Env.empty _))) = true.
Proof.
  intros ? ?.
  unfold one.
  admit.
Admitted.

Lemma remove_add:
  forall x (t: type) Γ,
    Env.remove x (Env.add x t Γ) = Γ.
Proof.
  intros x t.
  admit.
Admitted.

Theorem typecheck_sound:
  forall Γ E Δ t, typecheck Γ E = Some (Δ, t) -> Δ ⊢ E in t.
Proof using.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
  apply IHo.
  rewrite (env_add_minus x t1 Γ').
  2: auto.
  auto.
Qed.

Theorem typecheck_complete:
  forall E Γ t, Γ ⊢ E in t -> typecheck Γ E = Some (Γ, t).
Proof using.
  intros ? ? ? p.
  induction p.
  - unfold typecheck.
    unfold one.
    unfold empty.
    unfold add.
    rewrite (find_add x t (Env.empty _)).
    rewrite always_empty.
    reflexivity.
  - cbn.
    destruct (typecheck (add x t1 G) E) as [[]|] eqn:q1.
    2: discriminate.
    inversion IHp.
    subst.
    unfold add.
    rewrite (find_add x t1 G).
    destruct (eq_type t1 t1).
    2: contradiction.
    unfold minus.
    rewrite remove_add.
    reflexivity.
  - admit.
Admitted.

Definition of_t t := { E | exists Γ, Env.is_empty Γ = true /\ (Γ ⊢ E in t) }.

Definition tc E: if typecheck (Env.empty _) E is Some (Γ, t)
                   then
                     if Env.is_empty Γ
                     then
                       of_t t
                     else
                       unit
                   else
                     unit.
Proof.
  destruct (typecheck (Env.empty _) E) as [[Γ t]|] eqn:q1.
  2: apply tt.
  destruct (Env.is_empty Γ) eqn:q2.
  2: apply tt.
  exists E.
  exists Γ.
  split.
  1:  auto.
  apply (typecheck_sound (Env.empty _)).
  rewrite q1.
  reflexivity.
Defined.
