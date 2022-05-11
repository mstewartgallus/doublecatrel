Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.Environment.
Require Import Blech.Category.
Require Import Blech.Term.
Require Import Blech.Context.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Arith.PeanoNat.
Require Coq.Lists.List.

Import List.ListNotations.
Import IfNotations.

Implicit Type Γ: environment.
Implicit Type Δ: usage.
Implicit Type E: context.
Implicit Type t: type.
Implicit Types x y: var.
Implicit Type ρ: subst.
Implicit Type v: intro.

Definition set_x: axiom := 0.

Definition mem_ax: axiom := 1.

Definition empty_ax: axiom := 2.
Definition pair_ax: axiom := 3.
Definition union_ax: axiom := 4.
Definition infinity_ax: axiom := 5.
Definition powerset_ax: axiom := 6.

Definition set := t_var set_x.

Definition mem := E_axiom mem_ax.
Notation "∈" := mem.

Definition empty := v_axiom empty_ax v_tt.
Notation "∅" := empty.

Definition pair v v' := v_axiom pair_ax (v_fanout v v').

Definition union := v_axiom union_ax.
Notation "⋃" := union.

Definition infinity := v_axiom infinity_ax v_tt.
Notation "∞" := infinity.

Definition powerset := v_axiom powerset_ax.

Infix "→" := g_function.
Infix "↛" := g_relation (at level 90).

Notation "P ⇒ Q" := (H_seq (fst P) (snd P) (fst Q) (snd Q)) (at level 90).

Definition IZF: signature := [
    (mem_ax, set ↛ set_x) ;

    (empty_ax, t_unit → set_x) ;
    (pair_ax, set * set → set_x) ;
    (union_ax, set → set_x) ;
    (infinity_ax, t_unit → set_x) ;
    (powerset_ax, set → set_x)
].

(* Definition pair_inl_ax: axiom := 7. *)
(* Definition pair_inr_ax: axiom := 8. *)

(* fixme quantify over *)
Definition IZF_axioms: theory := [
    (∈ E_true, ∅) ⇒ (E_false, ∅) ;

    (* FIXME pi1/pi2 *)
    (E_or (∈ E_true) (∈ E_true), pair ∅ ∅) ⇒ (∈ E_true, ∅)
  ].

Lemma mem_use {Δ1 Δ2 E}:
    sE Δ1 E Δ2 →
    sE Δ1 (∈ E) Δ2.
Proof.
  intros.
  constructor.
  auto.
Qed.

Lemma mem_check {Γ E}:
  check IZF Γ E set →
  check IZF Γ (∈ E) set.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  auto.
Qed.

Lemma empty_check {Γ}: IZF @ Γ ⊢ ∅ ⇐ set.
Proof.
  econstructor.
  1: reflexivity.
  constructor.
Qed.

Lemma pair_check {Γ v v'}:
    IZF @ Γ ⊢ v ⇐ set →
    IZF @ Γ ⊢ v' ⇐ set →
    IZF @ Γ ⊢ pair v v' ⇐ set.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  constructor.
  all: auto.
Qed.

Lemma union_check {Γ v}:
    IZF @ Γ ⊢ v ⇐ set →
    IZF @ Γ ⊢ ⋃ v ⇐ set.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  auto.
Qed.

Lemma infinity_check {Γ}:
    IZF @ Γ ⊢ ∞ ⇐ set.
Proof.
  econstructor.
  1: reflexivity.
  constructor.
Qed.

Lemma powerset_check {Γ v}:
    IZF @ Γ ⊢ v ⇐ set →
    IZF @ Γ ⊢ powerset v ⇐ set.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  auto.
Qed.
