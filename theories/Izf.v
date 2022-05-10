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

Definition set_x: var := 0.
Definition set := t_var set_x.

Definition empty_ax: var := 0.
Definition pair_ax: var := 1.
Definition union_ax: var := 2.
Definition infinity_ax: var := 3.
Definition powerset_ax: var := 4.

(* FIXME allow axiomizing relations *)
Axiom mem: context → context.
Notation "∈" := mem.

Axiom mem_use: ∀ {Δ1 Δ2 E},
    sE Δ1 E Δ2 →
    sE Δ1 (∈ E) Δ2.
Axiom mem_check: ∀ {X Γ E},
  check X Γ E set →
  check X Γ (∈ E) set.

Definition IZF: globals := [
    (empty_ax, g_function t_unit set_x) ;
    (pair_ax, g_function (set * set) set_x) ;
    (union_ax, g_function set set_x) ;
    (infinity_ax, g_function t_unit set_x) ;
    (powerset_ax, g_function set set_x)
].

Definition empty := v_axiom empty_ax v_tt.
Notation "∅" := empty.

Definition pair v v' := v_axiom pair_ax (v_fanout v v').

Definition union := v_axiom union_ax.
Notation "⋃" := union.

Definition infinity := v_axiom infinity_ax v_tt.
Notation "∞" := infinity.

Definition powerset := v_axiom powerset_ax.

Lemma empty_check: ∀ {Γ}, IZF @ Γ ⊢ ∅ ⇐ set.
Proof.
  intro.
  econstructor.
  1: reflexivity.
  constructor.
Qed.

Lemma pair_check: ∀ {Γ v v'},
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

Lemma union_check: ∀ {Γ v},
    IZF @ Γ ⊢ v ⇐ set →
    IZF @ Γ ⊢ ⋃ v ⇐ set.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  auto.
Qed.

Lemma infinity_check: ∀ {Γ},
    IZF @ Γ ⊢ ∞ ⇐ set.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  constructor.
Qed.

Lemma powerset_check: ∀ {Γ v},
    IZF @ Γ ⊢ v ⇐ set →
    IZF @ Γ ⊢ powerset v ⇐ set.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  auto.
Qed.

(* not sure here *)
Axiom empty_accepts:
  ∀ {ρ1 ρ2 ρ3 E v},
    accepts ρ1 E v ρ2 →
    accepts ρ2 (∈ E) ∅ ρ3 →
    False.
    (* accepts ρ2 false v' ρ3. *)

Axiom pair_accepts_1:
  ∀ {ρ1 ρ2 E v v'},
    accepts ρ1 E v ρ2 →
    accepts ρ1 (∈ E) (pair v v') ρ2.
Axiom pair_accepts_2:
  ∀ {ρ1 ρ2 E v v'},
    accepts ρ1 E v' ρ2 →
    accepts ρ1 (∈ E) (pair v v') ρ2.
