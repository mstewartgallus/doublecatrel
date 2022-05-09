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

(* FIXME allow axiomizing maps *)
Axiom mem: context → context.
Notation "∈" := mem.

Axiom mem_use: ∀ {Δ1 Δ2 E},
    Δ1 ⊢ E ⊠ Δ2 →
    Δ1 ⊢ ∈ E ⊠ Δ2.
Axiom mem_check: ∀ {Γ E},
  check Γ E set →
  check Γ (∈ E) set.

Definition empty := v_axiom empty_ax t_unit set_x v_tt.
Notation "∅" := empty.

Definition pair v v' := v_axiom pair_ax (set * set) set_x (v_fanout v v').

Definition union := v_axiom union_ax set set_x.
Notation "⋃" := union.

Definition infinity := v_axiom infinity_ax t_unit set_x v_tt.
Notation "∞" := infinity.

Definition powerset := v_axiom powerset_ax set set_x.

Lemma empty_check: ∀ {Γ}, Γ ⊢ ∅ ⇐ set.
Proof.
  intro.
  constructor.
  constructor.
Qed.

Lemma pair_check: ∀ {Γ v v'},
    Γ ⊢ v ⇐ set →
    Γ ⊢ v' ⇐ set →
    Γ ⊢ pair v v' ⇐ set.
Proof.
  intros.
  constructor.
  constructor.
  all: auto.
Qed.

Lemma union_check: ∀ {Γ v},
    Γ ⊢ v ⇐ set →
    Γ ⊢ ⋃ v ⇐ set.
Proof.
  intros.
  constructor.
  auto.
Qed.

Lemma infinity_check: ∀ {Γ},
    Γ ⊢ ∞ ⇐ set.
Proof.
  intros.
  constructor.
  constructor.
Qed.

Lemma powerset_check: ∀ {Γ v},
    Γ ⊢ v ⇐ set →
    Γ ⊢ powerset v ⇐ set.
Proof.
  intros.
  constructor.
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
