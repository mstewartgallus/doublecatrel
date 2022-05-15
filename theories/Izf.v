Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Blech.Term.
Require Blech.Context.
Require Blech.Theory.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Arith.PeanoNat.
Require Coq.Lists.List.

Import List.ListNotations.
Import IfNotations.

Implicit Type Γ: environment.
Implicit Type Δ: usage.
Implicit Type E: context.
Implicit Type τ: type.
Implicit Types x y: var.
Implicit Type ρ: subst.
Implicit Type v: intro.

Import RelNotations.

Definition set: sort := 0.

Definition mem_ax: relation := 1.

Definition empty_ax: function := 2.
Definition pair_ax: function := 3.
Definition union_ax: function := 4.
Definition infinity_ax: function := 5.
Definition powerset_ax: function := 6.

Definition mem E E' := c_relation mem_ax (E_fanout E E').

Definition empty := v_function empty_ax v_tt.

Definition pair v v' := v_function pair_ax (v_fanout v v').

Definition union := v_function union_ax.

Definition infinity := v_function infinity_ax v_tt.

Definition powerset := v_function powerset_ax.

Infix "∈" := mem (in custom rel at level 30).
Notation "∅" := empty (in custom rel).
Notation "⋃" := union.
Notation "∞" := infinity (in custom rel).

Coercion inject: intro >-> context.

Definition IZF_sorts: sorts := [(set, tt)].

Definition IZF_relations: relations := [(mem_ax, <{ set ⊗ set }>)].
Definition IZF_functions: functions := [
    (empty_ax, (<{ I }>, set)) ;
    (pair_ax, (<{ set ⊗ set }>, set)) ;
    (union_ax, (set: type, set)) ;
    (infinity_ax, (<{ I }>, set)) ;
    (powerset_ax, (set: type, set))
].

Definition IZF_axioms: theory := Eval cbn in [
    <{ Π [(X, set: type)] , X ∈ ∅ ⇒ (c_unify (E_del X set) <{ ε, ⊥ }> <{ I }>) }> ;
    <{ Π [(X, set: type); (Y, set:type); (Z, set:type)] ,
        (E_del Z set >> c_unify Y X set) ∨ (E_del Y set >> c_unify Z X set) ⇒
        (X ∈ pair (v_neu Y) (v_neu Z)) }>
].

Lemma IZF_wellformed: JT IZF_sorts IZF_functions IZF_relations IZF_axioms.
Proof.
  apply Theory.check_theory_sound.
  cbv.
  constructor.
Qed.

Lemma mem_use {Δ1 Δ2 Δ3 E E'}:
  sE Δ1 E Δ2 →
  sE Δ2 E' Δ3 →
  se Δ1 <{ E ∈ E' }> Δ3.
Proof.
  intros.
  constructor.
  econstructor.
  all: eauto.
Qed.

Lemma mem_check {Γ E E'}:
  check IZF_sorts IZF_functions IZF_relations Γ E set →
  check IZF_sorts IZF_functions IZF_relations Γ E' set →
  infer IZF_sorts IZF_functions IZF_relations Γ <{ E ∈ E' }>.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  constructor.
  all: eauto.
Qed.

Lemma empty_check {Γ}: Jv IZF_sorts IZF_functions Γ <{ ∅ }> set.
Proof.
  econstructor.
  1: reflexivity.
  constructor.
Qed.

Lemma pair_check {Γ v v'}:
    Jv IZF_sorts IZF_functions Γ v set →
    Jv IZF_sorts IZF_functions Γ v' set →
    Jv IZF_sorts IZF_functions Γ (pair v v') set.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  constructor.
  all: auto.
Qed.

Lemma union_check {Γ v}:
    Jv IZF_sorts IZF_functions Γ v set →
    Jv IZF_sorts IZF_functions Γ (⋃ v) set.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  auto.
Qed.

Lemma infinity_check {Γ}:
    Jv IZF_sorts IZF_functions Γ <{ ∞ }> set.
Proof.
  econstructor.
  1: reflexivity.
  constructor.
Qed.

Lemma powerset_check {Γ v}:
    Jv IZF_sorts IZF_functions Γ v set →
    Jv IZF_sorts IZF_functions Γ (powerset v) set.
Proof.
  intros.
  econstructor.
  1: reflexivity.
  auto.
Qed.
