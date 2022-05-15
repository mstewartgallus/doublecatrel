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

Definition c_true := c_unify E_tt E_tt t_unit.
Definition c_and c c' := c_unify (E_match_tt c) (E_match_tt c') t_unit.

Definition set_x: sort := 0.

Definition mem_ax: relation := 1.

Definition empty_ax: function := 2.
Definition pair_ax: function := 3.
Definition union_ax: function := 4.
Definition infinity_ax: function := 5.
Definition powerset_ax: function := 6.

Definition set := t_var set_x.

Definition mem E E' := c_relation mem_ax (E_fanout E E').
Infix "∈" := mem (at level 30).

Definition empty := v_function empty_ax v_tt.
Notation "∅" := empty.

Definition pair v v' := v_function pair_ax (v_fanout v v').

Definition union := v_function union_ax.
Notation "⋃" := union.

Definition infinity := v_function infinity_ax v_tt.
Notation "∞" := infinity.

Definition powerset := v_function powerset_ax.

Definition IZF_sorts: sorts := [(set_x, tt)].
Definition IZF_relations: relations := [(mem_ax, set * set)].
Definition IZF_functions: functions := [
    (empty_ax, (t_unit, set_x)) ;
    (pair_ax, (set * set, set_x)) ;
    (union_ax, (set, set_x)) ;
    (infinity_ax, (t_unit, set_x)) ;
    (powerset_ax, (set, set_x))
].

(* FIXME quantify over ? *)
Definition X: var := 0.
Definition Y: var := 1.
Definition Z: var := 2.

Definition IZF_axioms: theory := Eval cbn in [
    H_seq [(X, set)] (E_var X ∈ inject ∅) (c_unify (E_del (E_var X) set) (E_match_tt c_false) t_unit)

    (* H_seq [(X, set)] (c_or (c_unify (E_var Y) (E_var X) set) (c_unify (E_var Z) (E_var X) set)) *)
    (*       (E_var X ∈ inject (pair (v_neu (V_var Y)) (v_neu (V_var Z)))) *)
].

Lemma IZF_wellformed: JT IZF_sorts IZF_functions IZF_relations IZF_axioms.
Proof.
  apply Theory.check_theory_sound.
  constructor.
Qed.

Lemma mem_use {Δ1 Δ2 Δ3 E E'}:
  sE Δ1 E Δ2 →
  sE Δ2 E' Δ3 →
  se Δ1 (E ∈ E') Δ3.
Proof.
  intros.
  constructor.
  econstructor.
  all: eauto.
Qed.

Lemma mem_check {Γ E E'}:
  check IZF_sorts IZF_functions IZF_relations Γ E set →
  check IZF_sorts IZF_functions IZF_relations Γ E' set →
  infer IZF_sorts IZF_functions IZF_relations Γ (E ∈ E').
Proof.
  intros.
  econstructor.
  1: reflexivity.
  constructor.
  all: eauto.
Qed.

Lemma empty_check {Γ}: Jv IZF_sorts IZF_functions Γ ∅ set.
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
    Jv IZF_sorts IZF_functions Γ ∞ set.
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
