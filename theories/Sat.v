Require Import Blech.Spec.
Require Blech.Map.
Require Import Blech.SpecNotations.

Require Blech.Context.
Require Blech.Term.

Require Coq.Lists.List.
Require Import Coq.Classes.SetoidClass.

Require Import FunInd.

Import IfNotations.

Definition denote E v := Map.empty ⊢ E[v].

Notation "[[ E ]]" := (denote E).


Definition leibniz E E' :=
  forall v, [[ E ]] v <-> [[ E' ]] v.

Instance leibniz_Reflexive: Reflexive leibniz.
Proof.
  exists.
  all: auto.
Defined.

Instance leibniz_Transitive: Transitive leibniz.
Proof.
  exists.
  - intro.
    apply H0.
    apply H.
    auto.
  - intro.
    apply H.
    apply H0.
    auto.
Defined.

Instance leibniz_Symmetric: Symmetric leibniz.
Proof.
  exists.
  all: apply H.
Defined.

Instance leibniz_Equivalence: Equivalence leibniz := { Equivalence_Reflexive := _ ; }.

Instance leibniz_Setoid: Setoid context := { equiv := leibniz }.

Definition eq_term (x y: term): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Import List.ListNotations.

Notation "'do' x <- e0 ; e1" := (List.flat_map (fun x => e1) e0) (x ident, at level 200, left associativity).

Fixpoint generate (t: type): list term :=
  match t with
  | t_unit => [v_tt]
  | A * B =>
      do v0 <- generate A ;
      do v1 <- generate B ;
      [ v_fanout v0 v1 ]
  end%list.

(* FIXME normalize *)
Fixpoint search (σ: Map.map term) E: list term :=
  match E with
  | E_var x => if Map.find x σ is Some v then [v] else []

  (* normalize ? *)
  | E_all x t E =>
      do v0 <- generate t ;
      do v1 <- search (Map.add x v0 σ) E ;
      [v_fanout v0 v1]

  | E_app E E' =>
      do v0 <- search σ E' ;
      do tuple <- search σ E ;
      if tuple is v_fanout a b
      then
        if eq_term v0 a
        then [b]
        else []
      else
        []

  | E_tt => [v_tt]
  | E_step E E' =>
      do p <- search σ E ;
      do _ <- (if p is v_tt then [tt] else []) ;
      search σ E'

  | E_fanout E E' =>
     do x <- search σ E ;
     do y <- search σ E' ;
     [v_fanout x y]
  | E_let x y E E' =>
      do tuple <- search σ E ;
      do ab <- (if tuple is v_fanout a b then [(a, b)] else []) ;
      search (Map.add x (fst ab) (Map.add y (snd ab) σ)) E'
  end%list.

Lemma Forall_concat:
  forall {A} p (x: list (list A)), List.Forall (List.Forall p) x -> List.Forall p (List.concat x).
Proof.
  all: intros.
  induction H.
  1: econstructor.
  cbn.
  induction H.
  1: auto.
  cbn.
  econstructor.
  1: auto.
  auto.
Qed.

Theorem Forall_flat_map:
  forall {A B} p (f: A -> list B) x, List.Forall (fun x => List.Forall p (f x)) x -> List.Forall p (List.flat_map f x).
Proof.
  intros.
  rewrite List.flat_map_concat_map.
  apply Forall_concat.
  induction H.
  1:econstructor.
  econstructor.
  1: auto.
  auto.
Qed.

Theorem search_sound:
  forall σ E, List.Forall (sat σ E) (search σ E).
Proof.
  intros σ E.
  generalize dependent σ.
  induction E.
  all: cbn.
  all: intros.
  all: try contradiction.
  - destruct (Map.find x σ) eqn:q.
    2: econstructor.
    econstructor.
    2:  econstructor.
    econstructor.
    auto.
  - apply Forall_flat_map.
    induction (generate t).
    1: econstructor.
    econstructor.
    2: auto.
    apply Forall_flat_map.
    induction (IHE (Map.add x a σ)).
    1: econstructor.
    econstructor.
    2: auto.
    econstructor.
    2: econstructor.
    econstructor.
    apply H.
  - apply Forall_flat_map.
    induction (IHE2 σ).
    1: econstructor.
    econstructor.
    2: auto.
    apply Forall_flat_map.
    induction (IHE1 σ).
    1: econstructor.
    cbn.
    econstructor.
    destruct x0.
    all: try econstructor.
    destruct (eq_term x x0_1).
    2: constructor.
    all: cbn.
    2: apply IHf0.
    2: auto.
    1: subst.
    1: constructor.
    1: econstructor.
    1: eauto.
    1: auto.
    1: econstructor.
    admit.
  - all: repeat constructor.
  - apply Forall_flat_map.
    induction (IHE1 σ).
    1: constructor.
    constructor.
    2: apply IHf.
    destruct x.
    all: cbn.
    all: try constructor.
    rewrite List.app_nil_r.
    induction (IHE2 σ).
    1: constructor.
    constructor.
    + constructor.
      all: auto.
    + admit.
  - apply Forall_flat_map.
    induction (IHE1 σ).
    1: constructor.
    constructor.
    2: auto.
    apply Forall_flat_map.
    induction (IHE2 σ).
    1: constructor.
    constructor.
    2: apply IHf0.
    + constructor.
      2: constructor.
      constructor.
      all: auto.
    + admit.
  - admit.
Admitted.

Example id t :=
  let x := 0 in
  E_all x t (E_var x).

Theorem id_sat t v: [[ id t ]] (v_fanout v v).
Proof.
  econstructor.
  cbn.
  econstructor.
  cbn.
  auto.
Defined.

Example conv E :=
  let x := 0 in
  let y := 1 in
  E_let x y E (E_fanout (E_var y) (E_var x)).

Theorem id_conv_id t: id t == conv (id t).
Proof.
  admit.
Admitted.
