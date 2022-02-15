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

Fixpoint mon {A B} (x: list A) (y: list B): list _ :=
  match x with
  | cons H T => List.map (fun y' => (H, y')) y ++ mon T y
  | _ => nil
  end.
Infix ">*<" := mon (at level 30).

Lemma mon_nil:
  forall {A B} (x: list A), x >*< @nil B = nil.
Proof using.
  intros ? ? x.
  induction x.
  1: reflexivity.
  cbn.
  rewrite IHx.
  reflexivity.
Qed.

Definition app {A B} (f: list (A -> B)) x :=
  List.map (fun '(f, x) => f x) (f >*< x).

Infix "<*>" := app (at level 30).

Fixpoint generate (t: type): list term :=
  match t with
  | t_unit => [v_tt]
  | A * B =>
      [ fun v0 v1 => v_fanout v0 v1 ] <*> generate A <*> generate B
  end%list.

(* FIXME normalize *)
Function search (σ: Map.map term) E: list term :=
  match E with
  | E_var x => if Map.find x σ is Some v then [v] else []

  (* normalize ? *)
  | E_all x t E =>
      do v0 <- generate t ;
      do v1 <- search (Map.add x v0 σ) E ;
      [v_fanout v0 v1]

  | E_app E E' =>
      do f <- search σ E ;
      do x <- search σ E' ;
      if f is v_fanout a b
      then
        if eq_term x a
        then
          [b]
        else []
      else []

  | E_tt => [v_tt]
  | E_step E E' =>
      do p <- search σ E ;
      do x <- search σ E' ;
      if p is v_tt then [x] else []

  | E_fanout E E' =>
     do x <- search σ E ;
     do y <- search σ E' ;
     [v_fanout x y]

  | E_let x y E E' =>
      do tuple <- search σ E ;
      do ab <- (if tuple is v_fanout a b then [(a, b)] else []) ;
      search (Map.add x (fst ab) (Map.add y (snd ab) σ)) E'
  end%list.


Definition matches σ E v := List.existsb (fun y => if eq_term v y then true else false) (search σ E).

Lemma Forall_concat:
  forall {A} p (x: list (list A)), List.Forall (List.Forall p) x -> List.Forall p (List.concat x).
Proof using.
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

Lemma Forall_map:
  forall {A B} p (f: A -> B) x, List.Forall (fun x => p (f x)) x -> List.Forall p (List.map f x).
Proof using.
  all: intros ? ? ? ? ? p.
  induction p.
  1: constructor.
  cbn.
  constructor.
  1: auto.
  auto.
Qed.

Lemma Forall_concat':
  forall {A} p (x: list (list A)), List.Forall p (List.concat x) -> List.Forall (List.Forall p) x.
Proof using.
  intros ? ? x.
  induction x.
  all: intros.
  1: constructor.
  cbn in H.
  - constructor.
    2: apply IHx.
    + induction a.
      1: constructor.
      constructor.
      * cbn in H.
        inversion H.
        subst.
        auto.
      * cbn in H.
        inversion H.
        subst.
        apply IHa.
        auto.
    + induction a.
      1: auto.
      cbn in *.
      inversion H.
      subst.
      apply IHa.
      auto.
Qed.

Theorem Forall_flat_map:
  forall {A B} p (f: A -> list B) x, List.Forall (fun x => List.Forall p (f x)) x -> List.Forall p (List.flat_map f x).
Proof using.
  intros.
  rewrite List.flat_map_concat_map.
  apply Forall_concat.
  induction H.
  1:econstructor.
  econstructor.
  1: auto.
  auto.
Qed.

Theorem Forall_flat_map':
  forall {A B} p (f: A -> list B) x, List.Forall p (List.flat_map f x) -> List.Forall (fun x => List.Forall p (f x)) x.
Proof using.
  intros ? ? ? ? ?.
  induction x.
  1: constructor.
  intros q.
  rewrite List.flat_map_concat_map in q.
  set (q' := Forall_concat' _ _ q).
  cbn in q'.
  inversion q'.
  subst.
  constructor.
  1: auto.
  apply IHx.
  rewrite List.flat_map_concat_map.
  apply Forall_concat.
  auto.
Qed.

Theorem search_sound:
  forall σ E x, matches σ E x = true -> sat σ E x.
Proof using.
  admit.
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
  cbn.
  admit.
Admitted.
