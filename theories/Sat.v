Require Import Blech.Spec.
Require Blech.Map.
Require Import Blech.SpecNotations.

Require Blech.Context.
Require Blech.Term.

Require Coq.Lists.List.
Require Import Coq.Classes.SetoidClass.

Require Import FunInd.

Import IfNotations.

Definition eq_normal (x y: normal): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Fixpoint denote (σ: Map.map normal) (E: context) (v: normal) {struct E}: Prop :=
  match E, v with
  | E_var x, _ => if Map.find x σ is Some v' then v = v' else False

  | E_tt, N_tt => True

  | E_step E E', _ => denote σ E N_tt /\ denote σ E' v

  | E_fanout E E', N_fanout v v' => denote σ E v /\ denote σ E' v'

  | E_let x y E E', _ =>
      exists a b, denote σ E (N_fanout a b) /\ denote (Map.add y b (Map.add x a σ)) E' v

  | E_all x t E, N_fanout v v' => denote (Map.add x v σ) E v'
  | E_app E E', _ =>
      exists v', denote σ E (N_fanout v' v) /\ denote σ E' v'
  | _, _ => False
  end.

(* Lemma normal_big: *)
(*   forall v, *)
(*     is_term_norm_of_term v = true -> v ⇓ v. *)
(* Proof. *)
(*   intros v. *)
(*   induction v. *)
(*   all: cbn. *)
(*   all: try discriminate. *)
(*   all: intros p. *)
(*   - constructor. *)
(*   - constructor. *)
(*     + apply IHv1. *)
(*       destruct (is_term_norm_of_term v1). *)
(*       2: discriminate. *)
(*       reflexivity. *)
(*     + apply IHv2. *)
(*       destruct (is_term_norm_of_term v1), (is_term_norm_of_term v2). *)
(*       all: try discriminate. *)
(*       reflexivity. *)
(* Qed. *)

Theorem denote_sound:
  forall σ E v,
    denote σ E v -> sat σ E v.
Proof using.
  intros σ E.
  generalize dependent σ.
  induction E.
  all: cbn in *.
  all: intros σ v p.
  - destruct (Map.find x σ) eqn:q.
    2: contradiction.
    subst.
    constructor.
    all: auto.
  - destruct v.
    all: try contradiction.
    cbn in p.
    constructor.
    all: auto.
  - destruct p as [? [? ?]].
    econstructor.
    all: eauto.
  - destruct v.
    all: try contradiction.
    constructor.
  - destruct p.
    constructor.
    all: auto.
  - destruct v.
    all: try contradiction.
    destruct p.
    constructor.
    all: auto.
  - destruct p as [? [? [? ?]]].
    econstructor.
    all: eauto.
Qed.

Theorem denote_complete:
  forall σ E v, sat σ E v -> denote σ E v.
Proof using.
  intros ? ? ? q.
  induction q.
  all: cbn.
  all: auto.
  - rewrite H.
    reflexivity.
  - exists N0.
    exists N1.
    all: repeat split.
    all: auto.
  - exists N.
    all: repeat split.
    all: auto.
Qed.

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

Fixpoint generate (t: type): list normal :=
  match t with
  | t_unit => [N_tt]
  | A * B =>
      [ fun v0 v1 => N_fanout v0 v1 ] <*> generate A <*> generate B
  end%list.

(* FIXME normalize *)
Function search (σ: Map.map normal) E: list normal :=
  match E with
  | E_var x => if Map.find x σ is Some v then [v] else []

  (* normalize ? *)
  | E_all x t E =>
      do v0 <- generate t ;
      do v1 <- search (Map.add x v0 σ) E ;
      [N_fanout v0 v1]

  | E_app E E' =>
      do f <- search σ E ;
      do x <- search σ E' ;
      if f is N_fanout a b
      then
        if eq_normal x a
        then
          [b]
        else []
      else []

  | E_tt => [N_tt]
  | E_step E E' =>
      do p <- search σ E ;
      do x <- search σ E' ;
      if p is N_tt then [x] else []

  | E_fanout E E' =>
     do x <- search σ E ;
     do y <- search σ E' ;
     [N_fanout x y]

  | E_let x y E E' =>
      do tuple <- search σ E ;
      do ab <- (if tuple is N_fanout a b then [(a, b)] else []) ;
      search (Map.add x (fst ab) (Map.add y (snd ab) σ)) E'
  end%list.


Definition matches σ E v := List.existsb (fun y => if eq_normal v y then true else false) (search σ E).

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

Example conv E :=
  let x := 0 in
  let y := 1 in
  E_let x y E (E_fanout (E_var y) (E_var x)).
