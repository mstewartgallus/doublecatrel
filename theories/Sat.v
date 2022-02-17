Require Import Blech.Spec.
Require Blech.Map.
Require Import Blech.SpecNotations.

Require Blech.Context.
Require Blech.Term.

Require Coq.Lists.List.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Program.Tactics.

Require Import FunInd.

Import IfNotations.

Definition eq_normal (x y: normal): {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.
Import List.ListNotations.

Notation "'do' x <- e0 ; e1" := (List.flat_map (fun x => e1) e0) (x pattern, at level 200, left associativity).

Fixpoint mon {A B} (x: list A) (y: list B): list _ :=
  match x with
  | cons H T => List.map (pair H) y ++ mon T y
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


Fixpoint app {A B} (f: list (A -> B)) x: list _ :=
  if f is cons H T
  then
    List.app (List.map H x) (app T x)
  else
    nil%list.

Infix "<*>" := app (at level 30).

Lemma map_map {A B C} (f: B -> C) (g: A -> B) x:
  List.map f (List.map g x) = List.map (fun x => f (g x)) x.
Proof.
  induction x.
  1: reflexivity.
  cbn.
  rewrite IHx.
  reflexivity.
Qed.

Lemma map_app {A B} (f: A -> B) x y:
  (List.map f (x ++ y) = List.map f x ++ List.map f y)%list.
Proof.
  induction x.
  1: reflexivity.
  cbn.
  rewrite IHx.
  reflexivity.
Qed.

Lemma map_mon {A B} (f: list (A -> B)) x:
  f <*> x = List.map (fun '(f, x) => f x) (f >*< x).
Proof.
  induction f.
  1: reflexivity.
  cbn in *.
  repeat rewrite map_app.
  repeat rewrite map_map.
  rewrite <- IHf.
  clear.
  reflexivity.
Qed.

Lemma app_as_flat_map {A B} (f: list (A -> B)) x:
  f <*> x = List.flat_map (fun f' => List.map f' x) f.
Proof.
  induction f.
  1: reflexivity.
  cbn.
  rewrite IHf.
  cbn.
  reflexivity.
Qed.

Fixpoint generate (t: type): list normal :=
  match t with
  | t_unit => [N_tt]
  | A * B => [N_fanout] <*> generate A <*> generate B
  end%list.

Fixpoint pick (σ: Map.map normal) E: list span :=
  match E with
  | E_var x => if Map.find x σ is Some N then [Map.one x N |- N] else []

  | E_lam x t E =>
      do N0 <- generate t ;
      do (σ' |- N1) <- pick (Map.add x N0 σ) E ;
      if Map.find x σ' is Some N0'
      then
        if eq_normal N0 N0'
        then
          [Map.minus x σ' |- N_fanout N0 N1]
        else
          []
      else
        []

  | E_app E E' =>
      do (σ1 |- N) <- pick σ E ;
      do (σ2 |- N0) <- pick σ E' ;
      if N is N_fanout N0' N1
      then
        if eq_normal N0 N0'
        then
          [Map.merge σ1 σ2 |- N1]
        else
          []
      else
        []

  | E_tt => [Map.empty |- N_tt]

  | E_step E E' =>
      do (σ1 |- N) <- pick σ E ;
      if N is N_tt
      then
        [fun '(σ2 |- N') => Map.merge σ1 σ2 |- N'] <*> pick σ E'
      else
        []

  | E_fanout E E' =>
      [fun '(σ1 |- N) '(σ2 |- N') => Map.merge σ1 σ2 |- N_fanout N N'] <*> pick σ E <*> pick σ E'

  | E_let x y E E' =>
      do (σ1 |- N) <- pick σ E ;
      do (a, b) <- (if N is N_fanout a b then [(a, b)] else []) ;
      do (σ2 |- N') <- pick (Map.add x a (Map.add y b σ)) E' ;
      if Map.find x (Map.minus y σ2)is Some a'
      then
        if eq_normal a a'
        then
          if Map.find y σ2 is Some b'
          then
            if eq_normal b b'
            then
              [Map.merge σ1 (Map.minus x (Map.minus y σ2)) |- N']
            else
              []
          else
            []
        else
          []
      else
        []
  end%list.

Lemma sound_pure {E p}: sat E p -> sound E ([p]%list).
Proof.
  intro.
  constructor.
  1: constructor.
  auto.
Defined.

Lemma sound_mon {E p p'}:
  sound E p -> sound E p' ->
  sound E ((p ++ p')%list).
Proof.
  intros.
  induction p.
  1: auto.
  cbn.
  inversion H.
  constructor.
  all: auto.
Defined.

Theorem search_sound:
  forall σ E, sound E (pick σ E).
Proof using.
  intros σ E.
  generalize dependent σ.
  induction E.
  all: intros.
  - cbn.
    destruct (Map.find x σ) eqn:q.
    2: constructor.
    apply sound_pure.
    constructor.
  - cbn.
    induction (generate t).
    1: cbn.
    1: constructor.
    cbn in *.
    apply sound_mon.
    2: auto.
    clear IHl.
    induction (IHE (Map.add x a σ)).
    1: constructor.
    cbn.
    destruct P.
    cbn in *.
    destruct (Map.find x D) eqn:q.
    2: auto.
    destruct (eq_normal a n).
    2: auto.
    subst.
    constructor.
    1: auto.
    constructor.
    rewrite Map.add_minus.
    all: auto.
  - cbn.
    induction (IHE1 σ).
    1: constructor.
    cbn.
    destruct P.
    apply sound_mon.
    2: auto.
    clear IHs.
    induction (IHE2 σ).
    1: constructor.
    cbn in *.
    destruct P.
    destruct N.
    1: auto.
    destruct (eq_normal N0 N1).
    2: cbn.
    2: auto.
    cbn.
    subst.
    constructor.
    1: auto.
    econstructor.
    all: eauto.
  - all: repeat constructor.
  - cbn.
    induction (IHE1 σ).
    1: constructor.
    cbn.
    destruct P.
    cbn in *.
    apply sound_mon.
    2: auto.
    clear IHs.
    destruct N.
    2: constructor.
    induction (IHE2 σ).
    1: constructor.
    cbn.
    destruct P.
    cbn in *.
    rewrite List.app_nil_r in *.
    constructor.
    1: auto.
    clear IHs0.
    constructor.
    all: auto.
  - cbn.
    induction (IHE1 σ).
    1: constructor.
    cbn.
    destruct P.
    cbn in *.
    apply sound_mon.
    2: auto.
    clear IHs.
    induction (IHE2 σ).
    1: constructor.
    cbn.
    destruct P.
    cbn in *.
    constructor.
    1: auto.
    econstructor.
    all: eauto.
  - cbn.
    induction (IHE1 σ).
    1: constructor.
    destruct P.
    apply sound_mon.
    2: auto.
    clear IHs.
    destruct N.
    1: constructor.
    cbn.
    rewrite List.app_nil_r.
    induction (IHE2 (Map.add x N1 (Map.add y N2 σ))).
    1: constructor.
    cbn.
    destruct P.
    destruct (Map.find x (Map.minus y D0)) eqn:q.
    2: auto.
    cbn in q.
    rewrite q.
    destruct (eq_normal N1 n).
    2: auto.
    subst.
    destruct (Map.find y D0) eqn:q'.
    destruct (eq_normal N2 n0).
    2: auto.
    subst.
    cbn.
    constructor.
    1: auto.
    econstructor.
    all: eauto.
    all: repeat rewrite Map.add_minus.
    all: eauto.
    all: cbn.
    cbn in q.
    rewrite q.
    cbn.
    auto.
Qed.

Example id t :=
  let x := 0 in
  E_lam x t (E_var x).

Example conv E :=
  let x := 0 in
  let y := 1 in
  E_let x y E (E_fanout (E_var y) (E_var x)).
