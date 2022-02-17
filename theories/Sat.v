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

Function denote (σ: Map.map normal) (v: normal) (E: context) {struct E}: Prop :=
  match E, v with
  | E_var x, _ => σ = Map.one x v

  | E_tt, N_tt => σ = Map.empty

  | E_step E E', _ =>
      exists a b,
      σ = Map.merge a b /\ denote a N_tt E /\ denote b v E'

  | E_fanout E E', N_fanout v v' =>
      exists a b,
      σ = Map.merge a b /\ denote a v E /\ denote b v' E'

  | E_let x y E E', _ =>
      exists l r a b,
      σ = Map.merge l r /\ denote l (N_fanout a b) E /\ denote (Map.add y b (Map.add x a r)) v E'

  | E_lam x t E, N_fanout v v' => denote (Map.add x v σ) v' E
  | E_app E E', _ =>
      exists v' a b,
      σ = Map.merge a b /\ denote a (N_fanout v' v) E /\ denote b v' E'
  | _, _ => False
  end.

Theorem denote_complete:
  forall c σ E v, sat σ c E v -> denote σ v E.
Proof using.
  intros c.
  induction c.
  all: intros σ E v q.
  all: inversion q.
  all: subst.
  all: cbn.
  all: auto.
  - exists N.
    exists D.
    exists D'.
    all: repeat (split; auto).
  - exists D.
    exists D'.
    all: repeat (split; auto).
  - exists D.
    exists D'.
    all: repeat (split; auto).
  - exists D.
    exists D'.
    exists N0.
    exists N1.
    all: repeat (split; auto).
Qed.

Theorem denote_sound:
  forall σ E v,
    denote σ v E -> exists c, sat σ c E v.
Proof using.
  intros σ E.
  generalize dependent σ.
  induction E.
  all: cbn in *.
  all: intros σ v p.
  - subst.
    eexists.
    econstructor.
  - destruct v.
    all: try contradiction.
    cbn in p.
    destruct (IHE _ _ p).
    eexists.
    constructor.
    eauto.
  - destruct_conjs.
    destruct (IHE1 _ _ H2).
    destruct (IHE2 _ _ H3).
    subst.
    eexists.
    econstructor.
    all: eauto.
  - destruct v.
    all: try contradiction.
    subst.
    eexists.
    constructor.
  - destruct_conjs.
    subst.
    destruct (IHE1 _ _ H1).
    destruct (IHE2 _ _ H2).
    eexists.
    constructor.
    all: eauto.
  - destruct v.
    all: try contradiction.
    destruct_conjs.
    subst.
    destruct (IHE1 _ _ H1).
    destruct (IHE2 _ _ H2).
    eexists.
    constructor.
    all: eauto.
  - destruct_conjs.
    subst.
    destruct (IHE1 _ _ H3).
    destruct (IHE2 _ _ H4).
    eexists (c_let x y x0 x1).
    econstructor.
    all: eauto.
Qed.

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

Fixpoint generate (t: type): list normal :=
  match t with
  | t_unit => [N_tt]
  | A * B => [N_fanout] <*> generate A <*> generate B
  end%list.

Fixpoint sub c: option (Map.map normal * context * normal) :=
  match c with
  | c_var x N => Some (Map.one x N, E_var x, N)
  | c_lam x t c =>
      if sub c is Some (σ, E, N')
      then
        if Map.find x σ is Some N
        then
          Some (Map.minus x σ, E_lam x t E, N_fanout N N')
        else
          None
      else
        None

  | c_app c c' =>
      if sub c is Some (σ, E, N_fanout N0 N1)
      then
        if sub c' is Some (σ', E', N0')
        then
          if eq_normal N0 N0'
          then
            Some (Map.merge σ σ', E_app E E', N1)
          else
            None
        else
          None
      else
        None

  | c_tt => Some (Map.empty, E_tt, N_tt)
  | c_step c c' =>
      if sub c is Some (σ, E, N_tt)
      then
        if sub c' is Some (σ', E', N)
        then
          Some (Map.merge σ σ', E_step E E', N)
        else
          None
      else
        None

  | c_fanout c c' =>
      if sub c is Some (σ, E, N)
      then
        if sub c' is Some (σ', E', N')
        then
          Some (Map.merge σ σ', E_fanout E E', N_fanout N N')
        else
          None
      else
        None

  | c_let x y c c' =>
      if sub c is Some (σ, E, N_fanout N N')
      then
        if sub c' is Some (σ', E', N2)
        then
          Some (Map.merge σ (Map.minus y (Map.minus x σ')), E_let x y E E', N2)
        else
          None
      else
        None
  end%list.

Fixpoint search (σ: Map.map normal) E: list command :=
  match E with
  | E_var x => if Map.find x σ is Some N then [c_var x N] else []

  | E_lam x t E =>
      do v0 <- generate t ;
      [c_lam x t] <*> search (Map.add x v0 σ) E

  | E_app E E' =>
      [c_app] <*> search σ E <*> search σ E'

  | E_tt => [c_tt]

  | E_step E E' =>
      [c_step] <*> search σ E <*> search σ E'

  | E_fanout E E' =>
      [c_fanout] <*> search σ E <*> search σ E'

  | E_let x y E E' =>
      do c <- search σ E ;
      do (a, b) <- (if sub c is Some (_, _, N_fanout a b) then [(a, b)] else []) ;
      [c_let x y c] <*> search (Map.add x a (Map.add y b σ)) E'
  end%list.

(* Fixpoint search (σ: Map.map normal) E: list (Map.map normal * normal) := *)
(*   match E with *)
(*   | E_var x => if Map.find x σ is Some v then [(Map.one x v, v)] else [] *)

(*   | E_lam x t E => *)
(*       do v0 <- generate t ; *)
(*       do (σ', v1) <- search (Map.add x v0 σ) E ; *)
(*       if Map.find x σ' is Some v0' *)
(*       then *)
(*         if eq_normal v0 v0' *)
(*         then *)
(*           [(Map.minus x σ', N_fanout v0 v1)] *)
(*         else *)
(*           [] *)
(*       else *)
(*         [] *)

(*   | E_app E E' => *)
(*       do (σ1, f) <- search σ E ; *)
(*       do (σ2, x) <- search σ E' ; *)
(*       if f is N_fanout a b *)
(*       then *)
(*         if eq_normal x a *)
(*         then *)
(*           [(Map.merge σ1 σ2, b)] *)
(*         else [] *)
(*       else [] *)

(*   | E_tt => [(Map.empty, N_tt)] *)

(*   | E_step E E' => *)
(*       do (σ1, p) <- search σ E ; *)
(*       do (σ2, x) <- search σ E' ; *)
(*       if p is N_tt then [(Map.merge σ1 σ2, x)] else [] *)

(*   | E_fanout E E' => *)
(*       do (σ1, v1) <- search σ E ; *)
(*       do (σ2, v2) <- search σ E' ; *)
(*       [(Map.merge σ1 σ2, N_fanout v1 v2)] *)

(*   | E_let x y E E' => *)
(*       do (σ1, tuple) <- search σ E ; *)
(*       do (a, b) <- (if tuple is N_fanout a b then [(a, b)] else []) ; *)
(*       do (σ2, v) <- search (Map.add x a (Map.add y b σ)) E' ; *)
(*       [(Map.merge σ1 σ2, v)] *)
(*   end%list. *)

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
  forall σ E, List.Forall (fun c =>
                             if sub c is Some (σ, E, v)
                             then
                               sat σ c E v
                             else
                               True) (search σ E).
Proof using.
  intros σ E.
  generalize dependent σ.
  induction E.
  all: cbn.
  all: intros.
  - destruct (Map.find x σ) eqn:q.
    2: constructor.
    constructor.
    2: constructor.
    cbn.
    constructor.
  - apply Forall_flat_map.
    induction (generate t).
    1: constructor.
    constructor.
    2: auto.
    repeat rewrite List.app_nil_r in *.
    induction (IHE (Map.add x a σ)).
    1: constructor.
    constructor.
    2: auto.
    cbn.
    destruct (sub x0) eqn:q.
    2: auto.
    destruct p.
    destruct p.
    destruct (Map.find x m) eqn:q'.
    constructor.
    rewrite Map.add_minus.
    auto.
    auto.
    auto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Example id t :=
  let x := 0 in
  E_lam x t (E_var x).

Example conv E :=
  let x := 0 in
  let y := 1 in
  E_let x y E (E_fanout (E_var y) (E_var x)).
