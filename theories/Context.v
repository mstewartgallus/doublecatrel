Require Import Blech.Spec.
Require Blech.Map.
Require Import Blech.SpecNotations.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import FunInd.

Import Map.MapNotations.
Import List.ListNotations.
Import IfNotations.

Implicit Type Δ: linear.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types X Y: cvar.
Implicit Type σ: store.

Function typecheck Δ E: option (linear * type) :=
  match E with
  | E_var X =>
      if Map.find X Δ is Some t
      then
          Some (Map.one X t, t)
      else
        None
  | E_lam X t1 E =>
      if typecheck (Map.add X t1 Δ) E is Some (Δ', t2)
      then
        if Map.find X Δ' is Some t1'
        then
          if eq_type t1 t1'
          then
              Some (Δ' \ X, t1 * t2)
          else
            None
        else
          None
      else
        None
  | E_app E E' =>
      if typecheck Δ E is Some (Δ', t1 * t2)
      then
        if typecheck Δ E' is Some (Δ, t1')
        then
          if eq_type t1 t1'
          then
            Some (Δ' ∪ Δ, t2)
          else
            None
        else
          None
      else
        None

  | E_tt => Some (Map.empty, t_unit)
  | E_step E E' =>
      if typecheck Δ E is Some (Δ', t_unit)
      then
        if typecheck Δ E' is Some (Δ, t)
        then
          Some (Δ' ∪ Δ, t)
        else
          None
      else
        None

  | E_fanout E E' =>
      if typecheck Δ E is Some (Δ', t1)
      then
        if typecheck Δ E' is Some (Δ, t2)
        then
          Some (Δ' ∪ Δ, t_prod t1 t2)
        else
          None
      else
        None

  | E_let X Y E E' =>
      if typecheck Δ E is Some (Δ', t1 * t2)
      then
        if typecheck (Map.add X t1 (Map.add Y t2 Δ)) E' is Some (Δ, t3)
        then
          if Map.find X (Δ \ Y) is Some t1'
          then
            if eq_type t1 t1'
            then
              if Map.find Y Δ is Some t2'
              then
                if eq_type t2 t2'
                then
                  Some (Δ' ∪ ((Δ \ Y) \ X), t3)
                else
                  None
              else
                None
            else
              None
          else
            None
        else
          None
      else
        None
  end
    %list.

Theorem typecheck_sound:
  ∀ Δ {E Δ' t}, typecheck Δ E = Some (Δ', t) → Δ' ⊢ E ? t.
Proof using.
  intros Δ E.
  functional induction (typecheck Δ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
  - apply IHo.
    rewrite (Map.add_minus X t1 Δ').
    2: auto.
    auto.
  - rewrite Map.add_minus.
    all: auto.
    1: rewrite Map.add_minus.
    all: auto.
Qed.

Notation "'do' x <- e0 ; e1" := (List.flat_map (fun x => e1) e0) (x pattern, at level 200, left associativity).

Fixpoint app {A B} (f: list (A → B)) x: list _ :=
  if f is cons H T
  then
    List.app (List.map H x) (app T x)
  else
    nil%list.

Infix "<*>" := app (at level 30).

Fixpoint generate t :=
  match t with
  | t_unit => [N_tt]
  | A * B => [N_fanout] <*> generate A <*> generate B
  end%list.

Fixpoint search σ E: list span :=
  match E with
  | E_var X => if Map.find X σ is Some N then [Map.one X N |- N] else []

  | E_lam X t E =>
      do N0 <- generate t ;
      do (σ' |- N1) <- search (Map.add X N0 σ) E ;
      if Map.find X σ' is Some N0'
      then
        if eq_normal N0 N0'
        then
          [Map.minus X σ' |- N_fanout N0 N1]
        else
          []
      else
        []

  | E_app E E' =>
      do (σ1 |- N) <- search σ E ;
      do (σ2 |- N0) <- search σ E' ;
      if N is N_fanout N0' N1
      then
        if eq_normal N0 N0'
        then
          [(σ1 ∪ σ2) |- N1]
        else
          []
      else
        []

  | E_tt => [Map.empty |- N_tt]

  | E_step E E' =>
      do (σ1 |- N) <- search σ E ;
      if N is N_tt
      then
        [fun '(σ2 |- N') => (σ1 ∪ σ2) |- N'] <*> search σ E'
      else
        []

  | E_fanout E E' =>
      [fun '(σ1 |- N) '(σ2 |- N') => (σ1 ∪ σ2) |- N_fanout N N'] <*> search σ E <*> search σ E'

  | E_let X Y E E' =>
      do (σ1 |- N) <- search σ E ;
      do (a, b) <- (if N is N_fanout a b then [(a, b)] else []) ;
      do (σ2 |- N') <- search (Map.add X a (Map.add Y b σ)) E' ;
      if Map.find X (Map.minus Y σ2)is Some a'
      then
        if eq_normal a a'
        then
          if Map.find Y σ2 is Some b'
          then
            if eq_normal b b'
            then
              [σ1 ∪ ((σ2 \ Y) \ X) |- N']
            else
              []
          else
            []
        else
          []
      else
        []
  end%list.

Lemma sound_pure:
  ∀ {E S N}, sat E S N → sound E ([S |- N]%list).
Proof.
  repeat constructor.
  auto.
Defined.

Lemma sound_mon {E p p'}:
  sound E p → sound E p' →
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

Lemma sound_fst {E p p'}:
  sound E ((p ++ p')%list) →
  sound E p.
Proof.
  intros.
  induction p.
  1: constructor.
  destruct a.
  cbn in H.
  inversion H.
  subst.
  constructor.
  all: auto.
Defined.

Lemma sound_snd {E p p'}:
  sound E ((p ++ p')%list) →
  sound E p'.
Proof.
  intros.
  induction p.
  1: auto.
  destruct a.
  cbn in H.
  inversion H.
  subst.
  auto.
Defined.

Lemma sound_split {E p p'}:
  sound E ((p ++ p')%list) → sound E p * sound E p'.
Proof.
  intros.
  refine (sound_fst _, sound_snd _).
  all:eauto.
Defined.

Theorem search_sound:
  ∀ σ E, sound E (search σ E).
Proof using.
  intros σ E.
  generalize dependent σ.
  induction E.
  all: intros.
  - cbn.
    destruct (Map.find X σ) eqn:q.
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
    induction (IHE (Map.add X a σ)).
    1: constructor.
    cbn.
    destruct (Map.find X S) eqn:q.
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
    apply sound_mon.
    2: auto.
    clear IHs.
    induction (IHE2 σ).
    1: constructor.
    cbn in *.
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
    apply sound_mon.
    2: auto.
    clear IHs.
    destruct N.
    2: constructor.
    induction (IHE2 σ).
    1: constructor.
    cbn.
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
    apply sound_mon.
    2: auto.
    clear IHs.
    induction (IHE2 σ).
    1: constructor.
    cbn.
    constructor.
    1: auto.
    econstructor.
    all: eauto.
  - cbn.
    induction (IHE1 σ).
    1: constructor.
    apply sound_mon.
    2: auto.
    clear IHs.
    destruct N.
    1: constructor.
    cbn.
    rewrite List.app_nil_r.
    induction (IHE2 (Map.add X N1 (Map.add Y N2 σ))).
    1: constructor.
    cbn.
    destruct (Map.find X (Map.minus Y S0)) eqn:q.
    2: auto.
    destruct (eq_normal N1 n).
    2: auto.
    subst.
    destruct (Map.find Y S0) eqn:q'.
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
Qed.

Theorem search_sound_sat:
  ∀ σ E N, List.In (σ |- N) (search σ E) → sat E σ N.
Proof using.
  intros σ E.
  induction (search_sound σ E).
  all: cbn.
  1: contradiction.
  intros N' p.
  destruct p.
  2: auto.
  inversion H0.
  subst.
  auto.
Defined.

(* FIXME put elsewhere/make a monad? *)
Section Heap.
  Context {A: Type}.

  Definition hprop := A → store → Prop.

  Inductive hempty: hprop :=
  | hempty_intro {a}: hempty a Map.empty.

  Inductive hpure P: hprop :=
  | hpure_intro {a}: P → hpure P a Map.empty.

  Inductive hsingle X N: hprop :=
  | hsingle_intro {a}: hsingle X N a (Map.one X N).

  Inductive hstar (H H': hprop): hprop :=
  | hstar_intro {a h1 h2}:
    H a h1 → H' a h2 → Map.disjoint h1 h2 →
    hstar H H' a (Map.merge h1 h2).
  Inductive hexists {A} (J: A → hprop): hprop :=
  | hexists_intro {x a h}: J x a h → hexists J a h.
End Heap.

Arguments hprop: clear implicits.

Notation "\[]" := hempty (at level 0).
Notation "\[ P ]" := (hpure P) (at level 0, format "\[ P ]").
Notation "p '~~>' v" := (hsingle p v) (at level 32).
Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
    (at level 39, x1 binder, H at level 50, right associativity,
      format "'[' '\exists' '/ ' x1 .. xn , '/ ' H ']'").

Definition ig {A} (P: hprop unit): hprop A := fun _ => P tt.

Theorem hstar_assoc:
  ∀ {V} {A B C: hprop V},
    (A \* B) \* C = A \* (B \* C).
Proof using.
  intros ? A B C.
  extensionality v.
  extensionality p.
  apply propositional_extensionality.
  split.
  - intro pred.
    destruct pred.
    destruct H.
    rewrite Map.merge_assoc.
    eexists.
    2: eexists.
    all: eauto.
    + intro n.
      unfold Map.disjoint in *.
      unfold Map.merge in *.
      unfold Map.find in *.
      destruct (H3 n).
      all: auto.
      destruct (H1 n).
      all: auto.
      destruct (h1 n).
      all: try discriminate.
      destruct (h0 n).
      all: try discriminate.
      auto.
    + intro n.
      unfold Map.disjoint in *.
      unfold Map.merge in *.
      unfold Map.find in *.
      destruct (H3 n).
      all: auto.
      destruct (H1 n).
      all: auto.
      destruct (h1 n).
      all: try discriminate.
      destruct (h0 n).
      all: try discriminate.
      auto.
      rewrite H4.
      rewrite H5.
      auto.
  - intro pred.
    destruct pred.
    destruct H0.
    rewrite <- Map.merge_assoc.
    eexists.
    1: eexists.
    all: eauto.
    + intro n.
      unfold Map.disjoint in *.
      unfold Map.merge in *.
      unfold Map.find in *.
      destruct (H3 n).
      all: auto.
      destruct (H1 n).
      all: auto.
      destruct (h1 n).
      all: try discriminate.
      destruct (h0 n).
      all: try discriminate.
      all: auto.
    + intro n.
      unfold Map.disjoint in *.
      unfold Map.merge in *.
      unfold Map.find in *.
      destruct (H3 n).
      all: auto.
      destruct (H1 n).
      all: auto.
      destruct (h1 n).
      all: try discriminate.
      destruct (h0 n).
      all: try discriminate.
      auto.
      rewrite H4.
      rewrite H4 in H5.
      rewrite H5.
      auto.
Qed.

(* Satisfaction defines a sort of nondeterministic Hoare logic *)

(* based on https://softwarefoundations.cis.upenn.edu/slf-current/Hprop.html *)
Inductive eval: context → store → normal → store → Prop :=
| eval_sat {E σ σ' N}: sat E σ' N → eval E σ N (Map.merge σ σ').

Definition hoare E (H: hprop unit) (Q: hprop normal): Prop :=
  ∀ s,
    H tt s →
    exists s' N, eval E s N s' /\ Q N s'.

Definition triple E H (Q: hprop normal) : Prop :=
  ∀ H', hoare E (H \* H') (Q \* ig H').

Definition oftype t := { E | Map.empty ⊢ E ? t }.

Definition equiv {t}: Relation_Definitions.relation (oftype t) :=
  fun a b =>
    ∀ N,
      sat (proj1_sig a) Map.empty N ↔ sat (proj1_sig b) Map.empty N.

Instance equiv_Reflexive t: Reflexive (@equiv t).
Proof using.
  unfold equiv.
  unfold Reflexive.
  intros.
  reflexivity.
Qed.

Instance equiv_Symmetric t: Symmetric (@equiv t).
Proof using.
  unfold equiv.
  unfold Symmetric.
  intros.
  symmetry.
  auto.
Qed.

Instance equiv_Transitive t: Transitive (@equiv t).
Proof using.
  unfold equiv.
  unfold Transitive.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Instance equiv_Equivalence t: Equivalence (@equiv t) := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid t: Setoid (oftype t) := {
    equiv := equiv ;
}.


#[program]
Definition id t: oftype (t * t) :=
  let X := 0 in
  E_lam X t (E_var X).

Next Obligation.
Proof.
  apply (@typecheck_sound Map.empty).
  cbn.
  unfold Map.one.
  destruct (eq_type t t).
  2: contradiction.
  admit.
Admitted.

#[program]
Definition conv {t t'} (E: oftype (t * t')): oftype (t' * t) :=
  let X := 0 in
  let Y := 1 in
  E_let X Y E (E_fanout (E_var Y) (E_var X)).

Next Obligation.
Proof.
  destruct E.
  cbn.
  rewrite <- (@Map.merge_empty_l _ Map.empty).
  econstructor.
  all: eauto.
  apply (@typecheck_sound (Map.add 1 t' (Map.add 0 t Map.empty))).
  cbn.
  admit.
Admitted.

Lemma conv_id t:
  conv (id t) == id t.
Proof.
  unfold conv, id.
  cbn.
  unfold equiv.
  cbn.
  intros.
  split.
  - intros p.
    inversion p.
    subst.
    inversion H5.
    subst.
    inversion H3.
    subst.
    inversion H6.
    subst.
    constructor.
    cbn.
    admit.
  - intros p.
    inversion p.
    subst.
    inversion H4.
    subst.
    rewrite <- (@Map.merge_empty_l _ Map.empty).
    econstructor.
    all: eauto.
    admit.
Admitted.
