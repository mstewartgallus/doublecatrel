Require Blech.Map.
Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Blech.OptionNotations.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import FunInd.

Import List.ListNotations.
Import IfNotations.

Implicit Type Δ: linear.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types X Y: cvar.
Implicit Type σ: store.

Import Map.MapNotations.

Section Typecheck.
  Import OptionNotations.

  Function typecheck Δ E: option (linear * type) :=
    match E with
    | E_var X =>
        do t ← Map.find X Δ ;
        Some (X ↦ t, t)
    | E_lam X t1 E =>
        do (Δ', t2) ← typecheck (X ↦ t1 ∪ Δ) E ;
        do t1' ← Map.find X Δ' ;
        if eq_type t1 t1'
        then
          Some (Δ' \ X, t1 * t2)
        else
          None
    | E_app E E' =>
        do (Δ', t1 * t2) ← typecheck Δ E ;
        do (Δ, t1') ← typecheck Δ E' ;
        if eq_type t1 t1'
        then
          Some (Δ' ∪ Δ, t2)
        else
          None

    | E_tt => Some (∅, t_unit)
    | E_step E E' =>
        do (Δ', t_unit) ← typecheck Δ E ;
        do (Δ, t) ← typecheck Δ E' ;
        Some (Δ' ∪ Δ, t)

    | E_fanout E E' =>
        do (Δ', t1) ← typecheck Δ E ;
        do (Δ, t2) ← typecheck Δ E' ;
        Some (Δ' ∪ Δ, t1 * t2)

    | E_let X Y E E' =>
        do (Δ', t1 * t2) ← typecheck Δ E ;
        do (Δ, t3) ← typecheck (X ↦ t1 ∪ Y ↦ t2 ∪ Δ) E' ;
        do t1' ← Map.find X (Δ \ Y) ;
        do t2' ← Map.find Y Δ ;
        if eq_type t1 t1'
        then
          if eq_type t2 t2'
          then
            Some (Δ' ∪ ((Δ \ Y) \ X), t3)
          else
            None
        else
          None
    end
      %list %map.
End Typecheck.

Notation "'do' x ← e0 ; e1" :=
  (List.flat_map (λ x, e1) e0)
    (x pattern, at level 200, left associativity): list_scope.

Fixpoint generate t :=
  match t with
  | t_unit => [N_tt]
  | t * t' =>
      do N ← generate t ;
      do N' ← generate t' ;
      [N_fanout N N']
  end%list.

Fixpoint search σ E: list span :=
  match E with
  | E_var X => if Map.find X σ is Some N then [X ↦ N |- N] else []

  | E_lam X t E =>
      do N0 ← generate t ;
      do (σ' |- N1) ← search (X ↦ N0 ∪ σ) E ;
      if Map.find X σ' is Some N0'
      then
        if eq_normal N0 N0'
        then
          [σ' \ X |- N_fanout N0 N1]
        else
          []
      else
        []

  | E_app E E' =>
      do (σ1 |- N) ← search σ E ;
      do (σ2 |- N0) ← search σ E' ;
      if N is N_fanout N0' N1
      then
        if eq_normal N0 N0'
        then
          [σ1 ∪ σ2 |- N1]
        else
          []
      else
        []

  | E_tt => [∅ |- N_tt]

  | E_step E E' =>
      do (σ1 |- N) ← search σ E ;
      do (σ2 |- N') ← search σ E' ;
      if N is N_tt
      then
        [σ1 ∪ σ2 |- N']
      else
        []

  | E_fanout E E' =>
      do (σ1 |- N) ← search σ E ;
      do (σ2 |- N') ← search σ E' ;
      [σ1 ∪ σ2 |- N_fanout N N']

  | E_let X Y E E' =>
      do (σ1 |- N) ← search σ E ;
      do (a, b) ← (if N is N_fanout a b then [(a, b)] else []) ;
      do (σ2 |- N') ← search ((X ↦ a) ∪ (Y ↦ b) ∪ σ) E' ;
      if Map.find X (σ2 \ Y) is Some a'
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
  end%list %map.

Theorem typecheck_sound:
  ∀ Δ {E Δ' t}, typecheck Δ E = Some (Δ', t) → Δ' ⊢ E ? t.
Proof using.
  intros Δ E.
  functional induction (typecheck Δ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
  - apply IHo.
    rewrite Map.add_minus.
    all: auto.
  - rewrite Map.add_minus.
    all: auto.
    1: rewrite Map.add_minus.
    all: auto.
Qed.

Lemma sound_pure:
  ∀ {σ E N}, sat σ E N → sound E ([σ |- N]%list).
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

Theorem search_sound:
  ∀ σ E, sound E (search σ E).
Proof using.
  Open Scope map.
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
    induction (IHE (X ↦ a ∪ σ)).
    1: constructor.
    cbn.
    destruct (Map.find X σ0) eqn:q.
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
    induction (IHE2 σ).
    1: constructor.
    cbn.
    destruct N.
    2: auto.
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
    induction (IHE2 (((X ↦ N1 ∪ Y ↦ N2) ∪ σ))).
    1: constructor.
    cbn.
    destruct (Map.find X (σ1 \ Y)) eqn:q.
    2: auto.
    destruct (eq_normal N1 n).
    2: auto.
    subst.
    destruct (Map.find Y σ1) eqn:q'.
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
  ∀ {σ E N}, List.In (σ |- N) (search σ E) → sat σ E N.
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
  (hexists (λ x1, .. (hexists (λ xn, H)) ..))
    (at level 39, x1 binder, H at level 50, right associativity,
      format "'[' '\exists' '/ ' x1 .. xn , '/ ' H ']'").

Definition ig {A} (P: hprop unit): hprop A := λ _, P tt.

Theorem hstar_assoc:
  ∀ {V} {A B C: hprop V},
    (A \* B) \* C = A \* (B \* C).
Proof using.
  admit.
Admitted.

(* Satisfaction defines a sort of nondeterministic Hoare logic *)

(* based on https://softwarefoundations.cis.upenn.edu/slf-current/Hprop.html *)
Inductive eval: context → store → normal → store → Prop :=
| eval_sat {E σ σ' N}: sat σ' E N → eval E σ N (Map.merge σ σ').

Definition hoare E (H: hprop unit) (Q: hprop normal): Prop :=
  ∀ s,
    H tt s →
    ∃ s' N, eval E s N s' /\ Q N s'.

Definition triple E H (Q: hprop normal) : Prop :=
  ∀ H', hoare E (H \* H') (Q \* ig H').

Definition oftype t := { E | Map.empty ⊢ E ? t }.

Definition equiv {t}: Relation_Definitions.relation (oftype t) :=
  λ a b,
    ∀ N,
      sat Map.empty (proj1_sig a) N ↔ sat Map.empty (proj1_sig b) N.

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


Import RelNotations.

#[program]
 Definition id t: oftype (t * t) :=
  let X: cvar := 0 in
   <{ λ X : t, X }>.

Next Obligation.
Proof.
  constructor.
  rewrite Map.merge_empty_r.
  constructor.
Qed.

#[program]
Definition conv {t t'} (E: oftype (t * t')): oftype (t' * t) :=
  let X: cvar := 0 in
  let Y: cvar := 1 in
  <{ let (X, Y) := E in (Y, X) }>.

Next Obligation.
Proof.
  destruct E.
  cbn.
  rewrite <- (@Map.merge_empty_l _ Map.empty).
  econstructor.
  all: eauto.
  constructor.
  - constructor.
  - rewrite Map.merge_empty_r.
    constructor.
Qed.

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
    inversion H2.
    subst.
    inversion H6.
    subst.
    rewrite H.
    constructor.
    rewrite Map.merge_empty_r.
    admit.
  - intros p.
    inversion p.
    subst.
    inversion H4.
    subst.
    rewrite <- (@Map.merge_empty_l _ Map.empty).
    econstructor.
    all: eauto.
    rewrite <- H0.
    rewrite Map.merge_empty_r in H0.
    destruct (Map.one_inj H0).
    subst.
    constructor.
    + constructor.
    + constructor.
Admitted.
