Require Blech.Map.
Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Blech.OptionNotations.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Coq.Lists.List.
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
  ∀ Δ {E Δ' t}, typecheck Δ E = Some (Δ', t) → JE (l_with Δ' E) t.
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

Variant occur := z | o | m.

Definition add e0 e1 :=
  match e0, e1 with
  | z, m => m
  | o, m => m
  | m, m => m
  | m, o => m
  | m, z => m

  | o, z => o
  | o, o => m
  | z, o => o

  | z, z => z
  end.

Infix "+" := add.

Function count X E :=
  match E with
  | E_var Y => if eq_cvar X Y then o else z

  | E_lam Y t E =>
      if eq_cvar X Y then z else count X E

  | E_app E E' => count X E + count X E'

  | E_tt => z

  | E_step E E' => count X E + count X E'

  | E_fanout E E' => count X E + count X E'

  | E_let Y Y' E E' =>
      if eq_cvar X Y
      then
        count X E
      else
        if eq_cvar X Y'
        then
          count X E
        else
          count X E + count X E'
  end.

(* Import Blech.OptionNotations. *)

Inductive result := one (c: context) | zero | many.

Function subst (S: context) (X: cvar) (E: context): result :=
  match E with
  | E_var Y => if eq_cvar X Y then one S else zero
  | E_lam Y t E =>
      if eq_cvar X Y
      then
        zero
      else
        match subst S X E with
        | one E' => one (E_lam Y t E')
        | p => p
        end

  | E_app E0 E1 =>
      match subst S X E0, subst S X E1 with
      | one E0', zero => one (E_app E0' E1)
      | zero, one E1' => one (E_app E0 E1')

      | zero, zero => zero
      | _, _ => many
      end

  | E_tt => zero

  | E_step E0 E1 =>
      match subst S X E0, subst S X E1 with
      | one E0', zero => one (E_step E0' E1)
      | zero, one E1' => one (E_step E0 E1')

      | zero, zero => zero
      | _, _ => many
      end

  | E_fanout E0 E1 =>
      match subst S X E0, subst S X E1 with
      | one E0', zero => one (E_fanout E0' E1)
      | zero, one E1' => one (E_fanout E0 E1')

      | zero, zero => zero
      | _, _ => many
      end

  | E_let Y Y' E0 E1 =>
      if eq_cvar X Y
      then
        match subst S X E0 with
        | one E0' => one (E_let Y Y' E0' E1)
        | p => p
        end
      else
        if eq_cvar X Y'
        then
          match subst S X E0 with
          | one E0' => one (E_let Y Y' E0' E1)
          | p => p
          end
        else
          match subst S X E0, subst S X E1 with
          | one E0', zero => one (E_let Y Y' E0' E1)
          | zero, one E1' => one (E_let Y Y' E0 E1')

          | zero, zero => zero
          | _, _ => many
          end

  end.

Lemma subst_id {E X E'}:
  count X E' = z → subst_context E X E' = E'.
Proof.
  functional induction (count X E').
  all: cbn.
  all: intros p.
  all: try destruct eq_cvar.
  all: subst.
  all: try discriminate.
  all: try destruct eq_cvar.
  all: subst.
  all: try contradiction.
  all: auto.
  all: try rewrite IHo0.
  all: try rewrite IHo1.
  all: auto.
  all: try destruct (count X E1), (count X E').
  all: try discriminate.
  all: cbn in p.
  all: auto.
  all: try destruct eq_cvar.
  all: subst.
  all: auto.
  all: try destruct eq_cvar.
  all: auto.
Qed.

Lemma subst_count {E X E'}:
  count X E' = match subst E X E' with
               | zero => z
               | one _ => o
               | many => m
               end.
Proof.
  functional induction (subst E X E').
  all: cbn.
  all: try destruct eq_cvar.
  all: auto.
  all: try discriminate.
  all: try contradiction.
  all: try rewrite IHr.
  all: try rewrite IHr0.
  all: try rewrite e0.
  all: try rewrite e1.
  all: auto.
  all: try destruct (subst E X E1), (subst E X E2).
  all: cbn.
  all: auto.
  all: try discriminate.
  all: try contradiction.
Qed.

Lemma linear {E X E'}:
  subst E X E' =
    match count X E' with
    | z => zero
    | o => one (subst_context E X E')
    | m => many
    end.
Proof.
  induction E'.
  all: cbn.
  all: try destruct eq_cvar.
  all: try destruct eq_cvar.
  all: subst.
  all: try contradiction.
  all: try discriminate.
  all: auto.
  - rewrite IHE'.
    destruct (count X E').
    all: auto.
  - destruct (count X E'1), (count X E'2).
    all: cbn.
    all: try rewrite IHE'1.
    all: try rewrite IHE'2.
    all: auto.
    + rewrite (@subst_id _ _ E'1) .
      2: erewrite subst_count.
      2: rewrite IHE'1.
      2: auto.
      auto.
    + rewrite (@subst_id _ _ E'2) .
      2: erewrite subst_count.
      2: rewrite IHE'2.
      2: auto.
      auto.
  - destruct (count X E'1), (count X E'2).
    all: cbn.
    all: try rewrite IHE'1.
    all: try rewrite IHE'2.
    all: auto.
    + rewrite (@subst_id _ _ E'1) .
      2: erewrite subst_count.
      2: rewrite IHE'1.
      2: auto.
      auto.
    + rewrite (@subst_id _ _ E'2) .
      2: erewrite subst_count.
      2: rewrite IHE'2.
      2: auto.
      auto.
  - destruct (count X E'1), (count X E'2).
    all: cbn.
    all: try rewrite IHE'1.
    all: try rewrite IHE'2.
    all: auto.
    + rewrite (@subst_id _ _ E'1) .
      2: erewrite subst_count.
      2: rewrite IHE'1.
      2: auto.
      auto.
    + rewrite (@subst_id _ _ E'2) .
      2: erewrite subst_count.
      2: rewrite IHE'2.
      2: auto.
      auto.
  - destruct (count X0 E'1), (count X0 E'2).
    all: cbn.
    all: try rewrite IHE'1.
    all: try rewrite IHE'2.
    all: auto.
  - destruct (count Y E'1), (count Y E'2).
    all: cbn.
    all: try rewrite IHE'1.
    all: try rewrite IHE'2.
    all: auto.
    all: try destruct eq_cvar.
    all: subst.
    all: try contradiction.
    all: try destruct eq_cvar.
    all: subst.
    all: try contradiction.
    all: auto.
  - destruct (count X E'1), (count X E'2).
    all: cbn.
    all: try rewrite IHE'1.
    all: try rewrite IHE'2.
    all: auto.
    all: try destruct eq_cvar.
    all: subst.
    all: try contradiction.
    all: try destruct eq_cvar.
    all: subst.
    all: try contradiction.
    + rewrite (@subst_id _ _ E'1).
      2: erewrite subst_count.
      2: rewrite IHE'1.
      2: auto.
      auto.
    + rewrite (@subst_id _ _ E'2) .
      2: erewrite subst_count.
      2: rewrite IHE'2.
      2: auto.
      auto.
Qed.

Lemma subst_preserve:
  ∀ {Δ' E' t},
    JE (l_with Δ' E') t →
    ∀ {X E Δ t'},
      JE (l_with (Map.merge (Map.one X t) Δ) E) t' →
      JE (l_with (Map.merge Δ' Δ) (subst_context E' X E)) t'.
Proof using.
  intros Δ' E' t p X.
  intros E.
  induction E.
  all: cbn.
  all: admit.
Admitted.

Lemma subst_var {X E}:
  subst_context (E_var X) X E = E.
Proof.
  induction E.
  all: cbn.
  all: auto.
  - destruct eq_cvar.
    all: subst.
    all: auto.
  - rewrite IHE.
    destruct eq_cvar.
    all: subst.
    all: auto.
  - rewrite IHE1, IHE2.
    auto.
  - rewrite IHE1, IHE2.
    auto.
  - rewrite IHE1, IHE2.
    auto.
  - rewrite IHE1, IHE2.
    destruct eq_cvar.
    all: subst.
    1: auto.
    destruct eq_cvar.
    all: subst.
    1: auto.
    auto.
Qed.

Lemma subst_assoc {X f g h}:
  subst_context (subst_context h X g) X f = subst_context h X (subst_context g X f).
Proof.
  induction f.
  all: cbn.
  all: auto.
  - destruct eq_cvar eqn:q.
    1: auto.
    cbn.
    rewrite q.
    auto.
  - rewrite IHf.
    destruct eq_cvar eqn:q.
    all: auto.
  - rewrite IHf1.
    rewrite IHf2.
    auto.
  - rewrite IHf1.
    rewrite IHf2.
    auto.
  - rewrite IHf1.
    rewrite IHf2.
    auto.
  - rewrite IHf1.
    rewrite IHf2.
    auto.
    destruct eq_cvar.
    1: auto.
    destruct eq_cvar.
    1: auto.
    auto.
Qed.

Definition oftype Δ t := { E | JE (l_with Δ E) t }.

Definition equiv {Δ t}: Relation_Definitions.relation (oftype Δ t) :=
  λ a b,
    ∀ N,
      (* FIXME substitute in contexts *)
      sat Map.empty (proj1_sig a) N ↔ sat Map.empty (proj1_sig b) N.

Instance equiv_Reflexive Δ t: Reflexive (@equiv Δ t).
Proof using.
  unfold equiv.
  unfold Reflexive.
  intros.
  reflexivity.
Qed.

Instance equiv_Symmetric Δ t: Symmetric (@equiv Δ t).
Proof using.
  unfold equiv.
  unfold Symmetric.
  intros.
  symmetry.
  auto.
Qed.

Instance equiv_Transitive Δ t: Transitive (@equiv Δ t).
Proof using.
  unfold equiv.
  unfold Transitive.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Instance equiv_Equivalence Δ t: Equivalence (@equiv Δ t) := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid Δ t: Setoid (oftype Δ t) := {
    equiv := equiv ;
}.
