Require Blech.Map.
Require Blech.Multiset.
Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.Environment.
Require Import Blech.Category.
Require Blech.OptionNotations.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Arith.PeanoNat.
Require Coq.Lists.List.

Require Import FunInd.
Require Import Psatz.

Import List.ListNotations.
Import IfNotations.

Implicit Type Γ: environment.
Implicit Type Δ: linear.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types x y: var.
Implicit Type σ: store.

Import Map.MapNotations.
Import Multiset.MultisetNotations.

Module ProofTree.
  Inductive JE: Set :=
  | JE_var Γ x
  | JE_lam: JE → JE
  | JE_app: JE → JE → JE
  | JE_tt Γ
  | JE_step: JE → JE → JE
  | JE_fanout: JE → JE → JE
  | JE_let: JE → JE → JE
  .

  #[local]
  Definition unknown_env (_: JE): environment := nil.
  #[local]
  Definition unknown_linear (_: JE): linear := Multiset.empty.
  #[local]
  Definition unknown_type (_: JE): type := t_unit.
  #[local]
  Definition unknown_context (_: JE): context := E_tt.

  Opaque unknown_env.
  Opaque unknown_linear.
  Opaque unknown_type.
  Opaque unknown_context.

  Function envof (E: JE): environment :=
    match E with
    | JE_var Γ _ => Γ
    | JE_lam p =>
        if envof p is cons _ T then T else unknown_env E
    | JE_app p1 _ => envof p1
    | JE_tt Γ => Γ
    | JE_step p1 _ => envof p1
    | JE_fanout p1 _ => envof p1
    | JE_let p1 _ => envof p1
    end.

  Function linof (E: JE): linear :=
    match E with
    | JE_var _ x => Multiset.one x
    | JE_lam p =>
        if envof p is cons (x, _) T
        then
          linof p \ x
        else
          unknown_linear E
    | JE_app p1 p2 => linof p1 ∪ linof p2
    | JE_tt _ => ∅
    | JE_step p1 p2 => linof p1 ∪ linof p2
    | JE_fanout p1 p2 => linof p1 ∪ linof p2
    | JE_let p1 p2 =>
        if envof p2 is cons (x, _) (cons (y, _) _)
        then
          linof p1 ∪ ((linof p2 \ x) \ y)
        else
          unknown_linear E
    end %multiset.

  Function ctxof (E: JE): context :=
    match E with
    | JE_var _ x => E_var x
    | JE_lam p =>
        if envof p is cons (x, t) _
        then
          E_lam x t (ctxof p)
        else
          unknown_context E
    | JE_app p1 p2 => E_app (ctxof p1) (ctxof p2)
    | JE_tt _ => E_tt
    | JE_step p1 p2 => E_step (ctxof p1) (ctxof p2)
    | JE_fanout p1 p2 => E_fanout (ctxof p1) (ctxof p2)
    | JE_let p1 p2 =>
        if envof p2 is cons (y, _) (cons (x, _) _)
        then
          E_let x y (ctxof p1) (ctxof p2)
        else
          unknown_context E
    end.

  Function typeof (E: JE): type :=
    match E with
    | JE_var Γ x => if find x Γ is Some t then t else unknown_type E
    | JE_lam p =>
        if envof p is cons (x, t) _
        then
          t * typeof p
        else
          unknown_type E
    | JE_app p1 p2 => if typeof p1 is _ * t then t else unknown_type E
    | JE_tt _ => t_unit
    | JE_step _ p2 => typeof p2
    | JE_fanout p1 p2 => typeof p1 * typeof p2
    | JE_let _ p2 => typeof p2
    end.

  Definition asserts (E: JE): Prop := Spec.JE (envof E) (linof E) (ctxof E) (typeof E).

  Notation "'test' p" := (match p with | left _ => true | right _ => false end) (at level 1).

  Function check (p: JE): bool :=
    match p with
    | JE_var Γ x =>
        if find x Γ is Some _ then true else false
    | JE_lam p =>
        (if envof p is cons (x, t) _
         then
           if Multiset.find x (linof p) is S _ then true else false
         else false)
        && check p
    | JE_app p1 p2 =>
        test (eq_environment (envof p1) (envof p2))
        && (if typeof p1 is t * _ then test (eq_type t (typeof p2)) else false)
        && check p1
        && check p2
    | JE_tt _ => true
    | JE_step p1 p2 =>
        test (eq_environment (envof p1) (envof p2))
        && (if typeof p1 is t_unit then true else false)
        && check p1
        && check p2
    | JE_fanout p1 p2 =>
        test (eq_environment (envof p1) (envof p2))
        && check p1
        && check p2
    | JE_let p1 p2 =>
        (match envof p2, typeof p1 with
         | cons (y, t2) (cons (x, t1) T), t1' * t2' =>
             test (eq_environment (envof p1) T)
             && test (eq_type t1 t1')
             && test (eq_type t2 t2')
             && (if Multiset.find y (linof p2) is S _ then true else false)
             && (if Multiset.find x (linof p2 \ y) is S _ then true else false)
         | _, _ => false
         end)
        && check p1
        && check p2
    end %bool.

  Lemma check_sound (p: JE): Bool.Is_true (check p) → asserts p.
  Proof.
    unfold asserts.
    functional induction (check p).
    all: cbn.
    all: intro q.
    all: try contradiction.
    - rewrite e0.
      constructor.
      apply Environment.find_sound.
      auto.
    - destruct (check p0).
      2: contradiction.
      rewrite e0.
      constructor.
      rewrite Multiset.add_minus.
      2: lia.
      rewrite <- e0.
      auto.
    - rewrite e1.
      rewrite e1 in IHb.
      destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      econstructor.
      all: eauto.
      rewrite _x.
      auto.
    - constructor.
    - destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      rewrite e1 in IHb.
      rewrite <- _x in IHb0.
      constructor.
      all: auto.
    - destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      rewrite <- _x in IHb0.
      constructor.
      all: auto.
    - destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      rewrite e0.
      rewrite e0 in IHb0.
      rewrite e1 in IHb.
      econstructor.
      1: eauto.
      repeat rewrite Multiset.add_minus.
      all: auto.
      + lia.
      + lia.
  Qed.

  Lemma check_complete {Γ Δ E t}:
    Spec.JE Γ Δ E t →
   ∃ p,
     Γ = envof p
     ∧ Δ = linof p
     ∧ E = ctxof p
     ∧ t = typeof p
     ∧ Bool.Is_true (check p).
  Proof.
    intro q.
    induction q.
    all: cbn.
    all: subst.
    - exists (JE_var Γ x).
      cbn.
      rewrite (find_complete H).
      all: repeat split; auto.
    - destruct IHq as [p [? [? [? [? ?]]]]].
      subst.
      exists (JE_lam p).
      cbn.
      rewrite <- H.
      cbn.
      rewrite <- H0.
      rewrite Multiset.find_merge.
      rewrite Multiset.find_one.
      destruct Nat.eq_dec.
      2: contradiction.
      cbn.
      destruct (check p).
      2: contradiction.
      all: repeat split; auto.
      apply Multiset.extensional.
      intro k.
      rewrite Multiset.find_minus.
      rewrite Multiset.find_merge.
      rewrite Multiset.find_one.
      destruct Nat.eq_dec.
      2: auto.
      cbn.
      auto.
    - destruct IHq1 as [p1 [? [? [? [? ?]]]]].
      destruct IHq2 as [p2 [? [? [? [? ?]]]]].
      subst.
      exists (JE_app p1 p2).
      cbn.
      rewrite H4.
      rewrite <- H2.
      destruct eq_environment.
      2: contradiction.
      destruct eq_type.
      2: contradiction.
      cbn.
      destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      cbn.
      all: repeat split; auto.
    - exists (JE_tt Γ).
      cbn.
      all: repeat split; auto.
    - destruct IHq1 as [p1 [? [? [? [? ?]]]]].
      destruct IHq2 as [p2 [? [? [? [? ?]]]]].
      subst.
      exists (JE_step p1 p2).
      cbn.
      rewrite H4.
      rewrite <- H2.
      cbn.
      destruct eq_environment.
      2: contradiction.
      cbn.
      destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      cbn.
      all: repeat split; auto.
    - destruct IHq1 as [p1 [? [? [? [? ?]]]]].
      destruct IHq2 as [p2 [? [? [? [? ?]]]]].
      subst.
      exists (JE_fanout p1 p2).
      cbn.
      rewrite H4.
      destruct eq_environment.
      2: contradiction.
      cbn.
      destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      cbn.
      all: repeat split; auto.
    - destruct IHq1 as [p1 [? [? [? [? ?]]]]].
      destruct IHq2 as [p2 [? [? [? [? ?]]]]].
      subst.
      exists (JE_let p1 p2).
      cbn.
      rewrite <- H4.
      rewrite <- H2.
      rewrite <- H5.
      cbn.
      destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      cbn.
      destruct eq_environment.
      2: contradiction.
      destruct eq_type.
      2: contradiction.
      cbn.
      destruct eq_type.
      2: contradiction.
      cbn.
      repeat rewrite Multiset.find_merge.
      repeat rewrite Multiset.find_one.
      repeat rewrite Multiset.find_minus.
      repeat rewrite Multiset.find_merge.
      repeat rewrite Multiset.find_one.
      destruct (Nat.eq_dec y y).
      2: contradiction.
      destruct (Nat.eq_dec x x).
      2: contradiction.
      cbn.
      destruct Nat.eq_dec.
      + subst.
        cbn.
        all: repeat split; auto.
        apply Multiset.extensional.
        intro k.
        repeat rewrite Multiset.find_merge.
        repeat rewrite Multiset.find_one.
        repeat rewrite Multiset.find_minus.
        repeat rewrite Multiset.find_merge.
        repeat rewrite Multiset.find_one.
        destruct Nat.eq_dec.
        all: auto.
      + cbn.
        all: repeat split; auto.
        apply Multiset.extensional.
        intro k.
        repeat rewrite Multiset.find_merge.
        repeat rewrite Multiset.find_one.
        repeat rewrite Multiset.find_minus.
        repeat rewrite Multiset.find_merge.
        repeat rewrite Multiset.find_one.
        destruct Nat.eq_dec.
        all: cbn.
        all: subst.
        all: auto.
        * destruct Nat.eq_dec.
          1: subst; contradiction.
          cbn.
          auto.
        * destruct Nat.eq_dec.
          all: subst.
          all: cbn.
          all: auto.
  Qed.
End ProofTree.

Section Typecheck.
  Import OptionNotations.

  Function typecheck Γ E: option (linear * type) :=
    match E with
    | E_var x =>
        do t ← find x Γ ;
        Some (Multiset.one x, t)
    | E_lam x t1 E =>
        do (Δ', t2) ← typecheck ((x, t1) :: Γ) E ;
        match Multiset.find x Δ' with
        | S _ => Some (Δ' \ x, t1 * t2)
        | _ => None
        end
    | E_app E E' =>
        do (Δ', t1 * t2) ← typecheck Γ E ;
        do (Δ, t1') ← typecheck Γ E' ;
        if eq_type t1 t1'
        then
          Some (Δ' ∪ Δ, t2)
        else
          None

    | E_tt => Some (∅, t_unit)
    | E_step E E' =>
        do (Δ', t_unit) ← typecheck Γ E ;
        do (Δ, t) ← typecheck Γ E' ;
        Some (Δ' ∪ Δ, t)

    | E_fanout E E' =>
        do (Δ', t1) ← typecheck Γ E ;
        do (Δ, t2) ← typecheck Γ E' ;
        Some (Δ' ∪ Δ, t1 * t2)

    | E_let x y E E' =>
        do (Δ', t1 * t2) ← typecheck Γ E ;
        do (Δ, t3) ← typecheck ((y, t2) :: (x, t1) :: Γ) E' ;
        match Multiset.find x (Δ \ y), Multiset.find y Δ with
        | S _, S _ => Some (Δ' ∪ ((Δ \ y) \ x), t3)
        | _, _ => None
        end
    end
      %list %multiset.
End Typecheck.

Theorem typecheck_sound:
  ∀ Γ {E Δ' t}, typecheck Γ E = Some (Δ', t) → JE Γ Δ' E t.
Proof using.
  intros Γ E.
  functional induction (typecheck Γ E).
  all: cbn.
  all: intros ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
  - apply find_sound.
    auto.
  - rewrite Multiset.add_minus.
    all: auto.
    lia.
  - repeat rewrite Multiset.add_minus.
    all: auto.
    all: lia.
Qed.

Notation "'do' n ← e0 ; e1" :=
  (List.flat_map (λ n, e1) e0)
    (n pattern, at level 200, left associativity): list_scope.

Fixpoint generate t: list normal :=
  match t with
  | t_unit => [N_tt]
  | t * t' =>
      do N ← generate t ;
      do N' ← generate t' ;
      [N_fanout N N']
  end%list.

Fixpoint search σ E: list span :=
  match E with
  | E_var x => if Map.find x σ is Some N then [x ↦ N |- N] else []

  | E_lam x t E =>
      do N0 ← generate t ;
      do (σ' |- N1) ← search (x ↦ N0 ∪ σ) E ;
      if Map.find x σ' is Some N0'
      then
        if eq_normal N0 N0'
        then
          [σ' \ x |- N_fanout N0 N1]
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

  | E_let x y E E' =>
      do (σ1 |- N) ← search σ E ;
      do (a, b) ← (if N is N_fanout a b then [(a, b)] else []) ;
      do (σ2 |- N') ← search ((x ↦ a) ∪ (y ↦ b) ∪ σ) E' ;
      match Map.find x (σ2 \ y), Map.find y σ2 with
      | Some a', Some b' =>
          if eq_normal a a'
          then
            if eq_normal b b'
            then
              [σ1 ∪ ((σ2 \ y) \ x) |- N']
            else
              []
          else
            []
      | _, _ => []
      end
  end%list %map.

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
    destruct Map.find eqn:q.
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
    induction (IHE (x ↦ a ∪ σ)).
    1: constructor.
    cbn.
    destruct Map.find eqn:q.
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
    induction (IHE2 (((x ↦ N1 ∪ y ↦ N2) ∪ σ))).
    1: constructor.
    cbn.
    destruct (Map.find x (σ1 \ y)) eqn:q.
    2: auto.
    destruct (Map.find y σ1) eqn:q'.
    2: auto.
    destruct (eq_normal N1 n).
    2: auto.
    subst.
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

(* FIXME type check *)
Record span := {
  s: Set ;
  π1: s → store ;
  π2: s → normal ;
}.

Definition satspan E: span :=
  {|
    s := { σN & sat (fst σN) E (snd σN) } ;
    π1 s := fst (projT1 s) ;
    π2 s := snd (projT1 s) ;
  |}.

Definition searchspan E: span :=
  {|
    s := { '(σ, N, n) | List.nth_error (search σ E) n = Some (σ |- N) } ;
    π1 '(exist _ (σ, _, _) _) := σ ;
    π2 '(exist _ (_, N, _) _) := N ;
  |}.

Definition sound E: s (searchspan E) → s (satspan E).
Proof.
  cbn.
  intros [[[σ N] n] p].
  exists (σ, N).
  cbn.
  generalize dependent n.
  induction (search_sound σ E).
  all: intros n p.
  1: destruct n; discriminate.
  destruct n.
  - cbn in p.
    inversion p.
    subst.
    auto.
  - cbn in p.
    destruct Ps.
    1: destruct n; discriminate.
    apply (IHs0 n).
    auto.
Defined.

Definition π1_sound1 E: ∀ s, π1 (searchspan E) s = π1 (satspan E) (sound E s).
Proof.
  cbn.
  intros [[[σ N] n] p].
  cbn.
  auto.
Defined.

Definition π2_sound1 E: ∀ s, π2 (searchspan E) s = π2 (satspan E) (sound E s).
Proof.
  cbn.
  intros [[[σ N] n] p].
  cbn.
  auto.
Defined.

Inductive notin {A} (a: A): list A → Prop :=
| notin_empty: notin a nil
| notin_cons a' T: a ≠ a' → notin a T → notin a (cons a' T).

Lemma subst_assoc {x f g h}:
  subst_context (subst_context h x g) x f = subst_context h x (subst_context g x f).
Proof.
  induction f.
  all: cbn.
  all: auto.
  - destruct eq_var eqn:q.
    1: auto.
    cbn.
    rewrite q.
    auto.
  - rewrite IHf.
    destruct eq_var eqn:q.
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
    destruct eq_var.
    1: auto.
    destruct eq_var.
    1: auto.
    auto.
Qed.

Fixpoint useall Γ: linear :=
  if Γ is cons (x, _) T
  then
    Multiset.merge (Multiset.one x) (useall T)
  else
    Multiset.empty.

Definition oftype Γ t := { E | JE Γ (useall Γ) E t }.

Record iso A B := {
    to: A → B ;
    from: B → A ;
    to_from b: to (from b) = b;
    from_to a: from (to a) = a;
}.
Arguments to {A B}.
Arguments from {A B}.
Arguments to_from {A B}.
Arguments from_to {A B}.

Inductive tr A: Prop := | tr_intro (a: A).

Definition equiv E E' :=
  ∀ σ N, tr (iso (sat σ E N) (sat σ E' N)).

Instance equiv_Reflexive: Reflexive equiv.
Proof.
  unfold Reflexive.
  intro.
  exists.
  exists (λ a, a) (λ a, a).
  all: auto.
Qed.

Instance equiv_Symmetric: Symmetric equiv.
Proof.
  unfold Symmetric.
  intros x y p σ N.
  destruct (p σ N) as [p'].
  exists.
  exists (from p') (to p').
  - apply from_to.
  - apply to_from.
Qed.

Instance equiv_Transitive: Transitive equiv.
Proof.
  unfold Transitive.
  intros ? ? ? p q σ N.
  destruct (p σ N) as [p'].
  destruct (q σ N) as [q'].
  exists.
  exists (λ a, to q' (to p' a)) (λ a, from p' (from q' a)).
  - intros.
    rewrite to_from.
    rewrite to_from.
    auto.
  - intros.
    rewrite from_to.
    rewrite from_to.
    auto.
Qed.

Instance equiv_Equivalence: Equivalence equiv := {
    Equivalence_Reflexive := _ ;
}.

Instance context_Setoid: Setoid context := {
    equiv := equiv ;
}.

Lemma subst_var {x E}:
  subst_context (E_var x) x E = E.
Proof.
  induction E.
  all: cbn.
  all: auto.
  all: try destruct eq_var.
  all: subst.
  all: auto.
  all: try destruct eq_var.
  all: try rewrite IHE.
  all: try rewrite IHE1.
  all: try rewrite IHE2.
  all: auto.
Qed.
