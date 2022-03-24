Require Import Blech.Opaque.
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
Implicit Type Δ: usage.
Implicit Type E: context.
Implicit Type t: type.
Implicit Types x y: var.
Implicit Type ρ: subst.
Implicit Type v: intro.

Definition eq_usage Δ Δ': {Δ = Δ'} + {Δ ≠ Δ'}.
Proof.
  decide equality.
  destruct a as [x u], p as [y u'].
  destruct (eq_var x y), (eq_use u u').
  all: subst.
  all: auto.
  all: right.
  all: intro p.
  all: inversion p.
  all: auto.
Defined.

Section Typecheck.
  Import OptionNotations.

  Function lookup x Δ :=
    if Δ is cons (y, u) Δ'
    then
        if eq_var x y
        then
          if u is u_unused
          then
             Some (cons (y, u_used) Δ')
          else
            None
        else
          do Δ'' ← lookup x Δ' ;
          Some (cons (y, u) Δ'')
  else
    None.

  Function usecheck Δ E: option usage :=
    match E with
    | E_lam x E =>
        do ' ((y, u_used) :: Δ') ← usecheck ((x, u_unused) :: Δ) E ;
        if eq_var x y
        then
          Some Δ'
        else
          None

    | E_tt => Some Δ

    | E_fanout E E' =>
        do Δ1 ← usecheck Δ E ;
        usecheck Δ1 E'

    | E_neu e =>
        useinfer Δ e

    end
      %list
  with useinfer Δ e: option usage :=
    match e with
    | e_var x => lookup x Δ

    | e_app e E' =>
        do Δ1 ← useinfer Δ e ;
        usecheck Δ1 E'

    | e_step e E' t =>
        do Δ1 ← useinfer Δ e ;
        usecheck Δ1 E'

    | e_let x y e E' t3 =>
        do Δ1 ← useinfer Δ e ;
        do ' ((y', u_used) :: (x', u_used) :: Δ2) ← usecheck ((y, u_unused) :: (x, u_unused) :: Δ1) E' ;
        match eq_var x x', eq_var y y' with
        | left _, left _ => Some Δ2
        | _, _ => None
        end

    | e_cut E t => usecheck Δ E
    end
      %list.

  Function typecheck Γ E t: bool :=
    match E, t with
    | E_lam x E, t1 * t2 =>
        typecheck ((x, t1) :: Γ) E t2

    | E_tt, t_unit => true

    | E_fanout E E', t1 * t2 =>
        typecheck Γ E t1
        && typecheck Γ E' t2

    | E_neu e, _ =>
        if typeinfer Γ e is Some t'
        then
          if eq_type t t' then true else false
        else
          false

    | _, _ => false
    end
     %bool %list
  with typeinfer Γ e: option type :=
    match e with
    | e_var x => find x Γ

    | e_app e E' =>
        do ' (t1 * t2) ← typeinfer Γ e ;
        if typecheck Γ E' t1
        then
          Some t2
        else
          None

    | e_step e E' t =>
        if typecheck Γ E' t
        then
          do ' t_unit ← typeinfer Γ e ;
          Some t
        else
          None

    | e_let x y e E' t3 =>
        do ' (t1 * t2) ← typeinfer Γ e ;
        if typecheck ((y, t2) :: (x, t1) :: Γ) E' t3
        then
          Some t3
        else
          None

    | e_cut E t =>
        if typecheck Γ E t
        then
          Some t
        else
          None
    end
      %list.
End Typecheck.

Fixpoint
  usecheck_sound {E} {struct E}:
  ∀ {Δ Δ'}, usecheck Δ E = Some Δ' → Δ ⊢ E ⊠ Δ'
    with
  useinfer_sound {e} {struct e}:
  ∀ {Δ Δ'}, useinfer Δ e = Some Δ' → se Δ e Δ'
.
Proof using.
  - destruct E.
    all: cbn.
    all: intros ? ? p.
    all: inversion p.
    all: subst.
    all: clear p.
    + destruct usecheck eqn:q.
      2: discriminate.
      destruct u.
      1: discriminate.
      destruct p.
      destruct u0.
      2: discriminate.
      destruct eq_var.
      2: discriminate.
      inversion H0.
      subst.
      constructor.
      auto.
    + constructor.
    + destruct usecheck eqn:q1.
      2: discriminate.
      econstructor.
      all: eauto.
    + constructor.
      apply useinfer_sound.
      auto.
  - destruct e.
    all: cbn.
    all: intros ? ? p.
    all: inversion p.
    all: subst.
    all: clear p.
    + constructor.
      generalize dependent Δ'.
      functional induction (lookup x Δ).
      all: cbn.
      all: intros ? p.
      all: inversion p.
      all: subst.
      all: constructor.
      all: eauto.
    + destruct useinfer eqn:q1.
      2: discriminate.
      econstructor.
      all: eauto.
    + destruct useinfer eqn:q1.
      2: discriminate.
      econstructor.
      all: eauto.
    + destruct useinfer eqn:q1.
      2: discriminate.
      destruct usecheck eqn:q2.
      2: discriminate.
      destruct u0.
      1: discriminate.
      destruct p.
      destruct u1.
      2: discriminate.
      destruct u0.
      1: discriminate.
      destruct p.
      destruct u1.
      2: discriminate.
      destruct eq_var.
      2: discriminate.
      destruct eq_var.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
    + constructor.
      eauto.
Qed.

Fixpoint
  typecheck_sound {E} {struct E}:
  ∀ {Γ t}, Bool.Is_true (typecheck Γ E t) → check Γ E t
    with
  typeinfer_sound {e} {struct e}:
  ∀ {Γ t}, typeinfer Γ e = Some t → infer Γ e t.
Proof using.
  - destruct E.
    all: cbn.
    all: intros ? ? p.
    all: try contradiction.
    + destruct t.
      all: try contradiction.
      destruct typecheck eqn:q.
      2: contradiction.
      constructor.
      apply typecheck_sound.
      rewrite q.
      auto.
    + destruct t.
      all: try contradiction.
      constructor.
    + destruct t.
      all: try contradiction.
      destruct typecheck eqn:q1.
      2: contradiction.
      destruct typecheck eqn:q2 in p.
      2: contradiction.
      constructor.
      * apply typecheck_sound.
        rewrite q1.
        auto.
      * apply typecheck_sound.
        rewrite q2.
        auto.
    + constructor.
      destruct typeinfer eqn:q.
      2: contradiction.
      destruct eq_type.
      2: contradiction.
      subst.
      auto.
  - destruct e.
    all: cbn.
    all: intros ? ? p.
    all: inversion p.
    all: subst.
    all: clear p.
    + constructor.
      apply find_sound.
      auto.
    + destruct typeinfer eqn:q1.
      2: discriminate.
      destruct t0.
      all: try discriminate.
      destruct typecheck eqn:q2.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
      apply typecheck_sound.
      rewrite q2.
      cbv.
      auto.
    + destruct typecheck eqn:q2.
      2: discriminate.
      destruct typeinfer eqn:q1.
      2: discriminate.
      destruct t1.
      all: try discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
      apply typecheck_sound.
      rewrite q2.
      cbv.
      auto.
    + destruct typeinfer eqn:q1.
      2: discriminate.
      destruct t1.
      all: try discriminate.
      destruct typecheck eqn:q2.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
      apply typecheck_sound.
      rewrite q2.
      cbv.
      auto.
    + destruct typecheck eqn:q.
      2: discriminate.
      inversion H0.
      subst.
      constructor.
      apply typecheck_sound.
      rewrite q.
      apply I.
Qed.

Fixpoint usecheck_complete {E Δ Δ'} (p: Δ ⊢ E ⊠ Δ'):
  usecheck Δ E = Some Δ'
with useinfer_complete {e Δ Δ'} (p: se Δ e Δ'):
  useinfer Δ e = Some Δ'.
Proof using.
  - destruct p.
    all: cbn.
    all: try rewrite (usecheck_complete _ _ _ p).
    all: try rewrite (usecheck_complete _ _ _ p1).
    all: try rewrite (usecheck_complete _ _ _ p2).
    all: try rewrite (useinfer_complete _ _ _ H).
    all: auto.
    destruct eq_var.
    2: contradiction.
    auto.
  - destruct p.
    all: cbn.
    all: try rewrite (useinfer_complete _ _ _ p).
    all: try rewrite (usecheck_complete _ _ _ H).
    all: auto.
    + induction H.
      all: cbn.
      * destruct eq_var.
        2: contradiction.
        auto.
      * destruct eq_var.
        1: subst; contradiction.
        rewrite IHlmem.
        auto.
    + destruct eq_var.
      2: contradiction.
      destruct eq_var.
      2: contradiction.
      auto.
Qed.

Fixpoint typecheck_complete {Γ E t} (p: check Γ E t):
  typecheck Γ E t = true
with typeinfer_complete {Γ e t} (p: infer Γ e t):
  typeinfer Γ e = Some t.
Proof using.
  - destruct p.
    all: cbn.
    all: try rewrite (typecheck_complete _ _ _ p).
    all: try rewrite (typecheck_complete _ _ _ p1).
    all: try rewrite (typecheck_complete _ _ _ p2).
    all: try rewrite (typeinfer_complete _ _ _ H).
    all: auto.
    destruct eq_type.
    2: contradiction.
    auto.
  - destruct p.
    all: cbn.
    all: try rewrite (typeinfer_complete _ _ _ p).
    all: try rewrite (typecheck_complete _ _ _ H).
    all: auto.
    apply find_complete.
    auto.
Qed.

Notation "'do' n ← e0 ; e1" :=
  (List.flat_map (λ n, e1) e0)
    (n pattern, at level 200, left associativity): list_scope.

Fixpoint generate t: list intro :=
  match t with
  | t_var _ => []
  | t_unit => [v_tt]
  | t * t' =>
      do v ← generate t ;
      do v' ← generate t' ;
      [v_fanout v v']
  end%list.

Function take x ρ :=
  if ρ is cons (y, v) ρ'
  then
    if eq_var x y
    then
      Some (v, cons (y, v_tt) ρ')
    else
      if take x ρ' is Some (v', ρ'')
      then
        Some (v', cons (y, v) ρ'')
      else
        None
  else
    None.

Fixpoint verify ρ E v: list subst :=
  match E, v with
  | E_lam x E, v_fanout v1 v2 =>
      do ρ' ← verify ((x, v1) :: ρ) E v2 ;
      if ρ' is (y, _) :: ρ''
      then
        if eq_var x y
        then [ρ'']
        else []
      else
        []

  | E_tt, v_tt => [ρ]

  | E_fanout E E', v_fanout v1 v2 =>
      do ρ1 ← verify ρ E v1 ;
      verify ρ1 E' v2

  | E_neu e, _ =>
      do (ρ' |- v') ← search ρ e ;
      if eq_intro v v'
      then [ρ']
      else []
  | _, _ => []
  end%list
with search ρ e: list span :=
  match e with
  | e_var x => if take x ρ is Some (v, ρ') then [ρ' |- v] else []

  | e_app e E' =>
      do (ρ1 |- v) ← search ρ e ;
      if v is v_fanout v0 v1
      then
          do ρ2 ← verify ρ1 E' v0 ;
          [ρ2 |- v1]
      else []

  | e_step e E' t2 =>
      do v' ← generate t2 ;
      do (ρ1 |- v) ← search ρ e ;
      if v is v_tt
      then
        do ρ2 ← verify ρ1 E' v' ;
        [ρ2 |- v']
      else
        []

  | e_let x y e E' t3 =>
      do v' ← generate t3 ;
      do (ρ1 |- v) ← search ρ e ;
      do (a, b) ← (if v is v_fanout a b then [(a, b)] else []) ;
      do ρ2 ← verify ((y, b) :: (x , a) :: ρ1) E' v' ;
      if ρ2 is (y', _) :: (x', _) :: ρ2'
      then
        match eq_var x x', eq_var y y' with
        | left _, left _ =>
            [ρ2' |- v']
        | _, _ => []
        end
      else
        []

  | e_cut E t =>
      do v ← generate t ;
      do ρ' ← verify ρ E v ;
      [ρ' |- v]
  end%list.

Lemma Forall_mon {A} {p: A → _} {l r}:
  List.Forall p l → List.Forall p r →
  List.Forall p (l ++ r).
Proof.
  intros.
  induction l.
  1: auto.
  cbn.
  inversion H.
  constructor.
  all: auto.
Qed.

Lemma In_mon {A} {a: A} {l r}:
  List.In a (l ++ r) →
  List.In a l ∨ List.In a r.
Proof.
  intros.
  induction l.
  1: auto.
  cbn in *.
  destruct H.
  - subst.
    left.
    left.
    auto.
  - destruct (IHl H).
    + left.
      right.
      auto.
    + right.
      auto.
Qed.

Lemma In_inl {A} {a: A} {l r}:
  List.In a l →
  List.In a (l ++ r).
Proof.
  intros.
  induction l.
  1: contradiction.
  cbn in *.
  destruct H.
  - left.
    auto.
  - right.
    auto.
Qed.

Lemma In_inr {A} {a: A} {l r}:
  List.In a r →
  List.In a (l ++ r).
Proof.
  intros.
  induction l.
  1: auto.
  cbn in *.
  right.
  auto.
Qed.

Theorem verify_complete {ρ E v p'}:
  accepts ρ E v p' →
  List.In p' (verify ρ E v)
with search_complete {ρ e v ρ'}:
  produces ρ e v ρ' →
  List.In ((ρ' |- v)) (search ρ e).
Proof using.
  Open Scope list.
  - intro q.
    destruct q.
    all: cbn.
    + left.
      auto.
    + assert (q1' := verify_complete _ _ _ _ q1).
      assert (q2' := verify_complete _ _ _ _ q2).
      clear q1 q2.
      induction (verify ρ1 E v).
      1: inversion q1'.
      cbn in *.
      destruct q1'.
      2: apply In_inr.
      2: auto.
      apply In_inl.
      subst.
      auto.
    + assert (q' := verify_complete _ _ _ _ q).
      clear q.
      induction (verify ((x, v1) :: ρ1) E v2).
      1: inversion q'.
      cbn in *.
      destruct q'.
      2: apply In_inr.
      2: auto.
      apply In_inl.
      clear IHl.
      destruct a.
      1: discriminate.
      inversion H.
      subst.
      destruct eq_var.
      2: contradiction.
      cbn.
      auto.
    + assert (H' := search_complete _ _ _ _ H).
      clear H.
      induction (search ρ1 e).
      1: contradiction.
      cbn in *.
      destruct H'.
      2: apply In_inr.
      2: auto.
      apply In_inl.
      clear IHl.
      destruct a.
      inversion H.
      subst.
      destruct eq_intro.
      2: contradiction.
      cbn.
      auto.
  - intro q.
    destruct q.
    all: cbn.
    + replace (take x ρ) with (Some (v, ρ')).
      1: cbv; auto.
      induction H.
      * cbn.
        destruct eq_var.
        2:contradiction.
        auto.
      * cbn.
        destruct eq_var.
        1: subst; contradiction.
        rewrite <- IHpmem.
        auto.
    + assert (q' := search_complete _ _ _ _ q).
      assert (H' := verify_complete _ _ _ _ H).
      clear q H.
      admit.
    + admit.
    + admit.
    + admit.
Admitted.

Theorem verify_sound {ρ E v}:
  List.Forall (accepts ρ E v) (verify ρ E v)
with search_sound {ρ e}:
  List.Forall (λ '(p' |- v), produces ρ e v p') (search ρ e).
Proof using.
  Open Scope list.
  - destruct E.
    all: cbn.
    + destruct v.
      1,3: constructor.
      induction (verify_sound ((x, v1) :: ρ) E v2).
      all: cbn.
      1: constructor.
      apply Forall_mon.
      2: auto.
      clear IHf.
      destruct x0.
      1: auto.
      destruct p as [y v].
      destruct eq_var.
      all: cbn.
      2: auto.
      constructor.
      2: auto.
      subst.
      econstructor.
      eauto.
    + destruct v.
      2,3: constructor.
      constructor.
      2: constructor.
      constructor.
    + destruct v.
      1,3: constructor.
      induction (verify_sound ρ E1 v1).
      1: constructor.
      cbn.
      apply Forall_mon.
      2: auto.
      clear IHf.
      induction (verify_sound x E2 v2).
      all: cbn.
      all: auto.
      constructor.
      2: auto.
      econstructor.
      all: eauto.
    + induction (search_sound ρ e).
      all: cbn.
      1: constructor.
      apply Forall_mon.
      2: auto.
      clear IHf.
      destruct x.
      destruct eq_intro.
      all: cbn.
      all: auto.
      constructor.
      2: auto.
      constructor.
      subst.
      auto.
  - destruct e.
    all: cbn.
    + destruct (take x ρ) eqn:q.
      2: constructor.
      destruct p.
      constructor.
      2: constructor.
      constructor.
      clear verify_sound search_sound.
      generalize dependent i.
      generalize dependent l.
      functional induction (take x ρ).
      all: try discriminate.
      all: intros ? ? q.
      all: inversion q.
      all: subst.
      all: clear q.
      * constructor.
      * constructor.
        all: eauto.
    + induction (search_sound ρ e).
      1: constructor.
      cbn.
      apply Forall_mon.
      2: auto.
      clear IHf.
      destruct x.
      destruct v.
      all: cbn.
      all: auto.
      induction (verify_sound ρ0 E' v1).
      all: cbn.
      all: auto.
      constructor.
      2: auto.
      econstructor.
      all: eauto.
    + induction (generate t).
      all: cbn in *.
      1: constructor.
      apply Forall_mon.
      all: auto.
      clear IHl.
      induction (search_sound ρ e).
      1: constructor.
      cbn.
      apply Forall_mon.
      2: auto.
      clear IHf.
      destruct x.
      destruct v.
      all: cbn.
      all: auto.
      all: auto.
      induction (verify_sound ρ0 E' a).
      all: auto.
      all: cbn.
      1: constructor.
      constructor.
      all: auto.
      econstructor.
      all: eauto.
    + induction (generate t).
      all: cbn in *.
      1: constructor.
      apply Forall_mon.
      all: auto.
      clear IHl.
      induction (search_sound  ρ e).
      1: constructor.
      cbn in *.
      apply Forall_mon.
      2: auto.
      destruct x0.
      destruct v.
      all: cbn.
      1,3: constructor.
      clear IHf.
      clear f.
      rewrite List.app_nil_r in *.
      cbn.
      induction (verify_sound ((y, v2) :: (x, v1) :: ρ0) E' a).
      all: cbn.
      1: constructor.
      apply Forall_mon.
      all: auto.
      destruct x0.
      1: constructor.
      destruct p.
      clear IHf.
      destruct x0.
      1: constructor.
      destruct p.
      destruct eq_var.
      2: constructor.
      destruct eq_var.
      2: constructor.
      constructor.
      2: constructor.
      subst.
      econstructor.
      all: eauto.
    + induction (generate t).
      1: constructor.
      cbn.
      apply Forall_mon.
      2: auto.
      clear IHl.
      induction (verify_sound ρ E a).
      1: constructor.
      cbn.
      constructor.
      all: auto.
      constructor.
      auto.
Qed.

Definition useonce Γ u: usage := List.map (λ '(x, t), (x, u)) Γ.

Definition oftype Γ t :=
  { E |
    Bool.Is_true (
        typecheck Γ E t
        && if usecheck (useonce Γ u_unused) E is Some Δ
           then
             if eq_usage Δ (useonce Γ u_used) then true else false
           else
             false)
  }.

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
