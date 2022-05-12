Require Import Blech.Opaque.
Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.Environment.
Require Import Blech.Category.
Require Blech.Term.
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
Implicit Types t τ: type.
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
    | E_var x => lookup x Δ

    | E_function _ E => usecheck Δ E

    | E_epsilon x _ c =>
        do ' ((y, u_used) :: Δ') ← useinfer ((x, u_unused) :: Δ) c ;
        if eq_var x y
        then
          Some Δ'
        else
          None

    | E_tt => Some Δ

    | E_fanout E E' =>
        do Δ1 ← usecheck Δ E ;
        usecheck Δ1 E'

    | E_match_fanout x _ y _ c =>
        do ' ((y', u_used) :: (x', u_used) :: Δ') ← useinfer ((y, u_unused) :: (x, u_unused) :: Δ) c ;
        match eq_var x x', eq_var y y' with
        | left _, left _ => Some Δ'
        | _, _ => None
        end

    | E_dup E => usecheck Δ E
    | E_del E => usecheck Δ E
    end
      %list
  with useinfer Δ c: option usage :=
    match c with
    | c_relation _ E => usecheck Δ E

    | c_unify E E' =>
        do Δ1 ← usecheck Δ E ;
        usecheck Δ1 E'

    | c_true => Some Δ
    | c_false => Some Δ

    | c_and c c' =>
        do Δ1 ← useinfer Δ c ;
        useinfer Δ1 c'

    | c_or c c' =>
        do Δ1 ← useinfer Δ c ;
        do Δ2 ← useinfer Δ c' ;
        if eq_usage Δ1 Δ2
        then
          Some Δ1
        else
          None
    end
      %list.

  Function typecheck X Γ E: option type :=
    match E with
    | E_var x => Assoc.find x Γ

    | E_function f E =>
        do ' g_function τ A ← Assoc.find f X ;
        do τ' ← typecheck X Γ E ;
        if eq_type τ τ'
        then
          Some (t_var A)
        else
          None

    | E_tt => Some t_unit

    | E_fanout E E' =>
        do τ1 ← typecheck X Γ E ;
        do τ2 ← typecheck X Γ E' ;
        Some (τ1 * τ2)

    | E_match_fanout x t1 y t2 c =>
        if typeinfer X ((y, t2) :: (x, t1) :: Γ) c
        then
          Some (t1 * t2)
        else
          None

    | E_dup E =>
        do τ ← typecheck X Γ E ;
        Some (τ * τ)

    | E_del E =>
        do _ ← typecheck X Γ E ;
        Some t_unit

    | E_epsilon x τ E =>
        if typeinfer X ((x, τ) :: Γ) E
        then
          Some τ
        else
          None
    end
  with typeinfer X Γ c: bool :=
    match c with
    | c_relation R E =>
        match Assoc.find R X, typecheck X Γ E with
        | Some (g_relation τ), Some τ' => if eq_type τ τ' then true else false
        | _, _ => false
        end

    | c_unify E E' =>
        match typecheck X Γ E, typecheck X Γ E' with
        | Some τ1, Some τ2 => if eq_type τ1 τ2 then true else false
        | _, _ => false
        end

    | c_true => true
    | c_false => true

    | c_and c c' => typeinfer X Γ c && typeinfer X Γ c'
    | c_or c c' => typeinfer X Γ c && typeinfer X Γ c'
    end
      %bool.
End Typecheck.

Fixpoint
  usecheck_sound {E} {struct E}:
  ∀ {Δ Δ'}, usecheck Δ E = Some Δ' → sE Δ E Δ'
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
    + constructor.
      generalize dependent Δ'.
      functional induction (lookup x Δ).
      all: cbn.
      all: intros ? p.
      all: inversion p.
      all: subst.
      all: constructor.
      all: eauto.
    + constructor.
      eauto.
    + constructor.
      destruct useinfer eqn:q.
      2: discriminate.
      destruct u eqn:q'.
      all: try discriminate.
      destruct p.
      destruct u1.
      all: try discriminate.
      destruct eq_var.
      2: discriminate.
      inversion H0.
      subst.
      eauto.
    + constructor.
    + destruct usecheck eqn:q.
      2: discriminate.
      econstructor.
      all: eauto.
    + destruct useinfer eqn:q.
      2: discriminate.
      destruct u.
      1: discriminate.
      destruct p.
      destruct u0.
      2: discriminate.
      destruct u.
      1: discriminate.
      destruct p.
      destruct u0.
      2: discriminate.
      destruct eq_var.
      2: discriminate.
      destruct eq_var.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      eauto.
    + constructor.
      eauto.
    + constructor.
      eauto.
  - destruct e.
    all: cbn.
    all: intros ? ? p.
    all: inversion p.
    all: subst.
    all: clear p.
    + destruct usecheck eqn:q1.
      2: discriminate.
      inversion H0.
      subst.
      constructor.
      eauto.
    + destruct usecheck eqn:q1.
      2: discriminate.
      econstructor.
      all: eauto.
    + constructor.
    + constructor.
    + destruct useinfer eqn:q1.
      2: discriminate.
      econstructor.
      all: eauto.
    + destruct useinfer eqn:q1.
      2: discriminate.
      destruct useinfer eqn:q2 in H0.
      2: discriminate.
      destruct eq_usage.
      2: discriminate.
      inversion H0.
      subst.
      econstructor.
      all: eauto.
Qed.

Fixpoint
  typecheck_sound {E} {struct E}:
  ∀ {X Γ t}, typecheck X Γ E = Some t → check X Γ E t
    with
  typeinfer_sound {c} {struct c}:
  ∀ {X Γ}, Bool.Is_true (typeinfer X Γ c) → infer X Γ c.
Proof using.
  - destruct E.
    all: cbn.
    all: intros ? ? ? p.
    all: try contradiction.
    + constructor.
      auto.
    + destruct Assoc.find eqn:q1 in p.
      all: try discriminate.
      destruct g.
      all: try discriminate.
      destruct typecheck eqn:q2 in p.
      2: discriminate.
      destruct eq_type in p.
      2: discriminate.
      inversion p.
      subst.
      econstructor.
      all: eauto.
    + destruct typeinfer eqn:q.
      2: discriminate.
      inversion p.
      subst.
      constructor.
      apply typeinfer_sound.
      rewrite q.
      cbv.
      constructor.
    + inversion p.
      constructor.
    + destruct typecheck eqn:q1 in p.
      2: discriminate.
      destruct typecheck eqn:q2 in p.
      2: discriminate.
      inversion p.
      constructor.
      all: eapply typecheck_sound.
      all: auto.
    + destruct typeinfer eqn:q1.
      2: discriminate.
      inversion p.
      subst.
      econstructor.
      apply typeinfer_sound.
      rewrite q1.
      constructor.
    + destruct typecheck eqn:q1.
      2: discriminate.
      inversion p.
      constructor.
      auto.
    + destruct typecheck eqn:q1.
      2: discriminate.
      inversion p.
      econstructor.
      eauto.
  - destruct c.
    all: cbn.
    all: intros ? ? p.
    + destruct Assoc.find eqn:q1 in p.
      all: try contradiction.
      destruct g.
      all: try contradiction.
      destruct typecheck eqn:q2 in p.
      2: contradiction.
      destruct eq_type in p.
      2: contradiction.
      subst.
      econstructor.
      all: eauto.
    + destruct typecheck eqn:q1 in p.
      2: contradiction.
      destruct typecheck eqn:q2 in p.
      2: contradiction.
      destruct eq_type.
      2: contradiction.
      subst.
      econstructor.
      all: eauto.
    + constructor.
    + constructor.
    + destruct typeinfer eqn:q1 in p.
      2: contradiction.
      destruct typeinfer eqn:q2 in p.
      2: contradiction.
      constructor.
      all: apply typeinfer_sound.
      all: try rewrite q1; try rewrite q2.
      all: constructor.
    + destruct typeinfer eqn:q1 in p.
      2: contradiction.
      destruct typeinfer eqn:q2 in p.
      2: contradiction.
      constructor.
      all: apply typeinfer_sound.
      all: try rewrite q1; try rewrite q2.
      all: constructor.
Qed.

Fixpoint usecheck_complete {E Δ Δ'} (p: sE Δ E Δ'):
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
    2: {
      destruct eq_var.
      2: contradiction.
      auto.
    }
    induction H.
    all: cbn.
    * destruct eq_var.
      2: contradiction.
      auto.
    * destruct eq_var.
      1: subst; contradiction.
      rewrite IHlmem.
      auto.
    * destruct eq_var.
      2: contradiction.
      destruct eq_var.
      2: contradiction.
      reflexivity.
  - destruct p.
    all: cbn.
    all: try rewrite (usecheck_complete _ _ _ H).
    all: try rewrite (useinfer_complete _ _ _ p).
    all: try rewrite (useinfer_complete _ _ _ p1).
    all: try rewrite (useinfer_complete _ _ _ p2).
    all: auto.
    destruct eq_usage.
    2: contradiction.
    reflexivity.
Qed.

Fixpoint typecheck_complete {X Γ E t} (p: check X Γ E t):
  typecheck X Γ E = Some t
with typeinfer_complete {X Γ c} (p: infer X Γ c):
  typeinfer X Γ c = true.
Proof using.
  - destruct p.
    all: cbn.
    all: try rewrite (typecheck_complete _ _ _ _ p).
    all: try rewrite (typecheck_complete _ _ _ _ p1).
    all: try rewrite (typecheck_complete _ _ _ _ p2).
    all: try rewrite (typeinfer_complete _ _ _ H).
    all: auto.
    + rewrite H.
      destruct eq_type.
      2: contradiction.
      reflexivity.
  - destruct p.
    all: cbn.
    all: try rewrite (typeinfer_complete _ _ _ p).
    all: try rewrite (typeinfer_complete _ _ _ p1).
    all: try rewrite (typeinfer_complete _ _ _ p2).
    all: try rewrite (typecheck_complete _ _ _ _ H).
    all: try rewrite (typecheck_complete _ _ _ _ H0).
    all: auto.
    + rewrite H.
      destruct eq_type.
      2: contradiction.
      reflexivity.
    + destruct eq_type.
      2: contradiction.
      reflexivity.
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

Definition eq_subst (x y: subst): {x = y} + {x ≠ y}.
Proof.
Admitted.

Fixpoint verify (T: theory) ρ c: list subst :=
  match c with
  | c_relation _ _ => []

  | c_unify E E' =>
      do ρ1 |- v1 ← search T ρ E ;
      do ρ2 |- v2 ← search T ρ1 E' ;
      if eq_intro v1 v2
      then
        [ρ2]
      else
        []

  | c_true => [ρ]
  | c_false => []

  | c_and c c' =>
      do ρ1 ← verify T ρ c ;
      verify T ρ1 c'
  | c_or c c' =>
      verify T ρ c ++ verify T ρ c'
  end%list
with search T ρ E: list span :=
  match E with
  | E_var x => if take x ρ is Some (v, ρ') then [ρ' |- v] else []

  | E_function f E =>
      do ρ' |- v ← search T ρ E ;
      [ρ' |- v_function f v]

  | E_tt => [ρ |- v_tt]
  | E_fanout E E' =>
      do ρ1 |- v1 ← search T ρ E ;
      do ρ2 |- v2 ← search T ρ1 E' ;
      [ρ2 |- v_fanout v1 v2]

  | E_match_fanout x t1 y t2 c =>
      do a ← generate t1 ;
      do b ← generate t2 ;
      do ρ2 ← verify T ((y, b) :: (x , a) :: ρ) c ;
      if ρ2 is (y', _) :: (x', _) :: ρ2'
      then
        match eq_var x x', eq_var y y' with
        | left _, left _ =>
            [ρ2' |- v_fanout a b]
        | _, _ => []
        end
      else
        []

  | E_dup E =>
      do ρ' |- v ← search T ρ E ;
      [ρ' |- v_fanout v v]

  | E_del E =>
      do ρ' |- _ ← search T ρ E ;
      [ρ' |- v_tt]

  | E_epsilon x τ c =>
      do v ← generate τ ;
      do ρ1 ← verify T ((x, v) :: ρ) c ;
      if ρ1 is (x', _) :: ρ1'
      then
        if eq_var x x'
        then
          [ρ1' |- v]
        else
          []
      else
        []
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

Theorem verify_complete {T ρ c ρ'}:
  produces T ρ c ρ' →
  List.In ρ' (verify T ρ c)
with search_complete {T ρ E v ρ'}:
  accepts T ρ E v ρ' →
  List.In ((ρ' |- v)) (search T ρ E).
Proof using.
  Open Scope list.
  - intro q.
    destruct q.
    all: cbn.
    + admit.
    + left.
      reflexivity.
    + admit.
    + admit.
    + admit.
  - admit.
Admitted.

Theorem verify_sound {T ρ c}:
  List.Forall (produces T ρ c) (verify T ρ c)
with search_sound {T ρ E}:
  List.Forall (λ '(p' |- v), accepts T ρ E v p') (search T ρ E).
Proof using.
  Open Scope list.
  - destruct c.
    all: cbn.
    + left.
    + induction (search_sound T ρ E).
      1: left.
      cbn.
      destruct x.
      apply Forall_mon.
      2: eauto.
      clear IHf.
      induction (search_sound T ρ0 E').
      1: left.
      cbn.
      destruct x.
      apply Forall_mon.
      2: eauto.
      clear IHf0.
      destruct eq_intro.
      2: left.
      constructor.
      2: constructor.
      subst.
      econstructor.
      all: eauto.
    + constructor.
      2: constructor.
      constructor.
    + constructor.
    + induction (verify_sound T ρ c1).
      1: left.
      cbn.
      apply Forall_mon.
      2: auto.
      clear IHf.
      induction (verify_sound T x c2).
      1: left.
      cbn.
      constructor.
      2: eauto.
      econstructor.
      all: eauto.
    + apply Forall_mon.
      * induction (verify_sound T ρ c1).
        1: left.
        constructor.
        2: eauto.
        constructor.
        auto.
      * induction (verify_sound T ρ c2).
        1: left.
        constructor.
        2: eauto.
        apply produces_or_inr.
        auto.
  - destruct E.
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
    + induction (search_sound T ρ E).
      1: left.
      cbn.
      apply Forall_mon.
      2: eauto.
      clear IHf0.
      destruct x.
      constructor.
      2: left.
      constructor.
      auto.
    + induction (generate τ).
      1: left.
      cbn.
      apply Forall_mon.
      2: eauto.
      clear IHl.
      induction (verify_sound T ((x, a) :: ρ) c).
      1: left.
      apply Forall_mon.
      2: auto.
      destruct x0.
      1: left.
      destruct p.
      destruct eq_var.
      2: left.
      subst.
      constructor.
      2: left.
      econstructor.
      all: eauto.
    + constructor.
      2: left.
      constructor.
    + induction (search_sound T ρ E1).
      1: left.
      cbn.
      apply Forall_mon.
      2: eauto.
      destruct x.
      induction (search_sound T ρ0 E2).
      1: left.
      cbn.
      apply Forall_mon.
      2: eauto.
      clear IHf0.
      destruct x.
      constructor.
      2: left.
      econstructor.
      all: eauto.
    + induction (generate τ1).
      1: left.
      cbn.
      apply Forall_mon.
      2: eauto.
      clear IHl.
      induction (generate τ2).
      1: left.
      cbn.
      apply Forall_mon.
      2: eauto.
      clear IHl0.
      induction (verify_sound T ((y, a0) :: (x, a) :: ρ) c).
      all: cbn.
      all: try left.
      apply Forall_mon.
      all: eauto.
      clear IHf.
      destruct x0.
      1: left.
      destruct p.
      destruct x0.
      all: try left.
      destruct p.
      destruct eq_var.
      all: try left.
      subst.
      destruct eq_var.
      all: try left.
      subst.
      constructor.
      econstructor.
      all: eauto.
    + induction (search_sound T ρ E).
      1: left.
      cbn.
      apply Forall_mon.
      2: auto.
      destruct x.
      constructor.
      2: left.
      constructor.
      auto.
    + induction (search_sound T ρ E).
      1: left.
      cbn.
      apply Forall_mon.
      2: auto.
      destruct x.
      constructor.
      2: left.
      econstructor.
      eauto.
Qed.

Definition useonce Γ u: usage := List.map (λ '(x, t), (x, u)) Γ.

Definition oftype X Γ t :=
  { E | typecheck X Γ E = Some t ∧
          Bool.Is_true (if usecheck (useonce Γ u_unused) E is Some Δ
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
