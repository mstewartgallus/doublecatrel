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

    | E_epsilon x c =>
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

    | E_match_tt c => useinfer Δ c

    | E_match_fanout x y c =>
        do ' ((y', u_used) :: (x', u_used) :: Δ') ← useinfer ((y, u_unused) :: (x, u_unused) :: Δ) c ;
        match eq_var x x', eq_var y y' with
        | left _, left _ => Some Δ'
        | _, _ => None
        end

    | E_dup E => usecheck Δ E
    | E_del E _ => usecheck Δ E
    end
      %list
  with useinfer Δ c: option usage :=
    match c with
    | c_relation _ E => usecheck Δ E

    | c_unify E E' _ =>
        do Δ1 ← usecheck Δ E ;
        usecheck Δ1 E'

    | c_false => Some Δ

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

  Function typecheck (X: sorts) F R Γ E τ: bool :=
    match E, τ with
    | E_var x, _ =>
        if Assoc.find x Γ is Some τ'
        then
          if eq_type τ τ' then true else false
        else
          false

    | E_function f E, t_var A =>
        if Assoc.find f F is Some (τ, A')
        then
          (if eq_var A A' then true else false)
          && typecheck X F R Γ E τ
        else
          false

    | E_tt, t_unit => true
    | E_fanout E E', τ1 * τ2 => typecheck X F R Γ E τ1 && typecheck X F R Γ E' τ2

    | E_match_tt c, t_unit => typeinfer X F R Γ c
    | E_match_fanout x y c, τ1 * τ2 => typeinfer X F R ((y, τ2) :: (x, τ1) :: Γ) c

    | E_dup E, τ * τ' =>
        (if eq_type τ τ' then true else false)
        && typecheck X F R Γ E τ

    | E_del E τ, t_unit => typecheck X F R Γ E τ

    | E_epsilon x c, t_var A =>
        (if Assoc.find A X is Some tt then true else false)
        && typeinfer X F R ((x, t_var A) :: Γ) c
    | _, _ => false
    end %bool
  with typeinfer X F R Γ c: bool :=
    match c with
    | c_relation Rv E =>
        if Assoc.find Rv R is Some τ
        then
          typecheck X F R Γ E τ
        else
          false

    | c_unify E E' τ => typecheck X F R Γ E τ && typecheck X F R Γ E' τ

    | c_false => true
    | c_or c c' => typeinfer X F R Γ c && typeinfer X F R Γ c'
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
    + constructor.
      eauto.
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

Fixpoint typecheck_sound {X F R Γ E τ} {struct E}:
  Bool.Is_true (typecheck X F R Γ E τ) → check X F R Γ E τ
with
typeinfer_sound {X F R Γ c} {struct c}:
  Bool.Is_true (typeinfer X F R Γ c) → infer X F R Γ c.
Proof using.
  - destruct E.
    all: cbn.
    all: intros p.
    all: try contradiction.
    + destruct Assoc.find eqn:q1.
      2: contradiction.
      destruct eq_type.
      2: contradiction.
      subst.
      constructor.
      eauto.
    + destruct τ.
      all: try contradiction.
      destruct Assoc.find eqn:q1 in p.
      all: try contradiction.
      destruct p0.
      destruct eq_var in p.
      2: contradiction.
      subst.
      econstructor.
      all: eauto.
    + destruct τ.
      all: try contradiction.
      destruct Assoc.find eqn:q.
      2: contradiction.
      destruct u.
      constructor.
      all: eauto.
    + destruct τ.
      all: try contradiction.
      constructor.
    + destruct τ.
      all: try contradiction.
      destruct typecheck eqn:q1 in p.
      2: contradiction.
      constructor.
      all: apply typecheck_sound.
      all: try rewrite q1.
      all: try constructor.
      all: eauto.
    + destruct τ.
      all: try contradiction.
      constructor.
      eauto.
    + destruct τ.
      all: try contradiction.
      constructor.
      auto.
    + destruct τ.
      all: try contradiction.
      all: try destruct eq_type.
      all: try contradiction.
      subst.
      econstructor.
      eauto.
    + destruct τ.
      all: try contradiction.
      constructor.
      eauto.
  - destruct c.
    all: cbn.
    all: intros p.
    + destruct Assoc.find eqn:q1 in p.
      all: try contradiction.
      econstructor.
      all: eauto.
    + destruct typecheck eqn:q1 in p.
      2: contradiction.
      constructor.
      all: apply typecheck_sound.
      all: try rewrite q1.
      all: eauto.
      constructor.
    + constructor.
    + destruct typeinfer eqn:q1 in p.
      2: contradiction.
      constructor.
      all: apply typeinfer_sound.
      all: try rewrite q1.
      all: try constructor.
      eauto.
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

Fixpoint typecheck_complete {X F R Γ E τ} (p: check X F R Γ E τ):
  typecheck X F R Γ E τ = true
with typeinfer_complete {X F R Γ c} (p: infer X F R Γ c):
  typeinfer X F R Γ c = true.
Proof using.
  - destruct p.
    all: cbn.
    all: try rewrite (typecheck_complete _ _ _ _ _ _ p).
    all: try rewrite (typecheck_complete _ _ _ _ _ _ p1).
    all: try rewrite (typecheck_complete _ _ _ _ _ _ p2).
    all: try rewrite (typeinfer_complete _ _ _ _ _ H).
    all: try rewrite H.
    all: auto.
    all: try destruct eq_type.
    all: try destruct eq_var.
    all: eauto.
    destruct Assoc.find.
    2: discriminate.
    inversion H.
    subst.
    destruct eq_var.
    2: contradiction.
    cbn.
    eauto.
  - destruct p.
    all: cbn.
    all: try rewrite (typeinfer_complete _ _ _ _ _ p).
    all: try rewrite (typeinfer_complete _ _ _ _ _ p1).
    all: try rewrite (typeinfer_complete _ _ _ _ _ p2).
    all: try rewrite (typecheck_complete _ _ _ _ _ _ H).
    all: try rewrite (typecheck_complete _ _ _ _ _ _ H0).
    all: auto.
    destruct Assoc.find.
    2: discriminate.
    inversion H.
    subst.
    eauto.
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

  | c_unify E E' τ =>
      do v ← generate τ ;
      do ρ1 ← search T ρ E v ;
      search T ρ1 E' v

  | c_false => []
  | c_or c c' => verify T ρ c ++ verify T ρ c'
  end%list
with search T ρ E v: list subst :=
  match E, v with
  | E_var x, _ => if take x ρ is Some (v', ρ')
                  then
                    if eq_intro v v'
                    then
                      [ρ']
                    else
                      []
                  else
                    []

  | E_function f E, v_function f' v =>
      if eq_var f f' then search T ρ E v else []

  | E_tt, v_tt => [ρ]

  | E_fanout E E', v_fanout v1 v2 =>
      do ρ1 ← search T ρ E v1 ;
      search T ρ1 E' v2

  | E_match_tt c, v_tt => verify T ρ c

  | E_match_fanout x y c, v_fanout v1 v2 =>
      do ρ2 ← verify T ((y, v2) :: (x , v1) :: ρ) c ;
      if ρ2 is (y', _) :: (x', _) :: ρ2'
      then
        match eq_var x x', eq_var y y' with
        | left _, left _ => [ρ2']
        | _, _ => []
        end
      else
        []

  | E_dup E, v_fanout v1 v2 =>
      if eq_intro v1 v2
      then
        search T ρ E v1
      else
        []

  | E_del E τ, v_tt =>
      do v ← generate τ ;
      search T ρ E v

  | E_epsilon x c, v =>
      do ρ1 ← verify T ((x, v) :: ρ) c ;
      if ρ1 is (x', _) :: ρ1'
      then
        if eq_var x x'
        then
          [ρ1']
        else
          []
      else
        []
  | _, _ => []
  end%list %bool.

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
  List.In ρ' (search T ρ E v).
Proof using.
  Open Scope list.
  - intro q.
    destruct q.
    all: cbn.
    + admit.
    + admit.
    + admit.
  - admit.
Admitted.

Theorem verify_sound {T ρ c}:
  List.Forall (produces T ρ c) (verify T ρ c)
with search_sound {T ρ E v}:
  List.Forall (λ p', accepts T ρ E v p') (search T ρ E v).
Proof using.
  Open Scope list.
  - destruct c.
    all: cbn.
    + left.
    + induction (generate τ).
      1: left.
      cbn.
      apply Forall_mon.
      all: eauto.
      induction (search_sound T ρ E a).
      1: left.
      apply Forall_mon.
      all: eauto.
      clear IHf.
      induction (search_sound T x E' a).
      1: left.
      constructor.
      all: eauto.
      econstructor.
      all: eauto.
    + left.
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
      destruct eq_intro.
      2: left.
      constructor.
      2: constructor.
      constructor.
      subst.
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
    + destruct v.
      all: try left.
      destruct eq_var.
      2: left.
      subst.
      induction (search_sound T ρ E v).
      1: left.
      constructor.
      all: eauto.
      constructor.
      eauto.
    + induction (verify_sound T ((x, v) :: ρ) c).
      1: left.
      cbn.
      apply Forall_mon.
      all: eauto.
      destruct x0.
      all: cbn.
      1: left.
      destruct p.
      destruct eq_var.
      2: left.
      constructor.
      2: constructor.
      subst.
      econstructor.
      eauto.
    + destruct v.
      all: try left.
      all: try repeat constructor.
    + destruct v.
      all: try left.
      induction (search_sound T ρ E1 v1).
      1: left.
      apply Forall_mon.
      all: eauto.
      clear IHf.
      induction (search_sound T x E2 v2).
      1: left.
      constructor.
      2: eauto.
      econstructor.
      all: eauto.
    + destruct v.
      all: try left.
      induction (verify_sound T ρ c).
      1: left.
      constructor.
      2: eauto.
      econstructor.
      auto.
    + destruct v.
      all: try left.
      induction (verify_sound T ((y, v2) :: (x, v1) :: ρ) c).
      all: cbn.
      all: try left.
      apply Forall_mon.
      all: eauto.
      clear IHf.
      destruct x0.
      1: left.
      destruct p.
      destruct x0.
      1: left.
      destruct p.
      destruct eq_var.
      2: left.
      destruct eq_var.
      2: left.
      constructor.
      2: eauto.
      subst.
      econstructor.
      eauto.
    + destruct v.
      all: try left.
      destruct eq_intro.
      2: left.
      subst.
      induction (search_sound T ρ E v2).
      1: left.
      constructor.
      all: eauto.
      constructor.
      eauto.
    + destruct v.
      all: try left.
      induction (generate τ).
      1: left.
      cbn.
      apply Forall_mon.
      all: eauto.
      clear IHl.
      induction (search_sound T ρ E a).
      1: left.
      constructor.
      all: eauto.
      econstructor.
      eauto.
Qed.

Definition useonce Γ u: usage := List.map (λ '(x, t), (x, u)) Γ.

Definition oftype X F R Γ t :=
  { E |  Bool.Is_true (typecheck X F R Γ E t && if usecheck (useonce Γ u_unused) E is Some Δ
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
