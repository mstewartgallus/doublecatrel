Require Import Blech.Spec.
Require Import Blech.SpecNotations.
Require Import Blech.Opaque.
Require Import Blech.OptionNotations.
Require Import Blech.Environment.
Require Import Blech.Category.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.SetoidClass.
Require Coq.Bool.Bool.
Require Coq.Lists.List.

Import IfNotations.

Require Import FunInd.

Implicit Type Γ: environment.
Implicit Type v: term.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types x y: var.
Implicit Type ρ: subst.

Function η t V :=
  match t with
  | t_var _ => v_neu V
  | t_unit => v_tt
  | t1 * t2 =>
      v_fanout (η t1 (V_fst V))  (η t2 (V_snd V))
  end.

Theorem η_preserve {t}:
  ∀ {Γ V},
  JV Γ V t →
  Γ ⊢ η t V in t.
Proof.
  induction t.
  all: cbn.
  all: intros ? ? q.
  - intros.
    constructor.
    auto.
  - constructor.
  - constructor.
    + eapply IHt1.
      econstructor.
      eauto.
    + eapply IHt2.
      econstructor.
      eauto.
Qed.

Function hsubst_expr v' x V :=
  match V with
  | V_var y => if eq_var x y then Some v' else None
  | V_fst V =>
      do v_fanout v1 _ ← hsubst_expr v' x V ;
      Some v1
  | V_snd V =>
      do v_fanout _ v2 ← hsubst_expr v' x V ;
      Some v2
  end.

Function hsubst_term v' x v :=
  match v with
  | v_tt => Some v_tt
  | v_fanout v1 v2 =>
      do v1' ← hsubst_term v' x v1 ;
      do v2' ← hsubst_term v' x v2 ;
      Some (v_fanout v1' v2')
  | v_neu V => hsubst_expr v' x V
  end.

Lemma hsubst_preserve_expr {v' x V}:
  ∀ {Γ t},
    Γ ⊢ v' in t →
  ∀ {t'},
    JV (cons (x, t) Γ) V t' →
    ∀ {vout}, hsubst_expr v' x V = Some vout →
    Γ ⊢ vout in t'.
Proof.
  functional induction (hsubst_expr v' x V).
  all: intros ? ? q ? p ? r.
  all: inversion p.
  all: subst.
  all: clear p.
  - inversion H1.
    all: subst.
    2: contradiction.
    inversion r.
    subst.
    auto.
  - inversion H1.
    all: subst.
    1: contradiction.
    inversion r.
  - inversion r.
    subst.
    clear r.
    assert (e0' := IHo _ _ q _ H1 _ e0).
    inversion e0'.
    subst.
    auto.
  - inversion r.
  - inversion r.
    subst.
    clear r.
    assert (e0' := IHo _ _ q _ H1 _ e0).
    inversion e0'.
    subst.
    auto.
  - inversion r.
Qed.

Lemma hsubst_preserve_term {v' x v}:
  ∀ {Γ t},
    Γ ⊢ v' in t →
  ∀ {t'},
    (x, t) :: Γ ⊢ v in t' →
    ∀ {vout}, hsubst_term v' x v = Some vout →
    Γ ⊢ vout in t'.
Proof.
  functional induction (hsubst_term v' x v).
  all: intros ? ? q ? p ? r.
  all: inversion p.
  all: subst.
  all: clear p.
  - inversion r.
    all: subst.
    constructor.
  - inversion r.
    all: subst.
    constructor.
    all: eauto.
  - inversion r.
  - inversion r.
  - eapply hsubst_preserve_expr.
    all: eauto.
Qed.

Lemma map_expr {Γ Γ'}:
  (∀ x t, mem x t Γ → mem x t Γ') →
  ∀ {V t}, JV Γ V t → JV Γ' V t.
Proof using.
  intros ? ? ? p.
  induction p.
  all: econstructor.
  all: eauto.
Qed.

Lemma map_term {Γ Γ'}:
  (∀ x t, mem x t Γ → mem x t Γ') →
  ∀ {v t}, Γ ⊢ v in t → Γ' ⊢ v in t.
Proof.
  intros ? ? ? p.
  induction p.
  all: econstructor.
  all: eauto.
  eapply map_expr.
  all: eauto.
Qed.

Lemma hsubst_expr_total {V}:
  ∀ {x t' t},
    JV (cons (x, t) nil) V t' →
  ∀ {v' t''},
  (x, t'') :: nil ⊢ v' in t →
  ∃ vout, hsubst_expr v' x V = Some vout.
Proof.
  induction V.
  all: cbn.
  all: intros ? ? ? q.
  all: inversion q.
  all: clear q.
  all: subst.
  all: intros ? ? p.
  - inversion H1.
    all: subst.
    + destruct eq_var.
      2: contradiction.
      eexists.
      eauto.
    + destruct eq_var.
      1: subst; contradiction.
      inversion H6.
  - destruct (IHV _ _ _ H1 _ _ p) as [? q1].
    rewrite q1.
    eassert (H1' := hsubst_preserve_expr p _ q1).
    Unshelve.
    3: {
      eapply (map_expr Environment.shadow).
      eapply H1.
    }
    destruct x0.
    all: inversion H1'.
    eexists.
    eauto.
  - destruct (IHV _ _ _ H1 _ _ p) as [? q1].
    rewrite q1.
    eassert (H1' := hsubst_preserve_expr p _ q1).
    Unshelve.
    3: {
      eapply (map_expr Environment.shadow).
      eapply H1.
    }
    destruct x0.
    all: inversion H1'.
    eexists.
    eauto.
Qed.

Lemma hsubst_term_total {v}:
  ∀ {x t' t},
    (x, t) :: nil ⊢ v in t' →
  ∀ {v' t''},
  (x, t'') :: nil ⊢ v' in t →
  ∃ vout, hsubst_term v' x v = Some vout.
Proof.
  induction v.
  all: cbn.
  all: intros ? ? ? q.
  all: inversion q.
  all: clear q.
  all: subst.
  all: intros ? ? p.
  - eexists.
    eauto.
  - destruct (IHv1 _ _ _ H2 _ _ p) as [? q1].
    destruct (IHv2 _ _ _ H4 _ _ p) as [? q2].
    rewrite q1, q2.
    eexists.
    eauto.
  - eapply hsubst_expr_total.
    all: eauto.
Qed.

Function typeinfer Γ V :=
  match V with
  | V_var x => find x Γ
  | V_fst V =>
      do t0 * _ ← typeinfer Γ V ;
      Some t0
  | V_snd V =>
      do _ * t1 ← typeinfer Γ V ;
      Some t1
  end.

Function typecheck Γ v t: bool :=
  match v, t with
  | v_tt, t_unit => true
  | v_fanout v0 v1, t1 * t2 =>
      typecheck Γ v0 t1 && typecheck Γ v1 t2
  | v_neu v, t_var _ =>
      if typeinfer Γ v is Some t'
      then if eq_type t t' then true else false
      else false
  | _, _ => false
  end %bool.

Function elim x s (V: expr) :=
  match V with
  | V_var y => if eq_var x y then Some s else None
  | V_fst V =>
      do v_fanout a _ ← elim x s V ;
      Some a
  | V_snd V =>
      do v_fanout _ a ← elim x s V ;
      Some a
  end.

Function intro x s v :=
  match v with
  | v_tt => Some v_tt
  | v_fanout v0 v1 =>
      do v0' ← intro x s v0 ;
      do v1' ← intro x s v1 ;
      Some (v_fanout v0' v1')
  | v_neu V => elim x s V
  end.

Lemma elim_sound {x s V}:
  ∀ {v'}, elim x s V = Some v' →
  hsubstV x s V v'.
Proof.
  functional induction (elim x s V).
  all: try discriminate.
  all: intros ? p.
  all: inversion p.
  all: subst.
  - constructor.
  - econstructor.
    eauto.
  - econstructor.
    eauto.
Qed.

Lemma intro_sound {x s v}:
  ∀ {v'}, intro x s v = Some v' →
  hsubstv x s v v'.
Proof.
  functional induction (intro x s v).
  all: try discriminate.
  all: intros ? p.
  all: inversion p.
  all: subst.
  - constructor.
  - constructor.
    all: auto.
  - constructor.
    apply elim_sound.
    auto.
Qed.

Lemma elim_complete {x s V v'}:
  hsubstV x s V v' →
  elim x s V = Some v'.
Proof.
  intro p.
  induction p.
  all: cbn.
  - destruct eq_var.
    2: contradiction.
    auto.
  - rewrite IHp.
    auto.
  - rewrite IHp.
    auto.
Qed.

Lemma intro_complete {x s v v'}:
  hsubstv x s v v' →
  intro x s v = Some v'.
Proof.
  intro p.
  induction p.
  all: cbn.
  - auto.
  - rewrite IHp1, IHp2.
    auto.
  - apply elim_complete.
    auto.
Qed.

Function lookup x ρ: option normal :=
  if ρ is ((y, t) :: ρ')%list
  then
    if eq_var x y
    then Some t
    else lookup x ρ'
  else None.


Fixpoint typeinfer_sound {Γ V t}: typeinfer Γ V = Some t → JV Γ V t.
Proof using .
  - intros p.
    destruct V.
    all: cbn.
    + cbn in p.
      constructor.
      apply find_sound.
      auto.
    + cbn in p.
      destruct typeinfer eqn:q.
      2: discriminate.
      destruct t0.
      all: try discriminate.
      inversion p.
      subst.
      econstructor.
      apply typeinfer_sound.
      eauto.
    + cbn in p.
      destruct typeinfer eqn:q.
      2: discriminate.
      destruct t0.
      all: try discriminate.
      inversion p.
      subst.
      econstructor.
      apply typeinfer_sound.
      eauto.
Qed.

Fixpoint typecheck_sound {Γ v t}:
  Bool.Is_true (typecheck Γ v t) → Γ ⊢ v in t.
  - intros p.
    destruct v.
    all: cbn.
    + destruct t.
      all: try contradiction.
      constructor.
    + destruct t.
      all: try contradiction.
      cbn in p.
      destruct typecheck eqn:q1.
      2: contradiction.
      destruct typecheck eqn:q2 in p.
      2: contradiction.
      constructor.
      * apply typecheck_sound.
        rewrite q1.
        apply I.
      * apply typecheck_sound.
        rewrite q2.
        apply I.
    + cbn in p.
      destruct t.
      all: try contradiction.
      destruct typeinfer eqn:q.
      all: try contradiction.
      destruct eq_type.
      all: try contradiction.
      subst.
      constructor.
      apply typeinfer_sound.
      auto.
Qed.

Fixpoint typeinfer_complete {Γ V t} (p: JV Γ V t): typeinfer Γ V = Some t.
Proof using .
  - destruct p.
    all: cbn in *.
    + apply find_complete.
      auto.
    + rewrite (typeinfer_complete Γ V _ p).
      auto.
    + rewrite (typeinfer_complete Γ V _ p).
      auto.
Qed.

Fixpoint typecheck_complete {Γ v t} (p: Γ ⊢ v in t): typecheck Γ v t = true.
Proof using .
  destruct p.
  all: cbn in *.
  all: auto.
  all: try rewrite typecheck_complete.
  all: try rewrite typecheck_complete.
  all: auto.
  rewrite (typeinfer_complete H).
  destruct eq_tyvar.
  2: contradiction.
  auto.
Qed.

Lemma lookup_sound {x ρ}:
  ∀ {N}, lookup x ρ = Some N → memp x N ρ.
Proof using .
  functional induction (lookup x ρ).
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: constructor.
  all: auto.
Qed.

Lemma lookup_complete {x ρ N}:
  memp x N ρ → lookup x ρ = Some N.
Proof using .
  intro p.
  induction p.
  all: cbn.
  - destruct eq_var.
    2: contradiction.
    reflexivity.
  - destruct eq_var.
    1: contradiction.
    auto.
Qed.

Definition oftype Γ t := { v | Bool.Is_true (typecheck Γ v t) }.

Definition equiv {Γ t} (p q: oftype Γ t): Prop := proj1_sig p = proj1_sig q.

Instance equiv_Reflexive Γ t: Reflexive (@equiv Γ t).
Proof.
  unfold Reflexive.
  reflexivity.
Qed.

Instance equiv_Transitive Γ t: Transitive (@equiv Γ t).
Proof.
  unfold Transitive, equiv.
  intros ? ? ? f g.
  rewrite f, g.
  auto.
Qed.

Instance equiv_Symmetric Γ t: Symmetric (@equiv Γ t).
Proof.
  unfold Symmetric, equiv.
  intros ? ? f.
  auto.
Qed.

Instance equiv_Equivalence Γ t: Equivalence (@equiv Γ t) := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid Γ t: Setoid (oftype Γ t) := {
    equiv := @equiv Γ t ;
}.

Instance subrelation_equiv_eq {Γ t}: subrelation (@equiv Γ t) (@eq _).
Proof.
  intros v v'.
  destruct v as [? p], v' as [? p'].
  cbn.
  unfold equiv.
  cbn.
  intros r.
  subst.
  replace p with p'.
  1: auto.
  generalize dependent p.
  generalize dependent p'.
  destruct typecheck.
  2: contradiction.
  cbn.
  intros.
  destruct p', p.
  auto.
Qed.
