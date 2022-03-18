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

Module ProofTree.
  Inductive Jv: Set :=
  | Jv_var Γ x
  | Jv_tt Γ
  | Jv_fanout: Jv → Jv → Jv
  | Jv_fst: Jv → Jv
  | Jv_snd: Jv → Jv.

  Function envof (v: Jv): environment :=
    match v with
    | Jv_var Γ _ => Γ
    | Jv_tt Γ => Γ
    | Jv_fanout p1 _ => envof p1
    | Jv_fst p => envof p
    | Jv_snd p => envof p
    end.

  Function termof (v: Jv): term :=
    match v with
    | Jv_var _ x => v_var x
    | Jv_tt _ => v_tt
    | Jv_fst p => v_fst (termof p)
    | Jv_snd p => v_snd (termof p)
    | Jv_fanout p1 p2 => v_fanout (termof p1) (termof p2)
    end.

  #[local]
  Definition unknown_type := opaque (λ _: Jv, t_unit).


  Function typeof (v: Jv): type :=
    match v with
    | Jv_var Γ x => if find x Γ is Some t then t else unknown_type v
    | Jv_tt _ => t_unit
    | Jv_fst p => if typeof p is t * _ then t else unknown_type v
    | Jv_snd p => if typeof p is _ * t then t else unknown_type v
    | Jv_fanout p1 p2 => typeof p1 * typeof p2
    end.

  Definition asserts (v: Jv): Prop := envof v ⊢ termof v in typeof v.

  Notation "'test' p" := (match p with | left _ => true | right _ => false end) (at level 1).

  Function check (p: Jv): bool :=
    match p with
    | Jv_var Γ x =>
        if find x Γ is Some t then true else false
    | Jv_tt _ => true
    | Jv_fst p =>
        (if typeof p is _ * _ then true else false)
        && check p
    | Jv_snd p =>
        (if typeof p is _ * _ then true else false)
        && check p
    | Jv_fanout p1 p2 =>
        test (eq_environment (envof p1) (envof p2))
        && check p1
        && check p2
    end %bool.

  Lemma check_sound (p: Jv): Bool.Is_true (check p) → asserts p.
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
    - constructor.
    - rewrite e0.
      rewrite e0 in IHb.
      destruct (check p0).
      2: contradiction.
      econstructor.
      eauto.
    - rewrite e0.
      rewrite e0 in IHb.
      destruct (check p0).
      2: contradiction.
      econstructor.
      eauto.
    - rewrite <- _x in IHb0.
      destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      constructor.
      all: auto.
  Qed.

  Lemma check_complete {Γ v t}:
    Γ ⊢ v in t →
             ∃ p,
               Γ = envof p ∧
               v = termof p ∧
               t = typeof p ∧
               Bool.Is_true (check p).
  Proof.
    intro q.
    induction q.
    all: cbn.
    - exists (Jv_var Γ x).
      cbn.
      rewrite (find_complete H).
      all: repeat split; auto.
    - exists (Jv_tt Γ).
      cbn.
      all: repeat split; auto.
    - destruct IHq1 as [p1 [? [? []]]].
      destruct IHq2 as [p2 [? [? []]]].
      subst.
      exists (Jv_fanout p1 p2).
      cbn.
      destruct (check p1).
      2: contradiction.
      destruct (check p2).
      2: contradiction.
      rewrite H3.
      all: repeat split; auto.
      destruct eq_environment.
      2: contradiction.
      cbn.
      auto.
    - destruct IHq as [p1 [? [? []]]].
      subst.
      exists (Jv_fst p1).
      cbn.
      rewrite <- H1.
      destruct (check p1).
      2: contradiction.
      all: repeat split; auto.
    - destruct IHq as [p1 [? [? []]]].
      subst.
      exists (Jv_snd p1).
      cbn.
      rewrite <- H1.
      destruct (check p1).
      2: contradiction.
      all: repeat split; auto.
  Qed.

  Function elaborate Γ v: option Jv :=
    match v with
    | v_var x =>
        do _ ← find x Γ ;
        Some (Jv_var Γ x)
    | v_tt => Some (Jv_tt Γ)
    | v_fst v =>
        do p ← elaborate Γ v ;
        if typeof p is _ * _
        then
          Some (Jv_fst p)
        else
          None
    | v_snd v =>
        do p ← elaborate Γ v ;
        if typeof p is _ * _
        then
          Some (Jv_snd p)
        else
          None
    | v_fanout v0 v1 =>
        do v0' ← elaborate Γ v0 ;
        do v1' ← elaborate Γ v1 ;
        Some (Jv_fanout v0' v1')
    end.

  Lemma termof_elaborate {Γ v p}: elaborate Γ v = Some p → termof p = v.
  Proof.
    generalize dependent p.
    functional induction (elaborate Γ v).
    all: intros ? q.
    all: inversion q.
    all: subst.
    all: cbn.
    all: auto.
    - rewrite IHo.
      all: auto.
    - rewrite IHo.
      all: auto.
    - rewrite IHo, IHo0.
      all: auto.
  Qed.

  Lemma envof_elaborate {Γ v p}: elaborate Γ v = Some p → envof p = Γ.
  Proof.
    generalize dependent p.
    functional induction (elaborate Γ v).
    all: intros ? q.
    all: inversion q.
    all: subst.
    all: cbn.
    all: auto.
  Qed.

  Definition elaborate_sound {Γ v p}:
    elaborate Γ v = Some p → Bool.Is_true (check p).
  Proof.
    generalize dependent p.
    functional induction (elaborate Γ v).
    all: cbn.
    all: intros ? q.
    all: inversion q.
    all: subst.
    - cbn.
      rewrite e0.
      cbv.
      auto.
    - cbn.
      auto.
    - cbn.
      rewrite e1.
      cbn.
      assert (IHo' := IHo _ e0).
      auto.
    - cbn.
      rewrite e1.
      cbn.
      assert (IHo' := IHo _ e0).
      auto.
    - cbn.
      assert (IHo' := IHo _ e0).
      assert (IHo0' := IHo0 _ e1).
      rewrite (envof_elaborate e0).
      rewrite (envof_elaborate e1).
      destruct eq_environment.
      2: contradiction.
      cbn.
      destruct (check v0').
      2: contradiction.
      destruct (check v1').
      2: contradiction.
      auto.
  Qed.
End ProofTree.

Function typecheck Γ v :=
  match v with
  | v_var x => find x Γ
  | v_tt => Some t_unit
  | v_fst v =>
      do t0 * _ ← typecheck Γ v ;
      Some t0
  | v_snd v =>
      do _ * t1 ← typecheck Γ v ;
      Some t1
  | v_fanout v0 v1 =>
      do t0 ← typecheck Γ v0 ;
      do t1 ← typecheck Γ v1 ;
      Some (t0 * t1)
  end.

Function eval v :=
  match v with
  | v_var _ => None
  | v_tt => Some N_tt
  | v_fst v =>
      do N_fanout a _ ← eval v ;
      Some a
  | v_snd v =>
      do N_fanout _ a ← eval v ;
      Some a
  | v_fanout v0 v1 =>
      do v0' ← eval v0 ;
      do v1' ← eval v1 ;
      Some (N_fanout v0' v1')
  end.

Theorem typecheck_sound:
  ∀ {Γ v t}, typecheck Γ v = Some t → Γ ⊢ v in t.
Proof using .
  intros Γ v.
  functional induction (typecheck Γ v).
  all: cbn.
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
  apply find_sound.
  auto.
Qed.

Theorem typecheck_complete:
  ∀ {Γ v t}, Γ ⊢ v in t → typecheck Γ v = Some t.
Proof using .
  intros Γ ? ? p.
  induction p.
  all: cbn.
  all: cbn in *.
  all: try (destruct (typecheck Γ v) as [[]|]).
  all: try (destruct (typecheck Γ v1)).
  all: try (destruct (typecheck Γ v2)).
  all: auto.
  all: try inversion IHp.
  all: subst.
  all: try inversion IHp1.
  all: subst.
  all: try inversion IHp2.
  all: subst.
  all: auto.
  apply find_complete.
  auto.
Qed.

Theorem eval_sound:
  ∀ {v N}, eval v = Some N → v ⇓ N.
Proof using.
  intros v.
  functional induction (eval v).
  all: intros ? p.
  all: inversion p.
  all: subst.
  all: econstructor.
  all: eauto.
Qed.

Theorem eval_complete:
  ∀ {v N}, v ⇓ N → eval v = Some N.
Proof using.
  intros ? ? p.
  induction p.
  all: cbn.
  all: try rewrite IHp.
  all: try rewrite IHp1.
  all: try rewrite IHp2.
  all: reflexivity.
Qed.

Theorem big_preserve:
  ∀ {v N},
    v ⇓ N →
    ∀ Γ t, Γ ⊢ v in t → Γ ⊢ N in t.
Proof using.
  intros v v' p.
  induction p.
  all: intros ? ? q.
  all: inversion q.
  all: subst.
  all: auto.
  - econstructor.
    all: eauto.
  - set (p' := IHp _ _ H1).
    inversion p'.
    subst.
    auto.
  - set (p' := IHp _ _ H1).
    inversion p'.
    subst.
    auto.
Qed.

Theorem big_unique:
  ∀ {v N N'},
    v ⇓ N → v ⇓ N' → N = N'.
Proof using.
  intros v N N' p q.
  set (p' := eval_complete p).
  set (q' := eval_complete q).
  rewrite p' in q'.
  inversion q'.
  auto.
Qed.

Theorem normalize:
  ∀ {v t},
   nil ⊢ v in t →
   ∃ N, v ⇓ N.
Proof using.
  intros v.
  induction v.
  all: intros ? p.
  all: inversion p.
  all: subst.
  - inversion H1.
  - exists N_tt.
    constructor.
  - destruct (IHv _ H1) as [v' s].
    set (vwf := big_preserve s _ _ H1).
    destruct v'.
    all: cbn in *.
    all: inversion vwf.
    subst.
    exists v'1.
    econstructor.
    eauto.
  - destruct (IHv _ H1) as [v' s].
    set (vwf := big_preserve s _ _ H1).
    destruct v'.
    all: cbn in *.
    all: inversion vwf.
    subst.
    exists v'2.
    econstructor.
    eauto.
  - destruct (IHv1 _ H2) as [v1' s1].
    destruct (IHv2 _ H4) as [v2' s2].
    exists (N_fanout v1' v2').
    constructor.
    all: auto.
Qed.

Lemma big_normal:
  ∀ {N}, N ⇓ N.
Proof using.
  intro N.
  induction N.
  all: cbn.
  all: constructor.
  all: auto.
Qed.

Definition oftype Γ A := { v | Γ ⊢ v in A }.

Lemma subst_var {x v}:
  subst_term (v_var x) x v = v.
Proof.
  induction v.
  all: cbn.
  all: auto.
  - destruct (eq_var x0 x).
    all: auto.
  - rewrite IHv.
    auto.
  - rewrite IHv.
    auto.
  - rewrite IHv1, IHv2.
    auto.
Qed.

Lemma subst_normal {v x N}: subst_term v x N = N.
Proof using.
  induction N.
  1: reflexivity.
  cbn.
  rewrite IHN1, IHN2.
  reflexivity.
Qed.

Lemma subst_preserve_minus:
  ∀ {Γ v' t x},
    minus x Γ ⊢ v' in t →
  ∀ {v t'},
    find x Γ = Some t →
    Γ ⊢ v in t' →
    minus x Γ ⊢ subst_term v' x v in t'.
Proof using.
  intros Γ v' t x p v.
  induction v.
  all: cbn.
  all: intros t' ? q.
  all: inversion q.
  all: subst.
  all: try (econstructor; eauto).
  clear q.
  assert (H2' := find_complete H2).
  clear H2.
  destruct eq_var.
  - subst.
    rewrite H in H2'.
    inversion H2'.
    subst.
    auto.
  - clear p H.
    constructor.
    apply find_sound.
    rewrite find_minus.
    all: auto.
Qed.

Lemma subst_preserve:
  ∀ {Γ v' t x},
    Γ ⊢ v' in t →
  ∀ {v t'},
    cons (x, t) Γ ⊢ v in t' →
    Γ ⊢ subst_term v' x v in t'.
Proof using.
  intros Γ v' t x p v.
  induction v.
  all: cbn.
  all: intros t' q.
  all: inversion q.
  all: subst.
  all: try (econstructor; eauto).
  destruct eq_var.
  - subst.
    inversion H1.
    2: contradiction.
    subst.
    auto.
  - inversion H1.
    1: contradiction.
    subst.
    constructor.
    auto.
Qed.

Lemma subst_assoc {x f g h}:
  subst_term (subst_term h x g) x f = subst_term h x (subst_term g x f).
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
    auto.
  - rewrite IHf.
    auto.
  - rewrite IHf1.
    rewrite IHf2.
    auto.
Qed.

Lemma msubst_normal {p N}: msubst p N = N.
Proof using.
  induction p.
  1: reflexivity.
  cbn.
  destruct a.
  rewrite subst_normal.
  auto.
Qed.

Lemma msubst_preserve:
  ∀ {p Γ v t},
    Jp p Γ →
    Γ ⊢ v in t →
    nil ⊢ msubst p v in t.
Proof using.
  intros p.
  induction p.
  all: cbn.
  all: intros.
  - inversion H.
    subst.
    auto.
  - destruct a.
    inversion H.
    subst.
    eapply IHp.
    2: eapply subst_preserve.
    all: eauto.
Qed.

Lemma msubst_fst {p}:
  ∀ {v}, msubst p (v_fst v) = v_fst (msubst p v).
Proof.
  induction p.
  all: cbn.
  1: auto.
  destruct a.
  intro.
  rewrite IHp.
  reflexivity.
Qed.

Lemma msubst_snd {p}:
  ∀ {v}, msubst p (v_snd v) = v_snd (msubst p v).
Proof.
  induction p.
  all: cbn.
  1: auto.
  destruct a.
  intro.
  rewrite IHp.
  reflexivity.
Qed.

Lemma msubst_fanout {p}:
  ∀ {v v'}, msubst p (v_fanout v v') = v_fanout (msubst p v) (msubst p v').
Proof.
  induction p.
  all: cbn.
  1: auto.
  destruct a.
  intros.
  rewrite IHp.
  reflexivity.
Qed.

Definition equiv {Γ t}: Relation_Definitions.relation (oftype Γ t) :=
  λ o o',
  ∀ p,
    Jp p Γ →
    ∃ N, (msubst p (proj1_sig o) ⇓ N) ∧ (msubst p (proj1_sig o') ⇓ N).

Instance equiv_Reflexive Γ t: Reflexive (@equiv Γ t).
Proof using.
  unfold equiv.
  intros [v p].
  cbn.
  intros σ ?.
  destruct (@normalize (msubst σ v) t).
  - eapply msubst_preserve.
    all: eauto.
  - exists x.
    split.
    all: auto.
Qed.

Instance equiv_Symmetric Γ t: Symmetric (@equiv Γ t).
Proof using.
  unfold equiv.
  intros [v p] [v' q].
  cbn.
  intros f σ r.
  destruct (f σ r).
  destruct H.
  exists x.
  split.
  all: auto.
Qed.

Instance equiv_Transitive Γ t: Transitive (@equiv Γ t).
Proof using.
  unfold equiv.
  intros [x p] [y q] [z r].
  cbn.
  intros f g σ u.
  destruct (f σ u), (g σ u).
  destruct H, H0.
  set (q' := big_unique H1 H0).
  repeat rewrite q' in *.
  exists x1.
  split.
  all: auto.
Qed.

Instance equiv_Equivalence Γ t: Equivalence (@equiv Γ t) := {
    Equivalence_Reflexive := _ ;
}.

Instance oftype_Setoid Γ t: Setoid (oftype Γ t) := {
    equiv := equiv ;
}.

Lemma map:
  ∀ {v t Γ Δ},
    (∀ x t, mem x t Γ → mem x t Δ) →
    Γ ⊢ v in t →
    Δ ⊢ v in t.
Proof.
  intro v.
  induction v.
  all: intros ? ? ? ? p.
  all: inversion p.
  all: subst.
  all: try econstructor.
  all: eauto.
Qed.

Definition linmap Γ Γ' := ∀ v t, Γ ⊢ v in t → Γ' ⊢ v in t.

Lemma map_mem {Γ Γ'}:
  linmap Γ Γ' →
  ∀ {x t}, mem x t Γ → mem x t Γ'.
Proof.
  unfold linmap.
  intros p.
  intros x t q.
  assert (q' := p _ _ (Jv_var _ _ _ q)).
  inversion q'.
  subst.
  auto.
Qed.

Definition shadow {v Γ x t0 t1 t2}:
  ((x, t0) :: Γ) ⊢ v in t2 → ((x, t0) :: (x, t1) :: Γ) ⊢ v in t2 :=
  map Environment.shadow.

Definition unshadow {v Γ x t0 t1 t2}:
  (x, t0) :: (x, t1) :: Γ ⊢ v in t2 → (x, t0) :: Γ ⊢ v in t2 :=
  map Environment.unshadow.

Module Dec.
  Inductive term {Γ: environment}: type → Set :=
  | v_var {t} (x: var): find x Γ = Some t → term t
  | v_tt: term t_unit
  | v_fst {t t'} (v: term (t * t')): term t
  | v_snd {t t'} (v: term (t * t')): term t'
  | v_fanout {t t'} (v: term t) (v': term t'): term (t * t').
  Arguments term: clear implicits.

  Import OptionNotations.

  Definition find_dec x Γ: option {t | find x Γ = Some t}.
  Proof.
    destruct (find x Γ).
    2: apply None.
    apply Some.
    exists t.
    auto.
  Defined.

  Fixpoint dec' Γ v: option { t & term Γ t } :=
    match v with
    | Spec.v_var x =>
        match find_dec x Γ with
        | Some p =>
            Some (existT (term Γ) (proj1_sig p) (@v_var _ (proj1_sig p) x (proj2_sig p)))
        | _ => None
        end
    | Spec.v_tt => Some (existT  (term Γ) t_unit v_tt)
    | Spec.v_fst v =>
        do existT _ (t0 * t1) v' ← dec' Γ v ;
        Some (existT _ t0 (v_fst v'))
    | Spec.v_snd v =>
        do existT _ (t0 * t1) v' ← dec' Γ v ;
        Some (existT (term Γ) t1 (v_snd v'))
    | Spec.v_fanout v v' =>
        do existT _ t0 v0 ← dec' Γ v ;
        do existT _ t1 v1 ← dec' Γ v' ;
        Some (existT (term Γ) (t0 * t1) (v_fanout v0 v1))
    end.

  Lemma dec_sound {Γ} v:
    typecheck Γ v = (do d ← dec' Γ v ;
                     Some (projT1 d)).
  Proof.
    induction v.
    all: cbn.
    all: auto.
    - destruct (find_dec x Γ) eqn:q.
      + cbn.
        destruct s.
        cbn.
        auto.
      + cbn.
        unfold find_dec in q.
        destruct (find x Γ).
        * discriminate.
        * auto.
    - rewrite IHv.
      destruct (dec' Γ v).
      2: auto.
      destruct s.
      cbn.
      destruct x.
      all: auto.
    - rewrite IHv.
      destruct (dec' Γ v).
      2: auto.
      destruct s.
      cbn.
      destruct x.
      all: auto.
    - rewrite IHv1.
      rewrite IHv2.
      destruct (dec' Γ v1).
      2: auto.
      destruct s.
      destruct (dec' Γ v2).
      2: auto.
      destruct s.
      cbn.
      auto.
  Defined.

  Definition dec {Γ} t v (p: typecheck Γ v = Some t): term Γ t.
  Proof.
    rewrite dec_sound in p.
    destruct (dec' Γ v).
    2: discriminate.
    destruct s.
    cbn in p.
    inversion p.
    subst.
    apply t0.
  Defined.

  Fixpoint undec {Γ t} (v: term Γ t) :=
    match v with
    | v_var x _ => Spec.v_var x
    | v_tt => Spec.v_tt
    | v_fst v => Spec.v_fst (undec v)
    | v_snd v => Spec.v_snd (undec v)
    | v_fanout v v' => Spec.v_fanout (undec v) (undec v')
    end.

  Lemma wf {Γ t} (v: term Γ t): Γ ⊢ undec v in t.
  Proof.
    induction v.
    all: cbn.
    all: econstructor.
    all: eauto.
    apply find_sound.
    auto.
  Qed.

  Lemma wf_undec_dec {Γ v t} (p: typecheck Γ v = Some t): Γ ⊢ undec (dec t v p) in t.
  Proof.
    apply wf.
  Qed.

  Lemma undec_dec {Γ v}:
    if dec' Γ v is Some (existT _ _ v')
    then
      undec v' = v
    else
      True.
  Proof.
    induction v.
    all: cbn.
    - destruct find_dec eqn:q.
      2: auto.
      cbn.
      auto.
    - auto.
    - destruct (dec' Γ v).
      2: auto.
      destruct s.
      destruct x.
      1: auto.
      cbn.
      rewrite IHv.
      auto.
    - destruct (dec' Γ v).
      2: auto.
      destruct s.
      destruct x.
      1: auto.
      cbn.
      rewrite IHv.
      auto.
    - destruct (dec' Γ v1).
      2: auto.
      destruct s.
      destruct (dec' Γ v2).
      2: auto.
      destruct s.
      cbn.
      rewrite IHv1, IHv2.
      auto.
  Qed.
End Dec.

Section Cartesian.
  Import CategoryNotations.

  Context {C: Category}.

  Context {unit: C}.
  Context {prod: C → C → C}.

  Context {bang: ∀ c, C c unit}.
  Context {fst: ∀ a b, C (prod a b) a}.
  Context {snd: ∀ a b, C (prod a b) b}.
  Context {fanout: ∀ a b c, C c a → C c b → C c (prod a b)}.

  Fixpoint obj t: C :=
    match t with
    | t_unit => unit
    | t_prod t t' => prod (obj t) (obj t')
    end.

  Fixpoint env Γ: C :=
    if Γ is cons ((_, t)) T
    then
      prod (obj t) (env T)
    else
      unit.

  Open Scope category.

  Import Dec.

  Fixpoint mor' {Γ t} (v: Dec.term Γ t) {A} {struct v}: (∀ x t, find x Γ = Some t → C A (obj t)) → C A (obj t) :=
    match v in term _ t' return (∀ x t, find x Γ = Some t → C A (obj t)) → C A (obj t') with
    | @v_var _ t' x p => λ h, h x t' p
    | v_tt => λ _, bang _
    | v_fst v => λ h, compose (fst _ _) (mor' v h)
    | v_snd v => λ h, compose (snd _ _) (mor' v h)
    | v_fanout v v' => λ h, fanout _ _ _ (mor' v h) (mor' v' h)
    end.

  Program Fixpoint find x t Γ (p: Environment.find x Γ = Some t): C (env Γ) (obj t) :=
    match Γ with
    | cons (y, t') T =>
        match eq_var x y with
        | left _ =>
            fst (obj t) (env T)
        | right _ =>
            compose (find x t T _) (snd (obj t') (env T))
        end
    | nil => match _: False with end
    end %list.

  Next Obligation.
  Proof.
    cbn in p.
    destruct eq_var in p.
    2: contradiction.
    inversion p.
    all: subst.
    all: auto.
  Qed.

  Definition mor {Γ t} v (p: typecheck Γ v = Some t) := mor' (Dec.dec t v p) (λ x t, find _ _ _).
End Cartesian.
