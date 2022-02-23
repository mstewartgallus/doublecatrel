Require Blech.Map.
Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Import Coq.Unicode.Utf8.
Require Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Import IfNotations.

Implicit Type Δ: linear.
Implicit Type E: context.
Implicit Type t: type.
Implicit Type N: normal.
Implicit Types X Y: cvar.
Implicit Type σ: store.

Import Map.MapNotations.

(* Satisfaction defines a sort of nondeterministic Hoare logic *)

(* based on https://softwarefoundations.cis.upenn.edu/slf-current/Hprop.html *)

(* FIXME make a monad? *)
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
    (at level 200, x1 binder, H at level 50, right associativity,
      format "'[' '\exists' '/ ' x1 .. xn , '/ ' H ']'").

Definition ig {A} (P: hprop unit): hprop A := λ _, P tt.

Lemma disjointness {h0 h1 h2: store}:
    Map.disjoint h1 h0 → Map.disjoint (h1 ∪ h0) h2 →
    Map.disjoint h0 h2.
Proof.
  unfold Map.disjoint.
  intros p q.
  intro k.
  destruct (p k).
  all: auto.
  destruct (q k).
  all: auto.
  rewrite Map.find_merge_r in H0.
  all: auto.
Qed.

Theorem hstar_assoc:
  ∀ {V} {A B C: hprop V},
    (A \* B) \* C = A \* (B \* C).
Proof using.
  intros.
  extensionality v.
  extensionality σ.
  apply propositional_extensionality.
  split.
  - intro p.
    destruct p.
    destruct H.
    rewrite Map.merge_assoc.
    constructor.
    1: auto.
    1: constructor.
    all: auto.
    + eapply disjointness.
      all: eauto.
    + admit.
Admitted.

Inductive eval: context → store → normal → store → Prop :=
| eval_sat {E σ σ' N}: sat σ' E N → eval E σ N (Map.merge σ σ').

Definition hoare E (H: hprop unit) (Q: hprop normal): Prop :=
  ∀ s,
    H tt s →
    ∃ s' N, eval E s N s' /\ Q N s'.

Definition triple E H (Q: hprop normal) : Prop :=
  ∀ H', hoare E (H \* H') (Q \* ig H').
