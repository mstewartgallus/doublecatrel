Require Import Blech.Spec.
Require Import Blech.SpecNotations.

Require Blech.Term.
Require Blech.Context.
Require Blech.Sat.
Require Blech.Map.

Import IfNotations.

(*
 Maps are behaviour preserving transformations between terms.  This
 way we get identity and composition for free without finicky
 substitution issues.
 *)
Module Import Hor.
  (* FIXME preserve behaviour as well *)
  Class Hor (A B: type) f := {
      preserves_types {Γ v}: Γ ⊢ v in A -> Γ ⊢ f v in B ;
  }.

  Definition id x: term := x.

  Instance id_Hor A: Hor A A id.
  Proof using.
    exists.
    auto.
  Defined.

  Definition compose (f g: term -> term) x := f (g x).

  Instance compose_Hor f g {A B C} `{Hor B C f} `{Hor A B g}: Hor A C (compose f g).
  Proof.
    exists.
    intros.
    unfold compose.
    apply preserves_types.
    apply preserves_types.
    auto.
  Defined.

  Definition tt (x: term) := v_tt.
  Instance tt_Hor A: Hor A t_unit tt.
  Proof.
    exists.
    intros.
    constructor.
  Defined.

  Definition fanout (f g: term -> term) x := v_fanout (f x) (g x).
  Instance fanout_Hor f g {A B C} `{Hor C A f} `{Hor C B g}: Hor C (t_prod A B) (fanout f g).
  Proof.
    exists.
    intros.
    unfold fanout.
    constructor.
    all: apply preserves_types.
    all: auto.
  Defined.

  Instance fst_Hor A B : Hor (t_prod A B) A v_fst.
  Proof.
    exists.
    intros.
    econstructor.
    eauto.
  Defined.

  Instance snd_Hor A B : Hor (t_prod A B) B v_snd.
  Proof.
    exists.
    intros.
    econstructor.
    eauto.
  Defined.

  (* FIXME define setoid equality and prove laws *)
End Hor.

Module Import Vert.
  Class Vert (A B: type) f := {
      preserves_types {Γ E}: Γ ⊢ E ? A -> Γ ⊢ f E ? B ;
  }.

  Definition id x: context := x.

  Instance id_Vert A: Vert A A id.
  Proof using.
    exists.
    auto.
  Defined.

  Definition compose (f g: context -> context) x := f (g x).

  Instance compose_Vert f g {A B C} `{Vert B C f} `{Vert A B g}: Vert A C (compose f g).
  Proof.
    exists.
    intros.
    unfold compose.
    apply preserves_types.
    apply preserves_types.
    auto.
  Defined.
End Vert.
