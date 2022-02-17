Require Coq.FSets.FMapAVL.
Require Coq.FSets.FMapInterface.
Require Coq.Structures.OrderedTypeEx.

Import IfNotations.

Module Env <: FMapInterface.S := FMapAVL.Make OrderedTypeEx.Nat_as_OT.

Definition map := Env.t.

Definition empty {V}: map V := Env.empty _.
Definition add {V}: nat -> V -> map V -> map V := @Env.add _.
Definition merge {V}: map V -> map V -> map V := Env.map2 (fun x y => if x is Some _ then x else y).

Definition one {V} (x: nat) (v: V) := add x v empty.
Definition minus {V}: nat -> map V -> map V := @Env.remove _.
Definition find {V}: nat -> map V -> option V := @Env.find _.

Lemma add_minus {V}:
  forall x (t: V) Γ,
    find x Γ = Some t ->
    add x t (minus x Γ) = Γ.
Proof.
  intros x t Γ p.
  unfold add, minus.
  admit.
Admitted.

Lemma find_add {V}:
  forall x (t: V) Γ,
    find x (add x t Γ) = Some t.
Proof.
  intros x t.
  admit.
Admitted.

Lemma always_empty {V}:
  forall x (t: V), Env.is_empty (minus x (add x t empty)) = true.
Proof.
  intros ? ?.
  unfold one.
  admit.
Admitted.

Lemma remove_add {V}:
  forall x (t: V) Γ,
    minus x (add x t Γ) = Γ.
Proof.
  intros x t.
  admit.
Admitted.


Lemma add_add {V}:
  forall x (s t: V) Γ,
    add x s (add x t Γ) = add x s Γ.
Proof.
  intros x s t Γ.
  unfold add.
  admit.
Admitted.
