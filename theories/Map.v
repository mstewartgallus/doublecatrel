Require Coq.FSets.FMapAVL.
Require Coq.FSets.FMapInterface.
Require Coq.Structures.OrderedTypeEx.

Import IfNotations.

Module Env <: FMapInterface.S := FMapAVL.Make OrderedTypeEx.Nat_as_OT.

Definition map := Env.t.

Definition empty {V}: Env.t V := Env.empty _.
Definition add {V}: nat -> V -> Env.t V -> Env.t V := @Env.add _.
Definition merge {V}: Env.t V -> Env.t V -> Env.t V := Env.map2 (fun x y => if x is Some _ then x else y).

Definition one {V} (x: nat) (v: V) := Env.add x v (Env.empty _).
Definition minus {V}: nat -> Env.t V -> Env.t V := @Env.remove _.
Definition find {V}: nat -> Env.t V -> option V := @Env.find _.
