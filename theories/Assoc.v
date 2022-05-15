Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.PeanoNat.

Require Import FunInd.

Import IfNotations.

Import Nat.

Record MapsTo (K V: Set) := maps { key: K ; value: V ; }.

Arguments maps {K V}.
Arguments key {K V}.
Arguments value {K V}.

Infix "↦" := maps (at level 30).

Definition assoc (K: Set) (V: Set) := list (MapsTo K V).

Function find {A: Set} x (l: assoc nat A) :=
  if l is (maps y t :: T)%list
  then
    if Nat.eq_dec x y
    then
      Some t
    else
      find x T
  else
    None.
