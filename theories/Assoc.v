Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.PeanoNat.

Require Import FunInd.

Import IfNotations.

Import Nat.

Definition assoc (A: Set) := list (nat * A).

Function find {A: Set} x (l: assoc A) :=
  if l is ((y, t) :: T)%list
  then
    if Nat.eq_dec x y
    then
      Some t
    else
      find x T
  else
    None.
