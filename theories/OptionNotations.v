(* Define only as a notation becaues Function can't see through otherwise *)
Notation "'do' x ← e0 ; e1" :=
  (match e0 with
   | Some x => e1
   | _ => None
   end) (x pattern, at level 200, left associativity).
