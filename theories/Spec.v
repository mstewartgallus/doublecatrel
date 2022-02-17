(* generated by Ott 0.31 from: ott/test.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Ott.ott_list_core.


Require Blech.Map.

Definition var : Set := nat.
Lemma eq_var: forall (x y : var), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_var : ott_coq_equality.

Inductive type : Set := 
 | t_unit : type
 | t_prod (t:type) (t':type).

Inductive normal : Set := 
 | N_tt : normal
 | N_fanout (N:normal) (N':normal).

Inductive term : Set := 
 | v_tt : term
 | v_fst (v:term)
 | v_snd (v:term)
 | v_fanout (v:term) (v':term).

Definition environment : Type := (Map.map type).

Inductive context : Set := 
 | E_var (x:var)
 | E_lam (x:var) (t:type) (E:context)
 | E_app (E:context) (E':context)
 | E_tt : context
 | E_step (E:context) (E':context)
 | E_fanout (E:context) (E':context)
 | E_let (x:var) (y:var) (E:context) (E':context).

Definition store : Type := (Map.map normal).

Inductive command : Set := 
 | c_var (x:var) (N:normal)
 | c_lam (x:var) (t:type) (c:command)
 | c_app (c:command) (c':command)
 | c_tt : command
 | c_step (c:command) (c':command)
 | c_fanout (c:command) (c':command)
 | c_let (x:var) (y:var) (c:command) (c':command).

Module Examples.

Example id t :=
 let x := 0 in
(E_lam x t (E_var x)). 

End Examples.

(** definitions *)

(* defns judge_context *)
Inductive JE : environment -> context -> type -> Type :=    (* defn E *)
 | JE_var : forall (x:var) (t:type),
     JE  (Map.add  x   t    Map.empty  )  (E_var x) t
 | JE_abs : forall (G:environment) (x:var) (t1:type) (E:context) (t2:type),
     JE  (Map.add  x   t1   G )  E t2 ->
     JE G (E_lam x t1 E) (t_prod t1 t2)
 | JE_app : forall (G1 G2:environment) (E1 E2:context) (t2 t1:type),
     JE G1 E1 (t_prod t1 t2) ->
     JE G2 E2 t1 ->
     JE  (Map.merge  G1   G2 )  (E_app E1 E2) t2
 | JE_tt : 
     JE  Map.empty  E_tt t_unit
 | JE_step : forall (G1 G2:environment) (E1 E2:context) (t:type),
     JE G1 E1 t_unit ->
     JE G2 E2 t ->
     JE  (Map.merge  G1   G2 )  (E_step E1 E2) t
 | JE_fanout : forall (G1 G2:environment) (E1 E2:context) (t1 t2:type),
     JE G1 E1 t1 ->
     JE G2 E2 t2 ->
     JE  (Map.merge  G1   G2 )  (E_fanout E1 E2) (t_prod t1 t2)
 | JE_let : forall (G1 G2:environment) (x0 x1:var) (E1 E2:context) (t3 t1 t2:type),
     JE G1 E1 (t_prod t1 t2) ->
     JE  (Map.add  x1   t2    (Map.add  x0   t1   G2 )  )  E2 t3 ->
     JE  (Map.merge  G1   G2 )  (E_let x0 x1 E1 E2) t3.
(** definitions *)

(* defns judge_term *)
Inductive Jv : term -> type -> Type :=    (* defn v *)
 | Jv_tt : 
     Jv v_tt t_unit
 | Jv_fanout : forall (v1 v2:term) (t1 t2:type),
     Jv v1 t1 ->
     Jv v2 t2 ->
     Jv (v_fanout v1 v2) (t_prod t1 t2)
 | Jv_fst : forall (v:term) (t1 t2:type),
     Jv v (t_prod t1 t2) ->
     Jv (v_fst v) t1
 | Jv_snd : forall (v:term) (t2 t1:type),
     Jv v (t_prod t1 t2) ->
     Jv (v_snd v) t2.
(** definitions *)

(* defns big *)
Inductive big : term -> normal -> Type :=    (* defn big *)
 | big_tt : 
     big v_tt N_tt
 | big_fanout : forall (v1 v2:term) (N1' N2':normal),
     big v1 N1' ->
     big v2 N2' ->
     big  ( (v_fanout v1 v2) )   ( (N_fanout N1' N2') ) 
 | big_fst : forall (v:term) (N1 N2:normal),
     big v (N_fanout N1 N2) ->
     big (v_fst v) N1
 | big_snd : forall (v:term) (N2 N1:normal),
     big v (N_fanout N1 N2) ->
     big (v_snd v) N2.
(** definitions *)

(* defns sat *)
Inductive sat : store -> command -> context -> normal -> Prop :=    (* defn sat *)
 | sat_var : forall (x:var) (N:normal),
     sat  (Map.add  x   N    Map.empty  )  (c_var x N) (E_var x) N
 | sat_tt : 
     sat  Map.empty  c_tt E_tt N_tt
 | sat_step : forall (D D':store) (c c':command) (E E':context) (N:normal),
     sat D c E N_tt ->
     sat D' c' E' N ->
     sat  (Map.merge  D   D' )  (c_step c c')  ( (E_step E E') )  N
 | sat_fanout : forall (D D':store) (c c':command) (E E':context) (N N':normal),
     sat D c E N ->
     sat D' c' E' N' ->
     sat  (Map.merge  D   D' )  (c_fanout c c')  ( (E_fanout E E') )  (N_fanout N N')
 | sat_let : forall (D D':store) (x y:var) (c c':command) (E E':context) (N2 N0 N1:normal),
     sat D c E (N_fanout N0 N1) ->
     sat  (Map.add  y   N1    (Map.add  x   N0   D' )  )  c' E' N2 ->
     sat  (Map.merge  D   D' )  (c_let x y c c')  ( (E_let x y E E') )  N2
 | sat_lam : forall (D:store) (x:var) (t:type) (c:command) (E:context) (N N':normal),
     sat  (Map.add  x   N   D )  c E N' ->
     sat D (c_lam x t c)  ( (E_lam x t E) )  (N_fanout N N')
 | sat_app : forall (D D':store) (c c':command) (E E':context) (N' N:normal),
     sat D c E (N_fanout N N') ->
     sat D' c' E' N ->
     sat  (Map.merge  D   D' )  (c_app c c')  ( (E_app E E') )  N'.


