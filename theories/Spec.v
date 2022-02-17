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
Definition index : Set := nat.

Inductive normal : Set := 
 | N_tt : normal
 | N_fanout (N:normal) (N':normal).

Definition store : Type := (Map.map normal).

Inductive type : Set := 
 | t_unit : type
 | t_prod (t:type) (t':type).

Inductive span : Type := 
 | P_with (D:store) (N:normal).

Inductive context : Set := 
 | E_var (x:var)
 | E_lam (x:var) (t:type) (E:context)
 | E_app (E:context) (E':context)
 | E_tt : context
 | E_step (E:context) (E':context)
 | E_fanout (E:context) (E':context)
 | E_let (x:var) (y:var) (E:context) (E':context).

Definition environment : Type := (Map.map type).

Inductive term : Set := 
 | v_var (x:var)
 | v_tt : term
 | v_fst (v:term)
 | v_snd (v:term)
 | v_fanout (v:term) (v':term).

Definition set : Type := (list span).

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
Inductive Jv : environment -> term -> type -> Type :=    (* defn v *)
 | Jv_var : forall (G:environment) (x:var) (t:type),
     Map.find x G = Some t  ->
     Jv G (v_var x) t
 | Jv_tt : forall (G:environment),
     Jv G v_tt t_unit
 | Jv_fanout : forall (G:environment) (v1 v2:term) (t1 t2:type),
     Jv G v1 t1 ->
     Jv G v2 t2 ->
     Jv G (v_fanout v1 v2) (t_prod t1 t2)
 | Jv_fst : forall (G:environment) (v:term) (t1 t2:type),
     Jv G v (t_prod t1 t2) ->
     Jv G (v_fst v) t1
 | Jv_snd : forall (G:environment) (v:term) (t2 t1:type),
     Jv G v (t_prod t1 t2) ->
     Jv G (v_snd v) t2.
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
Inductive sat : context -> span -> Prop :=    (* defn sat *)
 | sat_var : forall (x:var) (N:normal),
     sat (E_var x) (P_with  (Map.add  x   N    Map.empty  )  N)
 | sat_tt : 
     sat E_tt (P_with  Map.empty  N_tt)
 | sat_step : forall (E E':context) (D D':store) (N:normal),
     sat E (P_with D N_tt) ->
     sat E' (P_with D' N) ->
     sat  ( (E_step E E') )  (P_with  (Map.merge  D   D' )  N)
 | sat_fanout : forall (E E':context) (D D':store) (N N':normal),
     sat E (P_with D N) ->
     sat E' (P_with D' N') ->
     sat  ( (E_fanout E E') )  (P_with  (Map.merge  D   D' )  (N_fanout N N'))
 | sat_let : forall (x y:var) (E E':context) (D D':store) (N2 N0 N1:normal),
     sat E (P_with D (N_fanout N0 N1)) ->
     sat E' (P_with  (Map.add  y   N1    (Map.add  x   N0   D' )  )  N2) ->
     sat  ( (E_let x y E E') )  (P_with  (Map.merge  D   D' )  N2)
 | sat_lam : forall (x:var) (t:type) (E:context) (D:store) (N N':normal),
     sat E (P_with  (Map.add  x   N   D )  N') ->
     sat  ( (E_lam x t E) )  (P_with D (N_fanout N N'))
 | sat_app : forall (E E':context) (D D':store) (N' N:normal),
     sat E (P_with D (N_fanout N N')) ->
     sat E' (P_with D' N) ->
     sat (E_app E E') (P_with  (Map.merge  D   D' )  N').
(** definitions *)

(* defns sound *)
Inductive sound : context -> set -> Prop :=    (* defn sound *)
 | sound_nil : forall (E:context),
     sound E  nil 
 | sound_cons : forall (E:context) (X:set) (P:span),
     sound E X ->
     sat E P ->
     sound E  (cons  P   X ) .


