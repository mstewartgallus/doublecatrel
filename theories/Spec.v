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

Inductive type : Set := 
 | t_unit : type
 | t_prod (t:type) (t':type).

Inductive term : Set := 
 | v_tt : term
 | v_fst (v:term)
 | v_snd (v:term)
 | v_fanout (v:term) (v':term).

Definition seq : Type := (Map.map normal).

Inductive context : Set := 
 | E_var (x:var)
 | E_all (x:var) (t:type) (E:context)
 | E_app (E:context) (E':context)
 | E_tt : context
 | E_step (E:context) (E':context)
 | E_fanout (E:context) (E':context)
 | E_let (x:var) (y:var) (E:context) (E':context).

Definition environment : Type := (Map.map type).
(** library functions *)
Fixpoint list_mem A (eq:forall a b:A,{a=b}+{a<>b}) (x:A) (l:list A) {struct l} : bool :=
  match l with
  | nil => false
  | cons h t => if eq h x then true else list_mem A eq x t
end.
Arguments list_mem [A] _ _ _.


(** substitutions *)
Fixpoint subst_context (E5:context) (x5:var) (E_6:context) {struct E_6} : context :=
  match E_6 with
  | (E_var x) => (if eq_var x x5 then E5 else (E_var x))
  | (E_all x t E) => E_all x t (if list_mem eq_var x5 (cons x nil) then E else (subst_context E5 x5 E))
  | (E_app E E') => E_app (subst_context E5 x5 E) (subst_context E5 x5 E')
  | E_tt => E_tt 
  | (E_step E E') => E_step (subst_context E5 x5 E) (subst_context E5 x5 E')
  | (E_fanout E E') => E_fanout (subst_context E5 x5 E) (subst_context E5 x5 E')
  | (E_let x y E E') => E_let x y (subst_context E5 x5 E) (if list_mem eq_var x5 (app (cons x nil) (cons y nil)) then E' else (subst_context E5 x5 E'))
end.

(** library functions *)
Fixpoint list_minus A (eq:forall a b:A,{a=b}+{a<>b}) (l1:list A) (l2:list A) {struct l1} : list A :=
  match l1 with
  | nil => nil
  | cons h t => if (list_mem (A:=A) eq h l2) then list_minus A eq t l2 else cons h (list_minus A eq t l2)
end.
Arguments list_minus [A] _ _ _.


(** free variables *)
Fixpoint fv_context (E5:context) : list var :=
  match E5 with
  | (E_var x) => (cons x nil)
  | (E_all x t E) => ((list_minus eq_var (fv_context E) (cons x nil)))
  | (E_app E E') => (app (fv_context E) (fv_context E'))
  | E_tt => nil
  | (E_step E E') => (app (fv_context E) (fv_context E'))
  | (E_fanout E E') => (app (fv_context E) (fv_context E'))
  | (E_let x y E E') => (app (fv_context E) (list_minus eq_var (fv_context E') (app (cons x nil) (cons y nil))))
end.

(** definitions *)

(* defns judge_context *)
Inductive JE : environment -> context -> type -> Type :=    (* defn E *)
 | JE_var : forall (x:var) (t:type),
     JE  (Map.add  x   t    Map.empty  )  (E_var x) t
 | JE_abs : forall (G:environment) (x:var) (t1:type) (E:context) (t2:type),
     JE  (Map.add  x   t1   G )  E t2 ->
     JE G (E_all x t1 E) (t_prod t1 t2)
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
Inductive sat : seq -> context -> normal -> Prop :=    (* defn sat *)
 | sat_var : forall (D:seq) (x:var) (N:normal),
     Map.find x D = Some N  ->
     sat D (E_var x) N
 | sat_tt : forall (D:seq),
     sat D E_tt N_tt
 | sat_step : forall (D:seq) (E E':context) (N:normal),
     sat D E N_tt ->
     sat D E' N ->
     sat D  ( (E_step E E') )  N
 | sat_fanout : forall (D:seq) (E E':context) (N N':normal),
     sat D E N ->
     sat D E' N' ->
     sat D  ( (E_fanout E E') )  (N_fanout N N')
 | sat_let : forall (D:seq) (x0 x1:var) (E E':context) (N2 N0 N1:normal),
     sat D E (N_fanout N0 N1) ->
     sat  (Map.add  x1   N1    (Map.add  x0   N0   D )  )  E' N2 ->
     sat D  ( (E_let x0 x1 E E') )  N2
 | sat_abs : forall (D:seq) (x:var) (t:type) (E:context) (N N':normal),
     sat  (Map.add  x   N   D )  E N' ->
     sat D  ( (E_all x t E) )  (N_fanout N N')
 | sat_app : forall (D:seq) (E E':context) (N' N:normal),
     sat D E (N_fanout N N') ->
     sat D E' N ->
     sat D  ( (E_app E E') )  N'.


