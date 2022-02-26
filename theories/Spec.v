(* generated by Ott 0.31 from: ott/context.ott ott/term.ott ott/type.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Ott.ott_list_core.



Inductive type : Set := 
 | t_unit : type
 | t_prod (t:type) (t':type).
Lemma eq_type: forall (x y : type), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_type : ott_coq_equality.
Definition vvar : Set := nat.
Lemma eq_vvar: forall (x y : vvar), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_vvar : ott_coq_equality.

Inductive normal : Set := 
 | N_tt : normal
 | N_fanout (N:normal) (N':normal).

Inductive term : Set := 
 | v_var (x:vvar)
 | v_tt : term
 | v_fst (v:term)
 | v_snd (v:term)
 | v_fanout (v:term) (v':term).

Definition environment : Set := (list (vvar * type)).

Definition subst : Set := (list (vvar * term)).

Inductive definition : Set := 
 | d_with (Γ:environment) (v:term).
Lemma eq_normal: forall (x y : normal), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_normal : ott_coq_equality.
Lemma eq_term: forall (x y : term), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_term : ott_coq_equality.

(** substitutions *)
Fixpoint subst_term (v5:term) (x5:vvar) (v_6:term) {struct v_6} : term :=
  match v_6 with
  | (v_var x) => (if eq_vvar x x5 then v5 else (v_var x))
  | v_tt => v_tt 
  | (v_fst v) => v_fst (subst_term v5 x5 v)
  | (v_snd v) => v_snd (subst_term v5 x5 v)
  | (v_fanout v v') => v_fanout (subst_term v5 x5 v) (subst_term v5 x5 v')
end.

Definition subst_definition (v5:term) (x5:vvar) (d5:definition) : definition :=
  match d5 with
  | (d_with Γ v) => d_with Γ (subst_term v5 x5 v)
end.

(** definitions *)

(** funs toterm *)
Fixpoint toterm (x1:normal) : term:=
  match x1 with
  | N_tt => v_tt
  | (N_fanout N N') => (v_fanout  (toterm N )   (toterm N' ) )
end.

Coercion toterm: normal >-> term.

(** definitions *)

(** funs msubst *)
Fixpoint msubst (x1:subst) (x2:term) : term:=
  match x1,x2 with
  |  nil  , v => v
  |  (cons ( x ,  v' )  ρ )  , v =>  (msubst ρ  (  (subst_term  v'   x   v )  )  ) 
end.

(** definitions *)

(* defns find *)
Inductive mem : vvar -> type -> environment -> Prop :=    (* defn mem *)
 | mem_eq : forall (x:vvar) (t:type) (Γ:environment),
     mem x t  (cons ( x ,  t )  Γ ) 
 | mem_ne : forall (x:vvar) (t:type) (Γ:environment) (y:vvar) (t':type),
      ( x  <>  y )  ->
     mem x t Γ ->
     mem x t  (cons ( y ,  t' )  Γ ) .
(** definitions *)

(* defns judge_term *)
Inductive Jv : definition -> type -> Prop :=    (* defn v *)
 | Jv_var : forall (Γ:environment) (x:vvar) (t:type),
     mem x t Γ ->
     Jv (d_with Γ (v_var x)) t
 | Jv_tt : forall (Γ:environment),
     Jv (d_with Γ v_tt) t_unit
 | Jv_fanout : forall (Γ:environment) (v1 v2:term) (t1 t2:type),
     Jv (d_with Γ v1) t1 ->
     Jv (d_with Γ v2) t2 ->
     Jv (d_with Γ (v_fanout v1 v2)) (t_prod t1 t2)
 | Jv_fst : forall (Γ:environment) (v:term) (t1 t2:type),
     Jv (d_with Γ v) (t_prod t1 t2) ->
     Jv (d_with Γ (v_fst v)) t1
 | Jv_snd : forall (Γ:environment) (v:term) (t2 t1:type),
     Jv (d_with Γ v) (t_prod t1 t2) ->
     Jv (d_with Γ (v_snd v)) t2.
(** definitions *)

(* defns big *)
Inductive big : term -> normal -> Prop :=    (* defn big *)
 | big_tt : 
     big v_tt N_tt
 | big_fanout : forall (v1 v2:term) (N1' N2':normal),
     big v1 N1' ->
     big v2 N2' ->
     big (v_fanout v1 v2) (N_fanout N1' N2')
 | big_fst : forall (v:term) (N1 N2:normal),
     big v (N_fanout N1 N2) ->
     big (v_fst v) N1
 | big_snd : forall (v:term) (N2 N1:normal),
     big v (N_fanout N1 N2) ->
     big (v_snd v) N2.
(** definitions *)

(* defns judge *)
Inductive Jp : subst -> environment -> Prop :=    (* defn p *)
 | Jp_nil : 
     Jp  nil   nil 
 | Jp_cons : forall (ρ:subst) (x:vvar) (v:term) (Γ:environment) (t:type),
     Jv (d_with Γ v) t ->
     Jp ρ Γ ->
     Jp  (cons ( x ,  v )  ρ )   (cons ( x ,  t )  Γ ) .
Require Blech.Map.
Require Import Metalib.Metatheory.

Definition cvar : Set := var.
Lemma eq_cvar: forall (x y : cvar), {x = y} + {x <> y}.
Proof.
apply Atom.eq_dec.
Defined.
Hint Resolve eq_cvar : ott_coq_equality.

Definition store : Set := (Map.map normal).

Inductive span : Set := 
 | P_with (σ:store) (N:normal).

Definition linear : Set := (Map.map type).

Inductive context : Set := 
 | E_var (X:cvar)
 | E_lam (X:cvar) (t:type) (E:context)
 | E_app (E:context) (E':context)
 | E_tt : context
 | E_step (E:context) (E':context)
 | E_fanout (E:context) (E':context)
 | E_let (X:cvar) (Y:cvar) (E:context) (E':context).

Definition set : Set := (list span).
Lemma eq_context: forall (x y : context), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_context : ott_coq_equality.
(** library functions *)
Fixpoint list_mem A (eq:forall a b:A,{a=b}+{a<>b}) (x:A) (l:list A) {struct l} : bool :=
  match l with
  | nil => false
  | cons h t => if eq h x then true else list_mem A eq x t
end.
Arguments list_mem [A] _ _ _.


(** substitutions *)
Fixpoint subst_context (E5:context) (X5:cvar) (E_6:context) {struct E_6} : context :=
  match E_6 with
  | (E_var X) => (if eq_cvar X X5 then E5 else (E_var X))
  | (E_lam X t E) => E_lam X t (if list_mem eq_cvar X5 (cons X nil) then E else (subst_context E5 X5 E))
  | (E_app E E') => E_app (subst_context E5 X5 E) (subst_context E5 X5 E')
  | E_tt => E_tt 
  | (E_step E E') => E_step (subst_context E5 X5 E) (subst_context E5 X5 E')
  | (E_fanout E E') => E_fanout (subst_context E5 X5 E) (subst_context E5 X5 E')
  | (E_let X Y E E') => E_let X Y (subst_context E5 X5 E) (if list_mem eq_cvar X5 (app (cons X nil) (cons Y nil)) then E' else (subst_context E5 X5 E'))
end.

(** definitions *)

(* defns judge_context *)
Inductive JE : linear -> context -> type -> Prop :=    (* defn E *)
 | JE_var : forall (X:cvar) (t:type),
     JE  (Map.one  X   t )  (E_var X) t
 | JE_lam : forall (Δ:linear) (X:cvar) (t1:type) (E:context) (t2:type),
     JE  (Map.merge   (Map.one  X   t1 )    Δ )  E t2 ->
     JE Δ (E_lam X t1 E) (t_prod t1 t2)
 | JE_app : forall (Δ1 Δ2:linear) (E1 E2:context) (t2 t1:type),
     JE Δ1 E1 (t_prod t1 t2) ->
     JE Δ2 E2 t1 ->
     JE  (Map.merge  Δ1   Δ2 )  (E_app E1 E2) t2
 | JE_tt : 
     JE  (Map.empty)  E_tt t_unit
 | JE_step : forall (Δ1 Δ2:linear) (E1 E2:context) (t:type),
     JE Δ1 E1 t_unit ->
     JE Δ2 E2 t ->
     JE  (Map.merge  Δ1   Δ2 )  (E_step E1 E2) t
 | JE_fanout : forall (Δ1 Δ2:linear) (E1 E2:context) (t1 t2:type),
     JE Δ1 E1 t1 ->
     JE Δ2 E2 t2 ->
     JE  (Map.merge  Δ1   Δ2 )  (E_fanout E1 E2) (t_prod t1 t2)
 | JE_let : forall (Δ1 Δ2:linear) (X Y:cvar) (E1 E2:context) (t3 t1 t2:type),
     JE Δ1 E1 (t_prod t1 t2) ->
     JE  (Map.merge   (Map.one  Y   t2 )     (Map.merge   (Map.one  X   t1 )    Δ2 )  )  E2 t3 ->
     JE  (Map.merge  Δ1   Δ2 )  (E_let X Y E1 E2) t3.
(** definitions *)

(* defns sat *)
Inductive sat : store -> context -> normal -> Prop :=    (* defn sat *)
 | sat_var : forall (X:cvar) (N:normal),
     sat  (Map.one  X   N )  (E_var X) N
 | sat_tt : 
     sat  (Map.empty)  E_tt N_tt
 | sat_step : forall (σ σ':store) (E E':context) (N:normal),
     sat σ E N_tt ->
     sat σ' E' N ->
     sat  (Map.merge  σ   σ' )   ( (E_step E E') )  N
 | sat_fanout : forall (σ σ':store) (E E':context) (N N':normal),
     sat σ E N ->
     sat σ' E' N' ->
     sat  (Map.merge  σ   σ' )   ( (E_fanout E E') )  (N_fanout N N')
 | sat_let : forall (σ σ':store) (X Y:cvar) (E E':context) (N2 N0 N1:normal),
     sat σ E (N_fanout N0 N1) ->
     sat  (Map.merge   (Map.one  Y   N1 )     (Map.merge   (Map.one  X   N0 )    σ' )  )  E' N2 ->
     sat  (Map.merge  σ   σ' )   ( (E_let X Y E E') )  N2
 | sat_lam : forall (σ:store) (X:cvar) (t:type) (E:context) (N N':normal),
     sat  (Map.merge   (Map.one  X   N )    σ )  E N' ->
     sat σ  ( (E_lam X t E) )  (N_fanout N N')
 | sat_app : forall (σ σ':store) (E E':context) (N' N:normal),
     sat σ E (N_fanout N N') ->
     sat σ' E' N ->
     sat  (Map.merge  σ   σ' )   ( (E_app E E') )  N'.
(** definitions *)

(* defns judgeS *)
Inductive JS : store -> linear -> Prop :=    (* defn S *)
 | JS_nil : 
     JS  (Map.empty)   (Map.empty) 
 | JS_merge : forall (σ σ':store) (Δ Δ':linear),
     JS σ Δ ->
     JS σ' Δ' ->
     JS  (Map.merge  σ   σ' )   (Map.merge  Δ   Δ' ) 
 | JS_one : forall (X:cvar) (N:normal) (t:type),
     Jv (d_with  nil   (toterm N ) ) t ->
     JS  (Map.one  X   N )   (Map.one  X   t ) .
(** definitions *)

(* defns sound *)
Inductive sound : context -> set -> Prop :=    (* defn sound *)
 | sound_nil : forall (E:context),
     sound E  nil 
 | sound_cons : forall (E:context) (Ps:set) (σ:store) (N:normal),
     sound E Ps ->
     sat σ E N ->
     sound E  (cons  (P_with σ N)   Ps ) .


