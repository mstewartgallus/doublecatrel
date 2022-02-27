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
Definition var : Set := nat.
Lemma eq_var: forall (x y : var), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_var : ott_coq_equality.

Inductive normal : Set := 
 | N_tt : normal
 | N_fanout (N:normal) (N':normal).

Inductive term : Set := 
 | v_var (x:var)
 | v_tt : term
 | v_fst (v:term)
 | v_snd (v:term)
 | v_fanout (v:term) (v':term).

Definition environment : Set := (list (var * type)).

Definition subst : Set := (list (var * term)).
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
Fixpoint subst_term (v5:term) (x5:var) (v_6:term) {struct v_6} : term :=
  match v_6 with
  | (v_var x) => (if eq_var x x5 then v5 else (v_var x))
  | v_tt => v_tt 
  | (v_fst v) => v_fst (subst_term v5 x5 v)
  | (v_snd v) => v_snd (subst_term v5 x5 v)
  | (v_fanout v v') => v_fanout (subst_term v5 x5 v) (subst_term v5 x5 v')
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
Inductive mem : var -> type -> environment -> Prop :=    (* defn mem *)
 | mem_eq : forall (x:var) (t:type) (Γ:environment),
     mem x t  (cons ( x ,  t )  Γ ) 
 | mem_ne : forall (x:var) (t:type) (Γ:environment) (y:var) (t':type),
      ( x  <>  y )  ->
     mem x t Γ ->
     mem x t  (cons ( y ,  t' )  Γ ) .
(** definitions *)

(* defns judge_term *)
Inductive Jv : environment -> term -> type -> Prop :=    (* defn v *)
 | Jv_var : forall (Γ:environment) (x:var) (t:type),
     mem x t Γ ->
     Jv Γ (v_var x) t
 | Jv_tt : forall (Γ:environment),
     Jv Γ v_tt t_unit
 | Jv_fanout : forall (Γ:environment) (v1 v2:term) (t1 t2:type),
     Jv Γ v1 t1 ->
     Jv Γ v2 t2 ->
     Jv Γ (v_fanout v1 v2) (t_prod t1 t2)
 | Jv_fst : forall (Γ:environment) (v:term) (t1 t2:type),
     Jv Γ v (t_prod t1 t2) ->
     Jv Γ (v_fst v) t1
 | Jv_snd : forall (Γ:environment) (v:term) (t2 t1:type),
     Jv Γ v (t_prod t1 t2) ->
     Jv Γ (v_snd v) t2.
(** definitions *)

(* defns big *)
Inductive big : term -> normal -> Prop :=    (* defn big *)
 | big_tt : 
     big v_tt N_tt
 | big_fanout : forall (v1 v2:term) (N1 N2:normal),
     big v1 N1 ->
     big v2 N2 ->
     big (v_fanout v1 v2) (N_fanout N1 N2)
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
 | Jp_cons : forall (ρ:subst) (x:var) (v:term) (Γ:environment) (t:type),
     Jv Γ v t ->
     Jp ρ Γ ->
     Jp  (cons ( x ,  v )  ρ )   (cons ( x ,  t )  Γ ) .
Require Blech.Map.


Definition store : Set := (Map.map normal).

Inductive span : Set := 
 | P_with (σ:store) (N:normal).

Definition set : Set := (list span).

Inductive context : Set := 
 | E_var (x:var)
 | E_lam (x:var) (t:type) (E:context)
 | E_app (E:context) (E':context)
 | E_tt : context
 | E_step (E:context) (E':context)
 | E_fanout (E:context) (E':context)
 | E_let (x:var) (y:var) (E:context) (E':context).
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
Fixpoint subst_context (E5:context) (x5:var) (E_6:context) {struct E_6} : context :=
  match E_6 with
  | (E_var x) => (if eq_var x x5 then E5 else (E_var x))
  | (E_lam x t E) => E_lam x t (if list_mem eq_var x5 (cons x nil) then E else (subst_context E5 x5 E))
  | (E_app E E') => E_app (subst_context E5 x5 E) (subst_context E5 x5 E')
  | E_tt => E_tt 
  | (E_step E E') => E_step (subst_context E5 x5 E) (subst_context E5 x5 E')
  | (E_fanout E E') => E_fanout (subst_context E5 x5 E) (subst_context E5 x5 E')
  | (E_let x y E E') => E_let x y (subst_context E5 x5 E) (if list_mem eq_var x5 (app (cons x nil) (cons y nil)) then E' else (subst_context E5 x5 E'))
end.

(** definitions *)

(* defns nev *)
Inductive never : var -> context -> Prop :=    (* defn never *)
 | never_var : forall (x y:var),
      ( x  <>  y )  ->
     never x (E_var y)
 | never_lam_eq : forall (x:var) (t:type) (E:context),
     never x (E_lam x t E)
 | never_lam : forall (x y:var) (t:type) (E:context),
     never x E ->
      ( x  <>  y )  ->
     never x (E_lam y t E)
 | never_app : forall (x:var) (E E':context),
     never x E ->
     never x E' ->
     never x (E_app E E')
 | never_tt : forall (x:var),
     never x E_tt
 | never_step : forall (x:var) (E E':context),
     never x E ->
     never x E' ->
     never x (E_step E E')
 | never_fanout : forall (x:var) (E E':context),
     never x E ->
     never x E' ->
     never x (E_fanout E E')
 | never_let : forall (x y y':var) (E E':context),
     never x E ->
     never x E' ->
      ( x  <>  y )  ->
      ( x  <>  y' )  ->
     never x (E_let y y' E E')
 | never_let_eq_1 : forall (x y:var) (E E':context),
     never x E ->
     never x (E_let x y E E')
 | never_let_eq_2 : forall (x y:var) (E E':context),
     never x E ->
     never x (E_let y x E E').
(** definitions *)

(* defns onc *)
Inductive once : var -> context -> Prop :=    (* defn once *)
 | once_var : forall (x:var),
     once x (E_var x)
 | once_lam : forall (x y:var) (t:type) (E:context),
      ( x  <>  y )  ->
     once x E ->
     once x (E_lam y t E)
 | once_app_l : forall (x:var) (E E':context),
     once x E ->
     never x E' ->
     once x (E_app E E')
 | once_app_r : forall (x:var) (E E':context),
     never x E ->
     once x E' ->
     once x (E_app E E')
 | once_step_l : forall (x:var) (E E':context),
     once x E ->
     never x E' ->
     once x (E_step E E')
 | once_step_r : forall (x:var) (E E':context),
     never x E ->
     once x E' ->
     once x (E_step E E')
 | once_fanout_l : forall (x:var) (E E':context),
     once x E ->
     never x E' ->
     once x (E_fanout E E')
 | once_fanout_r : forall (x:var) (E E':context),
     never x E ->
     once x E' ->
     once x (E_fanout E E')
 | once_let_l : forall (x y y':var) (E E':context),
     once x E ->
     never x E' ->
      ( x  <>  y )  ->
      ( x  <>  y' )  ->
     once x (E_let y y' E E')
 | once_let_l1 : forall (x y:var) (E E':context),
     once x E ->
     once x (E_let x y E E')
 | once_let_l2 : forall (x y:var) (E E':context),
     once x E ->
     once x (E_let y x E E')
 | once_let_r : forall (x y y':var) (E E':context),
     never x E ->
     once x E' ->
      ( x  <>  y )  ->
      ( x  <>  y' )  ->
     once x (E_let y y' E E').
(** definitions *)

(* defns dummy *)
Inductive dd : Prop :=    (* defn d *).
(** definitions *)

(* defns judge_linear *)
Inductive JL : context -> Prop :=    (* defn L *)
 | JL_var : forall (x:var),
     JL (E_var x)
 | JL_lam : forall (x:var) (t:type) (E:context),
     once x E ->
     JL E ->
     JL (E_lam x t E)
 | JL_app : forall (E E':context),
     JL E ->
     JL E' ->
     JL (E_app E E')
 | JL_tt : 
     JL E_tt
 | JL_step : forall (E E':context),
     JL E ->
     JL E' ->
     JL (E_step E E')
 | JL_fanout : forall (E E':context),
     JL E ->
     JL E' ->
     JL (E_fanout E E')
 | JL_let : forall (x y:var) (E E':context),
     once x E' ->
     once y E' ->
     JL E ->
     JL E' ->
     JL (E_let x y E E').
(** definitions *)

(* defns judge_context *)
Inductive JE : environment -> context -> type -> Prop :=    (* defn E *)
 | JE_var : forall (Γ:environment) (x:var) (t:type),
     mem x t Γ ->
     JE Γ (E_var x) t
 | JE_lam : forall (Γ:environment) (x:var) (t1:type) (E:context) (t2:type),
     JE  (cons ( x ,  t1 )  Γ )  E t2 ->
     JE Γ (E_lam x t1 E) (t_prod t1 t2)
 | JE_app : forall (Γ:environment) (E1 E2:context) (t2 t1:type),
     JE Γ E1 (t_prod t1 t2) ->
     JE Γ E2 t1 ->
     JE Γ (E_app E1 E2) t2
 | JE_tt : forall (Γ:environment),
     JE Γ E_tt t_unit
 | JE_step : forall (Γ:environment) (E1 E2:context) (t:type),
     JE Γ E1 t_unit ->
     JE Γ E2 t ->
     JE Γ (E_step E1 E2) t
 | JE_fanout : forall (Γ:environment) (E1 E2:context) (t1 t2:type),
     JE Γ E1 t1 ->
     JE Γ E2 t2 ->
     JE Γ (E_fanout E1 E2) (t_prod t1 t2)
 | JE_let : forall (Γ:environment) (x y:var) (E1 E2:context) (t3 t1 t2:type),
     JE Γ E1 (t_prod t1 t2) ->
     JE  (cons ( y ,  t2 )   (cons ( x ,  t1 )  Γ )  )  E2 t3 ->
     JE Γ (E_let x y E1 E2) t3.
(** definitions *)

(* defns sat *)
Inductive sat : store -> context -> normal -> Prop :=    (* defn sat *)
 | sat_var : forall (x:var) (N:normal),
     sat  (Map.one  x   N )  (E_var x) N
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
 | sat_let : forall (σ σ':store) (x y:var) (E E':context) (N2 N0 N1:normal),
     sat σ E (N_fanout N0 N1) ->
     sat  (Map.merge   (Map.one  y   N1 )     (Map.merge   (Map.one  x   N0 )    σ' )  )  E' N2 ->
     sat  (Map.merge  σ   σ' )   ( (E_let x y E E') )  N2
 | sat_lam : forall (σ:store) (x:var) (t:type) (E:context) (N N':normal),
     sat  (Map.merge   (Map.one  x   N )    σ )  E N' ->
     sat σ  ( (E_lam x t E) )  (N_fanout N N')
 | sat_app : forall (σ σ':store) (E E':context) (N' N:normal),
     sat σ E (N_fanout N N') ->
     sat σ' E' N ->
     sat  (Map.merge  σ   σ' )   ( (E_app E E') )  N'.
(** definitions *)

(* defns sound *)
Inductive sound : context -> set -> Prop :=    (* defn sound *)
 | sound_nil : forall (E:context),
     sound E  nil 
 | sound_cons : forall (E:context) (Ps:set) (σ:store) (N:normal),
     sound E Ps ->
     sat σ E N ->
     sound E  (cons  (P_with σ N)   Ps ) .


