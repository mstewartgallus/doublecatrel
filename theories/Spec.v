(* generated by Ott 0.32 from: ott/term.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Ott.ott_list_core.


Require Blech.Assoc.

Definition tyvar : Set := nat.
Lemma eq_tyvar: forall (x y : tyvar), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_tyvar : ott_coq_equality.
Definition var : Set := nat.
Lemma eq_var: forall (x y : var), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_var : ott_coq_equality.
Definition axiom : Set := nat.
Lemma eq_axiom: forall (x y : axiom), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_axiom : ott_coq_equality.

Inductive type : Set := 
 | t_var (A:tyvar)
 | t_unit : type
 | t_prod (t:type) (t':type).

Inductive elim : Set := 
 | V_var (x:var)
 | V_fst (V:elim)
 | V_snd (V:elim).

Inductive use : Set := 
 | u_used : use
 | u_unused : use.

Inductive global : Set := 
 | g_function (t:type) (A:tyvar)
 | g_relation (t:type) (A:tyvar).

Inductive intro : Set := 
 | v_axiom (K:axiom) (v:intro)
 | v_tt : intro
 | v_fanout (v:intro) (v':intro)
 | v_neu (V:elim).

Definition usage : Set := (Assoc.assoc use).

Definition globals : Set := (Assoc.assoc global).

Inductive context : Set := 
 | E_axiom (K:axiom) (E:context)
 | E_inj (v:intro)
 | E_lam (x:var) (E:context)
 | E_tt : context
 | E_fanout (E:context) (E':context)
 | E_neu (e:redex)
with redex : Set := 
 | e_var (x:var)
 | e_app (e:redex) (E':context)
 | e_step (e:redex) (E':context) (t:type)
 | e_let (x:var) (y:var) (e:redex) (E':context) (t:type)
 | e_cut (E:context) (t:type).

Definition environment : Set := (Assoc.assoc type).

Definition subst : Set := (Assoc.assoc intro).

Inductive span : Set := 
 | P_with (ρ:subst) (v:intro).

Definition spans : Set := (list span).
Lemma eq_type: forall (x y : type), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_type : ott_coq_equality.
Lemma eq_elim: forall (x y : elim), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_elim : ott_coq_equality.
Lemma eq_use: forall (x y : use), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_use : ott_coq_equality.
Lemma eq_intro: forall (x y : intro), {x = y} + {x <> y}.
Proof.
  decide equality; auto with ott_coq_equality arith.
Defined.
Hint Resolve eq_intro : ott_coq_equality.
(** definitions *)

(** funs eta_expand *)
Fixpoint eta (x1:type) (x2:elim) : intro:=
  match x1,x2 with
  | (t_var A) , V => (v_neu V)
  | t_unit , V => v_tt
  | (t_prod t1 t2) , V => (v_fanout  (eta t1  ( (V_fst V) )  )   (eta t2  ( (V_snd V) )  ) )
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
Inductive JV : globals -> environment -> elim -> type -> Prop :=    (* defn V *)
 | JV_var : forall (X:globals) (Γ:environment) (x:var) (t:type),
     mem x t Γ ->
     JV X Γ (V_var x) t
 | JV_fst : forall (X:globals) (Γ:environment) (V:elim) (t1 t2:type),
     JV X Γ V (t_prod t1 t2) ->
     JV X Γ (V_fst V) t1
 | JV_snd : forall (X:globals) (Γ:environment) (V:elim) (t2 t1:type),
     JV X Γ V (t_prod t1 t2) ->
     JV X Γ (V_snd V) t2
with Jv : globals -> environment -> intro -> type -> Prop :=    (* defn v *)
 | Jv_axiom : forall (X:globals) (Γ:environment) (K:axiom) (v:intro) (A:tyvar) (t:type),
     Assoc.find K X = Some (g_function t A)  ->
     Jv X Γ v t ->
     Jv X Γ (v_axiom K v) (t_var A)
 | Jv_tt : forall (X:globals) (Γ:environment),
     Jv X Γ v_tt t_unit
 | Jv_fanout : forall (X:globals) (Γ:environment) (v1 v2:intro) (t1 t2:type),
     Jv X Γ v1 t1 ->
     Jv X Γ v2 t2 ->
     Jv X Γ (v_fanout v1 v2) (t_prod t1 t2)
 | Jv_neu : forall (X:globals) (Γ:environment) (V:elim) (A:tyvar),
     JV X Γ V (t_var A) ->
     Jv X Γ (v_neu V) (t_var A).
(** definitions *)

(* defns judge_subst *)
Inductive Jp : globals -> subst -> environment -> environment -> Prop :=    (* defn p *)
 | Jp_bang : forall (X:globals) (Γ:environment),
     Jp X  nil  Γ  nil 
 | Jp_cut : forall (X:globals) (ρ:subst) (x:var) (v:intro) (Γ1 Γ2:environment) (t:type),
     Jv X Γ1 v t ->
     Jp X ρ Γ1 Γ2 ->
     Jp X  (cons ( x ,  v )  ρ )  Γ1  (cons ( x ,  t )  Γ2 ) .
(** definitions *)

(* defns bigV *)
Inductive bigV : subst -> elim -> intro -> Prop :=    (* defn bigV *)
 | bigV_var : forall (ρ:subst) (x:var) (v:intro),
     Assoc.find x ρ = Some v  ->
     bigV ρ (V_var x) v
 | bigV_fst : forall (ρ:subst) (V:elim) (v1 v2:intro),
     bigV ρ V (v_fanout v1 v2) ->
     bigV ρ (V_fst V) v1
 | bigV_snd : forall (ρ:subst) (V:elim) (v2 v1:intro),
     bigV ρ V (v_fanout v1 v2) ->
     bigV ρ (V_snd V) v2.
(** definitions *)

(* defns bigv *)
Inductive bigv : subst -> intro -> intro -> Prop :=    (* defn bigv *)
 | bigv_axiom : forall (ρ:subst) (K:axiom) (v v':intro),
     bigv ρ v v' ->
     bigv ρ (v_axiom K v) (v_axiom K v')
 | bigv_tt : forall (ρ:subst),
     bigv ρ v_tt v_tt
 | bigv_fanout : forall (ρ:subst) (v1 v2 v1' v2':intro),
     bigv ρ v1 v1' ->
     bigv ρ v2 v2' ->
     bigv ρ (v_fanout v1 v2) (v_fanout v1' v2')
 | bigv_neu : forall (ρ:subst) (V:elim) (v:intro),
     bigV ρ V v ->
     bigv ρ (v_neu V) v.
(** definitions *)

(* defns lfind *)
Inductive lmem : var -> usage -> usage -> Prop :=    (* defn lmem *)
 | lmem_eq : forall (x:var) (Δ:usage),
     lmem x  (cons ( x ,  u_unused )  Δ )   (cons ( x ,  u_used )  Δ ) 
 | lmem_ne : forall (x:var) (Δ:usage) (y:var) (u:use) (Δ':usage),
      ( x  <>  y )  ->
     lmem x Δ Δ' ->
     lmem x  (cons ( y ,  u )  Δ )   (cons ( y ,  u )  Δ' ) .
(** definitions *)

(* defns scope *)
Inductive se : usage -> redex -> usage -> Prop :=    (* defn se *)
 | se_var : forall (Δ:usage) (x:var) (Δ':usage),
     lmem x Δ Δ' ->
     se Δ (e_var x) Δ'
 | se_app : forall (Δ1:usage) (e1:redex) (E2:context) (Δ3 Δ2:usage),
     se Δ1 e1 Δ2 ->
     sE Δ2 E2 Δ3 ->
     se Δ1 (e_app e1 E2) Δ3
 | se_step : forall (Δ1:usage) (e1:redex) (E2:context) (t:type) (Δ3 Δ2:usage),
     se Δ1 e1 Δ2 ->
     sE Δ2 E2 Δ3 ->
     se Δ1 (e_step e1 E2 t) Δ3
 | se_let : forall (Δ1:usage) (x y:var) (e1:redex) (E2:context) (t3:type) (Δ3 Δ2:usage),
     se Δ1 e1 Δ2 ->
     sE  (cons ( y ,  u_unused )   (cons ( x ,  u_unused )  Δ2 )  )  E2  (cons ( y ,  u_used )   (cons ( x ,  u_used )  Δ3 )  )  ->
     se Δ1 (e_let x y e1 E2 t3) Δ3
 | se_cut : forall (Δ:usage) (E:context) (t:type) (Δ':usage),
     sE Δ E Δ' ->
     se Δ (e_cut E t) Δ'
with sE : usage -> context -> usage -> Prop :=    (* defn sE *)
 | sE_axiom : forall (Δ:usage) (K:axiom) (E:context) (Δ':usage),
     sE Δ E Δ' ->
     sE Δ (E_axiom K E) Δ'
 | sE_lam : forall (Δ:usage) (x:var) (E:context) (Δ':usage),
     sE  (cons ( x ,  u_unused )  Δ )  E  (cons ( x ,  u_used )  Δ' )  ->
     sE Δ (E_lam x E) Δ'
 | sE_tt : forall (Δ:usage),
     sE Δ E_tt Δ
 | sE_fanout : forall (Δ1:usage) (E1 E2:context) (Δ3 Δ2:usage),
     sE Δ1 E1 Δ2 ->
     sE Δ2 E2 Δ3 ->
     sE Δ1 (E_fanout E1 E2) Δ3
 | sE_neu : forall (Δ:usage) (e:redex) (Δ':usage),
     se Δ e Δ' ->
     sE Δ (E_neu e) Δ'.
(** definitions *)

(* defns judge_context *)
Inductive infer : globals -> environment -> redex -> type -> Prop :=    (* defn infer *)
 | infer_var : forall (X:globals) (Γ:environment) (x:var) (t:type),
     mem x t Γ ->
     infer X Γ (e_var x) t
 | infer_app : forall (X:globals) (Γ:environment) (e1:redex) (E2:context) (t2 t1:type),
     infer X Γ e1 (t_prod t1 t2) ->
     check X Γ E2 t1 ->
     infer X Γ (e_app e1 E2) t2
 | infer_step : forall (X:globals) (Γ:environment) (e1:redex) (E2:context) (t:type),
     infer X Γ e1 t_unit ->
     check X Γ E2 t ->
     infer X Γ (e_step e1 E2 t) t
 | infer_let : forall (X:globals) (Γ:environment) (x y:var) (e1:redex) (E2:context) (t3 t1 t2:type),
     infer X Γ e1 (t_prod t1 t2) ->
     check X  (cons ( y ,  t2 )   (cons ( x ,  t1 )  Γ )  )  E2 t3 ->
     infer X Γ (e_let x y e1 E2 t3) t3
 | infer_cut : forall (X:globals) (Γ:environment) (E:context) (t:type),
     check X Γ E t ->
     infer X Γ (e_cut E t) t
with check : globals -> environment -> context -> type -> Prop :=    (* defn check *)
 | check_axiom : forall (X:globals) (Γ:environment) (K:axiom) (E:context) (A:tyvar) (t:type),
     Assoc.find K X = Some (g_relation t A)  ->
     check X Γ E t ->
     check X Γ (E_axiom K E) (t_var A)
 | check_inject : forall (X:globals) (Γ:environment) (v:intro) (t:type),
     Jv X Γ v t ->
     check X Γ (E_inj v) t
 | check_lam : forall (X:globals) (Γ:environment) (x:var) (E:context) (t1 t2:type),
     check X  (cons ( x ,  t1 )  Γ )  E t2 ->
     check X Γ (E_lam x E) (t_prod t1 t2)
 | check_tt : forall (X:globals) (Γ:environment),
     check X Γ E_tt t_unit
 | check_fanout : forall (X:globals) (Γ:environment) (E1 E2:context) (t1 t2:type),
     check X Γ E1 t1 ->
     check X Γ E2 t2 ->
     check X Γ (E_fanout E1 E2) (t_prod t1 t2)
 | check_neu : forall (X:globals) (Γ:environment) (e:redex) (t:type),
     infer X Γ e t ->
     check X Γ (E_neu e) t.
(** definitions *)

(* defns pfind *)
Inductive pmem : var -> intro -> subst -> subst -> Prop :=    (* defn pmem *)
 | pmem_eq : forall (x:var) (v:intro) (ρ:subst),
     pmem x v  (cons ( x ,  v )  ρ )   (cons ( x ,  v_tt )  ρ ) 
 | pmem_ne : forall (x:var) (v:intro) (ρ:subst) (y:var) (v':intro) (ρ':subst),
      ( x  <>  y )  ->
     pmem x v ρ ρ' ->
     pmem x v  (cons ( y ,  v' )  ρ )   (cons ( y ,  v' )  ρ' ) .
(** definitions *)

(* defns sat *)
Inductive produces : subst -> redex -> intro -> subst -> Prop :=    (* defn produces *)
 | produces_var : forall (ρ:subst) (x:var) (v:intro) (ρ':subst),
     pmem x v ρ ρ' ->
     produces ρ (e_var x) v ρ'
 | produces_step : forall (ρ1:subst) (e:redex) (E':context) (t:type) (v:intro) (ρ3 ρ2:subst),
     produces ρ1 e v_tt ρ2 ->
     accepts ρ2 E' v ρ3 ->
     produces ρ1  ( (e_step e E' t) )  v ρ3
 | produces_let : forall (ρ1:subst) (x y:var) (e:redex) (E':context) (t:type) (v2:intro) (ρ3:subst) (v0 v1:intro) (ρ2:subst) (v0' v1':intro),
     produces ρ1 e (v_fanout v0 v1) ρ2 ->
     accepts  (cons ( y ,  v1 )   (cons ( x ,  v0 )  ρ2 )  )  E' v2  (cons ( y ,  v1' )   (cons ( x ,  v0' )  ρ3 )  )  ->
     produces ρ1  ( (e_let x y e E' t) )  v2 ρ3
 | produces_app : forall (ρ1:subst) (e:redex) (E':context) (v':intro) (ρ3:subst) (v:intro) (ρ2:subst),
     produces ρ1 e (v_fanout v v') ρ2 ->
     accepts ρ2 E' v ρ3 ->
     produces ρ1  ( (e_app e E') )  v' ρ3
 | produces_cut : forall (ρ1:subst) (E:context) (t:type) (v:intro) (ρ2:subst),
     accepts ρ1 E v ρ2 ->
     produces ρ1  ( (e_cut E t) )  v ρ2
with accepts : subst -> context -> intro -> subst -> Prop :=    (* defn accepts *)
 | accepts_inject : forall (ρ:subst) (v:intro),
     accepts ρ (E_inj v) v ρ
 | accepts_tt : forall (ρ:subst),
     accepts ρ E_tt v_tt ρ
 | accepts_fanout : forall (ρ1:subst) (E E':context) (v v':intro) (ρ3 ρ2:subst),
     accepts ρ1 E v ρ2 ->
     accepts ρ2 E' v' ρ3 ->
     accepts ρ1  ( (E_fanout E E') )  (v_fanout v v') ρ3
 | accepts_lam : forall (ρ1:subst) (x:var) (E:context) (v1 v2:intro) (ρ2:subst) (v1':intro),
     accepts  (cons ( x ,  v1 )  ρ1 )  E v2  (cons ( x ,  v1' )  ρ2 )  ->
     accepts ρ1  ( (E_lam x E) )  (v_fanout v1 v2) ρ2
 | accepts_neu : forall (ρ1:subst) (e:redex) (v:intro) (ρ2:subst),
     produces ρ1 e v ρ2 ->
     accepts ρ1  ( (E_neu e) )  v ρ2.


