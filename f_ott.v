(* generated by Ott 0.25, locally-nameless lngen from: f.ott *)
Require Import Metalib.Metatheory.
(** syntax *)
Definition a := var. (*r type variables *)
Definition x := var. (*r variables *)
Definition i := nat. (*r integer literals *)

Inductive t : Set :=  (*r types *)
 | t_var_b (_:nat)
 | t_var_f (a5:a)
 | t_int : t
 | t_arr (t1:t) (t2:t)
 | t_all (t5:t)
 | t_prod (t1:t) (t2:t).

Inductive p : Set :=  (*r primitives *)
 | p_plus : p
 | p_minus : p.

Definition D : Set := list a.

Inductive u : Set :=  (*r terms *)
 | u_var_b (_:nat)
 | u_var_f (x5:x)
 | u_int (i5:i)
 | u_fix (t1:t) (t2:t) (e:u)
 | u_lam (t1:t) (e:u)
 | u_app (e1:u) (e2:u)
 | u_tlam (e:u)
 | u_tapp (e:u) (t5:t)
 | u_pair (e1:u) (e2:u)
 | u_prl (e:u)
 | u_prr (e:u)
 | u_prim (e1:u) (p5:p) (e2:u)
 | u_if0 (e1:u) (e2:u) (e3:u)
 | u_ann (u5:u) (t5:t) (*r annotated terms *).

Definition G : Set := list (x * t).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_t_wrt_t_rec (k:nat) (t_6:t) (t__7:t) {struct t__7}: t :=
  match t__7 with
  | (t_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => t_var_b nat
        | inleft (right _) => t_6
        | inright _ => t_var_b (nat - 1)
      end
  | (t_var_f a5) => t_var_f a5
  | t_int => t_int 
  | (t_arr t1 t2) => t_arr (open_t_wrt_t_rec k t_6 t1) (open_t_wrt_t_rec k t_6 t2)
  | (t_all t5) => t_all (open_t_wrt_t_rec (S k) t_6 t5)
  | (t_prod t1 t2) => t_prod (open_t_wrt_t_rec k t_6 t1) (open_t_wrt_t_rec k t_6 t2)
end.

Fixpoint open_u_wrt_u_rec (k:nat) (e_5:u) (e__6:u) {struct e__6}: u :=
  match e__6 with
  | (u_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => u_var_b nat
        | inleft (right _) => e_5
        | inright _ => u_var_b (nat - 1)
      end
  | (u_var_f x5) => u_var_f x5
  | (u_int i5) => u_int i5
  | (u_fix t1 t2 e) => u_fix t1 t2 (open_u_wrt_u_rec (S k) e_5 e)
  | (u_lam t1 e) => u_lam t1 (open_u_wrt_u_rec (S k) e_5 e)
  | (u_app e1 e2) => u_app (open_u_wrt_u_rec k e_5 e1) (open_u_wrt_u_rec k e_5 e2)
  | (u_tlam e) => u_tlam (open_u_wrt_u_rec k e_5 e)
  | (u_tapp e t5) => u_tapp (open_u_wrt_u_rec k e_5 e) t5
  | (u_pair e1 e2) => u_pair (open_u_wrt_u_rec k e_5 e1) (open_u_wrt_u_rec k e_5 e2)
  | (u_prl e) => u_prl (open_u_wrt_u_rec k e_5 e)
  | (u_prr e) => u_prr (open_u_wrt_u_rec k e_5 e)
  | (u_prim e1 p5 e2) => u_prim (open_u_wrt_u_rec k e_5 e1) p5 (open_u_wrt_u_rec k e_5 e2)
  | (u_if0 e1 e2 e3) => u_if0 (open_u_wrt_u_rec k e_5 e1) (open_u_wrt_u_rec k e_5 e2) (open_u_wrt_u_rec k e_5 e3)
  | (u_ann u5 t5) => u_ann (open_u_wrt_u_rec k e_5 u5) t5
end.

Fixpoint open_u_wrt_t_rec (k:nat) (t_6:t) (e_5:u) {struct e_5}: u :=
  match e_5 with
  | (u_var_b nat) => u_var_b nat
  | (u_var_f x5) => u_var_f x5
  | (u_int i5) => u_int i5
  | (u_fix t1 t2 e) => u_fix (open_t_wrt_t_rec k t_6 t1) (open_t_wrt_t_rec k t_6 t2) (open_u_wrt_t_rec k t_6 e)
  | (u_lam t1 e) => u_lam (open_t_wrt_t_rec k t_6 t1) (open_u_wrt_t_rec k t_6 e)
  | (u_app e1 e2) => u_app (open_u_wrt_t_rec k t_6 e1) (open_u_wrt_t_rec k t_6 e2)
  | (u_tlam e) => u_tlam (open_u_wrt_t_rec (S k) t_6 e)
  | (u_tapp e t5) => u_tapp (open_u_wrt_t_rec k t_6 e) (open_t_wrt_t_rec k t_6 t5)
  | (u_pair e1 e2) => u_pair (open_u_wrt_t_rec k t_6 e1) (open_u_wrt_t_rec k t_6 e2)
  | (u_prl e) => u_prl (open_u_wrt_t_rec k t_6 e)
  | (u_prr e) => u_prr (open_u_wrt_t_rec k t_6 e)
  | (u_prim e1 p5 e2) => u_prim (open_u_wrt_t_rec k t_6 e1) p5 (open_u_wrt_t_rec k t_6 e2)
  | (u_if0 e1 e2 e3) => u_if0 (open_u_wrt_t_rec k t_6 e1) (open_u_wrt_t_rec k t_6 e2) (open_u_wrt_t_rec k t_6 e3)
  | (u_ann u5 t5) => u_ann (open_u_wrt_t_rec k t_6 u5) (open_t_wrt_t_rec k t_6 t5)
end.

Definition open_u_wrt_u e_5 e__6 := open_u_wrt_u_rec 0 e__6 e_5.

Definition open_u_wrt_t t_6 e_5 := open_u_wrt_t_rec 0 e_5 t_6.

Definition open_t_wrt_t t_6 t__7 := open_t_wrt_t_rec 0 t__7 t_6.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_t *)
Inductive lc_t : t -> Prop :=    (* defn lc_t *)
 | lc_t_var_f : forall (a5:a),
     (lc_t (t_var_f a5))
 | lc_t_int : 
     (lc_t t_int)
 | lc_t_arr : forall (t1 t2:t),
     (lc_t t1) ->
     (lc_t t2) ->
     (lc_t (t_arr t1 t2))
 | lc_t_all : forall (t5:t),
      ( forall a5 , lc_t  ( open_t_wrt_t t5 (t_var_f a5) )  )  ->
     (lc_t (t_all t5))
 | lc_t_prod : forall (t1 t2:t),
     (lc_t t1) ->
     (lc_t t2) ->
     (lc_t (t_prod t1 t2)).

(* defns LC_u *)
Inductive lc_u : u -> Prop :=    (* defn lc_u *)
 | lc_u_var_f : forall (x5:x),
     (lc_u (u_var_f x5))
 | lc_u_int : forall (i5:i),
     (lc_u (u_int i5))
 | lc_u_fix : forall (t1 t2:t) (e:u),
     (lc_t t1) ->
     (lc_t t2) ->
      ( forall x5 , lc_u  ( open_u_wrt_u e (u_var_f x5) )  )  ->
     (lc_u (u_fix t1 t2 e))
 | lc_u_lam : forall (t1:t) (e:u),
     (lc_t t1) ->
      ( forall x1 , lc_u  ( open_u_wrt_u e (u_var_f x1) )  )  ->
     (lc_u (u_lam t1 e))
 | lc_u_app : forall (e1 e2:u),
     (lc_u e1) ->
     (lc_u e2) ->
     (lc_u (u_app e1 e2))
 | lc_u_tlam : forall (e:u),
      ( forall a5 , lc_u  ( open_u_wrt_t e (t_var_f a5) )  )  ->
     (lc_u (u_tlam e))
 | lc_u_tapp : forall (e:u) (t5:t),
     (lc_u e) ->
     (lc_t t5) ->
     (lc_u (u_tapp e t5))
 | lc_u_pair : forall (e1 e2:u),
     (lc_u e1) ->
     (lc_u e2) ->
     (lc_u (u_pair e1 e2))
 | lc_u_prl : forall (e:u),
     (lc_u e) ->
     (lc_u (u_prl e))
 | lc_u_prr : forall (e:u),
     (lc_u e) ->
     (lc_u (u_prr e))
 | lc_u_prim : forall (e1:u) (p5:p) (e2:u),
     (lc_u e1) ->
     (lc_u e2) ->
     (lc_u (u_prim e1 p5 e2))
 | lc_u_if0 : forall (e1 e2 e3:u),
     (lc_u e1) ->
     (lc_u e2) ->
     (lc_u e3) ->
     (lc_u (u_if0 e1 e2 e3))
 | lc_u_ann : forall (u5:u) (t5:t),
     (lc_u u5) ->
     (lc_t t5) ->
     (lc_u (u_ann u5 t5)).
(** free variables *)
Fixpoint tt_fv_t (t_6:t) : vars :=
  match t_6 with
  | (t_var_b nat) => {}
  | (t_var_f a5) => {{a5}}
  | t_int => {}
  | (t_arr t1 t2) => (tt_fv_t t1) \u (tt_fv_t t2)
  | (t_all t5) => (tt_fv_t t5)
  | (t_prod t1 t2) => (tt_fv_t t1) \u (tt_fv_t t2)
end.

Fixpoint tt_fv_u (e_5:u) : vars :=
  match e_5 with
  | (u_var_b nat) => {}
  | (u_var_f x5) => {}
  | (u_int i5) => {}
  | (u_fix t1 t2 e) => (tt_fv_t t1) \u (tt_fv_t t2) \u (tt_fv_u e)
  | (u_lam t1 e) => (tt_fv_t t1) \u (tt_fv_u e)
  | (u_app e1 e2) => (tt_fv_u e1) \u (tt_fv_u e2)
  | (u_tlam e) => (tt_fv_u e)
  | (u_tapp e t5) => (tt_fv_u e) \u (tt_fv_t t5)
  | (u_pair e1 e2) => (tt_fv_u e1) \u (tt_fv_u e2)
  | (u_prl e) => (tt_fv_u e)
  | (u_prr e) => (tt_fv_u e)
  | (u_prim e1 p5 e2) => (tt_fv_u e1) \u (tt_fv_u e2)
  | (u_if0 e1 e2 e3) => (tt_fv_u e1) \u (tt_fv_u e2) \u (tt_fv_u e3)
  | (u_ann u5 t5) => (tt_fv_u u5) \u (tt_fv_t t5)
end.

Fixpoint e_fv_u (e_5:u) : vars :=
  match e_5 with
  | (u_var_b nat) => {}
  | (u_var_f x5) => {{x5}}
  | (u_int i5) => {}
  | (u_fix t1 t2 e) => (e_fv_u e)
  | (u_lam t1 e) => (e_fv_u e)
  | (u_app e1 e2) => (e_fv_u e1) \u (e_fv_u e2)
  | (u_tlam e) => (e_fv_u e)
  | (u_tapp e t5) => (e_fv_u e)
  | (u_pair e1 e2) => (e_fv_u e1) \u (e_fv_u e2)
  | (u_prl e) => (e_fv_u e)
  | (u_prr e) => (e_fv_u e)
  | (u_prim e1 p5 e2) => (e_fv_u e1) \u (e_fv_u e2)
  | (u_if0 e1 e2 e3) => (e_fv_u e1) \u (e_fv_u e2) \u (e_fv_u e3)
  | (u_ann u5 t5) => (e_fv_u u5)
end.

(** substitutions *)
Fixpoint t_subst_t (t_6:t) (a_6:a) (t__7:t) {struct t__7} : t :=
  match t__7 with
  | (t_var_b nat) => t_var_b nat
  | (t_var_f a5) => (if eq_var a5 a_6 then t_6 else (t_var_f a5))
  | t_int => t_int 
  | (t_arr t1 t2) => t_arr (t_subst_t t_6 a_6 t1) (t_subst_t t_6 a_6 t2)
  | (t_all t5) => t_all (t_subst_t t_6 a_6 t5)
  | (t_prod t1 t2) => t_prod (t_subst_t t_6 a_6 t1) (t_subst_t t_6 a_6 t2)
end.

Fixpoint e_subst_u (e_5:u) (x_6:x) (e__6:u) {struct e__6} : u :=
  match e__6 with
  | (u_var_b nat) => u_var_b nat
  | (u_var_f x5) => (if eq_var x5 x_6 then e_5 else (u_var_f x5))
  | (u_int i5) => u_int i5
  | (u_fix t1 t2 e) => u_fix t1 t2 (e_subst_u e_5 x_6 e)
  | (u_lam t1 e) => u_lam t1 (e_subst_u e_5 x_6 e)
  | (u_app e1 e2) => u_app (e_subst_u e_5 x_6 e1) (e_subst_u e_5 x_6 e2)
  | (u_tlam e) => u_tlam (e_subst_u e_5 x_6 e)
  | (u_tapp e t5) => u_tapp (e_subst_u e_5 x_6 e) t5
  | (u_pair e1 e2) => u_pair (e_subst_u e_5 x_6 e1) (e_subst_u e_5 x_6 e2)
  | (u_prl e) => u_prl (e_subst_u e_5 x_6 e)
  | (u_prr e) => u_prr (e_subst_u e_5 x_6 e)
  | (u_prim e1 p5 e2) => u_prim (e_subst_u e_5 x_6 e1) p5 (e_subst_u e_5 x_6 e2)
  | (u_if0 e1 e2 e3) => u_if0 (e_subst_u e_5 x_6 e1) (e_subst_u e_5 x_6 e2) (e_subst_u e_5 x_6 e3)
  | (u_ann u5 t5) => u_ann (e_subst_u e_5 x_6 u5) t5
end.

Fixpoint t_subst_u (t_6:t) (a_6:a) (e_5:u) {struct e_5} : u :=
  match e_5 with
  | (u_var_b nat) => u_var_b nat
  | (u_var_f x5) => u_var_f x5
  | (u_int i5) => u_int i5
  | (u_fix t1 t2 e) => u_fix (t_subst_t t_6 a_6 t1) (t_subst_t t_6 a_6 t2) (t_subst_u t_6 a_6 e)
  | (u_lam t1 e) => u_lam (t_subst_t t_6 a_6 t1) (t_subst_u t_6 a_6 e)
  | (u_app e1 e2) => u_app (t_subst_u t_6 a_6 e1) (t_subst_u t_6 a_6 e2)
  | (u_tlam e) => u_tlam (t_subst_u t_6 a_6 e)
  | (u_tapp e t5) => u_tapp (t_subst_u t_6 a_6 e) (t_subst_t t_6 a_6 t5)
  | (u_pair e1 e2) => u_pair (t_subst_u t_6 a_6 e1) (t_subst_u t_6 a_6 e2)
  | (u_prl e) => u_prl (t_subst_u t_6 a_6 e)
  | (u_prr e) => u_prr (t_subst_u t_6 a_6 e)
  | (u_prim e1 p5 e2) => u_prim (t_subst_u t_6 a_6 e1) p5 (t_subst_u t_6 a_6 e2)
  | (u_if0 e1 e2 e3) => u_if0 (t_subst_u t_6 a_6 e1) (t_subst_u t_6 a_6 e2) (t_subst_u t_6 a_6 e3)
  | (u_ann u5 t5) => u_ann (t_subst_u t_6 a_6 u5) (t_subst_t t_6 a_6 t5)
end.


(** definitions *)

(* defns Jtype *)
Inductive type : D -> t -> Prop :=    (* defn type *)
 | type_var : forall (D5:D) (a5:a),
      In  a5   D5  ->
     type D5 (t_var_f a5)
 | type_int : forall (D5:D),
     type D5 t_int
 | type_arr : forall (D5:D) (t1 t2:t),
     type D5 t1 ->
     type D5 t2 ->
     type D5 (t_arr t1 t2)
 | type_all : forall (L:vars) (D5:D) (t5:t),
      ( forall a5 , a5 \notin  L  -> type  ( a5  ::  D5 )   ( open_t_wrt_t t5 (t_var_f a5) )  )  ->
     type D5 (t_all t5).

(* defns Jterm *)
Inductive term : D -> G -> u -> t -> Prop :=    (* defn term *)
 | term_ann : forall (D5:D) (G5:G) (u5:u) (t5:t),
     term D5 G5 u5 t5 ->
     term D5 G5 (u_ann u5 t5) t5
 | term_var : forall (D5:D) (G5:G) (x5:x) (t5:t),
     type D5 t5 ->
      In ( x5 ,  t5 )  G5  ->
     term D5 G5 (u_var_f x5) t5
 | term_int : forall (D5:D) (G5:G) (i5:i),
     term D5 G5 (u_int i5) t_int
 | term_lam : forall (L:vars) (D5:D) (G5:G) (t1:t) (u5:u) (t2:t),
     type D5 t1 ->
      ( forall x1 , x1 \notin  L  -> term D5  (( x1 ,  t1 ) ::  G5 )   ( open_u_wrt_u u5 (u_var_f x1) )  t2 )  ->
     term D5 G5 (u_lam t1 u5) (t_arr t1 t2)
 | term_fix : forall (L:vars) (D5:D) (G5:G) (t1 t2:t) (u5:u),
     type D5 t1 ->
     type D5 t2 ->
      ( forall x5 , x5 \notin  L  -> term D5  (( x5 ,  (t_arr t1 t2) ) ::  G5 )   ( open_u_wrt_u u5 (u_var_f x5) )  (t_arr t1 t2) )  ->
     term D5 G5 (u_fix t1 t2 u5) (t_arr t1 t2)
 | term_app : forall (D5:D) (G5:G) (e1 e2:u) (t2 t1:t),
     term D5 G5 e1 (t_arr t1 t2) ->
     term D5 G5 e2 t1 ->
     term D5 G5 (u_app e1 e2) t2
 | term_tlam : forall (L:vars) (D5:D) (G5:G) (e:u) (t5:t),
      ( forall a5 , a5 \notin  L  -> term  ( a5  ::  D5 )  G5  ( open_u_wrt_t e (t_var_f a5) )   ( open_t_wrt_t t5 (t_var_f a5) )  )  ->
     term D5 G5 (u_tlam e) (t_all t5)
 | term_tapp : forall (D5:D) (G5:G) (e:u) (t5 t':t),
     type D5 t5 ->
     term D5 G5 e (t_all t') ->
     term D5 G5 (u_tapp e t5)  (open_t_wrt_t  t' t5 ) 
 | term_pair : forall (D5:D) (G5:G) (e1 e2:u) (t1 t2:t),
     term D5 G5 e1 t1 ->
     term D5 G5 e2 t2 ->
     term D5 G5 (u_pair e1 e2) (t_prod t1 t2)
 | term_prl : forall (D5:D) (G5:G) (e:u) (t1 t2:t),
     term D5 G5 e (t_prod t1 t2) ->
     term D5 G5 (u_prl e) t1
 | term_prr : forall (D5:D) (G5:G) (e:u) (t2 t1:t),
     term D5 G5 e (t_prod t1 t2) ->
     term D5 G5 (u_prr e) t2
 | term_prim : forall (D5:D) (G5:G) (e1:u) (p5:p) (e2:u),
     term D5 G5 e1 t_int ->
     term D5 G5 e2 t_int ->
     term D5 G5 (u_prim e1 p5 e2) t_int
 | term_if0 : forall (D5:D) (G5:G) (e1 e2 e3:u) (t5:t),
     term D5 G5 e1 t_int ->
     term D5 G5 e2 t5 ->
     term D5 G5 e3 t5 ->
     term D5 G5 (u_if0 e1 e2 e3) t5.


(** infrastructure *)
Hint Constructors type term lc_t lc_u.


