(* generated by Ott 0.25, locally-nameless lngen from: k.ott *)
Require Import Metatheory.
(** syntax *)
Definition a := var. (*r type variables *)
Definition x := var. (*r variables *)
Definition i := nat. (*r integer literals *)

Inductive t : Set :=  (*r types *)
 | t_var_b (_:nat)
 | t_var_f (a5:a)
 | t_int : t
 | t_void : t
 | t_arr (t1:t) (t2:t)
 | t_all (t5:t)
 | t_prod (t1:t) (t2:t).

Inductive p : Set :=  (*r primitives *)
 | p_plus : p
 | p_minus : p.

Inductive e : Set :=  (*r annotated terms *)
 | e_ann (u5:u) (t5:t)
with u : Set :=  (*r raw terms *)
 | u_var_b (_:nat)
 | u_var_f (x5:x)
 | u_int (i5:i)
 | u_lam (t5:t) (e5:e)
 | u_app (e1:e) (e2:e)
 | u_pair (e1:e) (e2:e)
 | u_prl (e5:e)
 | u_prr (e5:e)
 | u_prim (e1:e) (p5:p) (e2:e)
 | u_if0 (e1:e) (e2:e) (e3:e)
 | u_let (e5:e) (u5:u)
 | u_halt (e5:e).

Definition D : Set := list a.

Definition G : Set := list (x * t).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_t_wrt_t_rec (k:nat) (s5:t) (s_6:t) {struct s_6}: t :=
  match s_6 with
  | (t_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => t_var_b nat
        | inleft (right _) => s5
        | inright _ => t_var_b (nat - 1)
      end
  | (t_var_f a5) => t_var_f a5
  | t_int => t_int 
  | t_void => t_void 
  | (t_arr t1 t2) => t_arr (open_t_wrt_t_rec k s5 t1) (open_t_wrt_t_rec k s5 t2)
  | (t_all t5) => t_all (open_t_wrt_t_rec (S k) s5 t5)
  | (t_prod t1 t2) => t_prod (open_t_wrt_t_rec k s5 t1) (open_t_wrt_t_rec k s5 t2)
end.

Fixpoint open_u_wrt_u_rec (k:nat) (u_6:u) (u__7:u) {struct u__7}: u :=
  match u__7 with
  | (u_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => u_var_b nat
        | inleft (right _) => u_6
        | inright _ => u_var_b (nat - 1)
      end
  | (u_var_f x5) => u_var_f x5
  | (u_int i5) => u_int i5
  | (u_lam t5 e5) => u_lam t5 (open_e_wrt_u_rec (S k) u_6 e5)
  | (u_app e1 e2) => u_app (open_e_wrt_u_rec k u_6 e1) (open_e_wrt_u_rec k u_6 e2)
  | (u_pair e1 e2) => u_pair (open_e_wrt_u_rec k u_6 e1) (open_e_wrt_u_rec k u_6 e2)
  | (u_prl e5) => u_prl (open_e_wrt_u_rec k u_6 e5)
  | (u_prr e5) => u_prr (open_e_wrt_u_rec k u_6 e5)
  | (u_prim e1 p5 e2) => u_prim (open_e_wrt_u_rec k u_6 e1) p5 (open_e_wrt_u_rec k u_6 e2)
  | (u_if0 e1 e2 e3) => u_if0 (open_e_wrt_u_rec k u_6 e1) (open_e_wrt_u_rec k u_6 e2) (open_e_wrt_u_rec k u_6 e3)
  | (u_let e5 u5) => u_let (open_e_wrt_u_rec k u_6 e5) (open_u_wrt_u_rec (S k) u_6 u5)
  | (u_halt e5) => u_halt (open_e_wrt_u_rec k u_6 e5)
end
with open_e_wrt_u_rec (k:nat) (u_6:u) (e_6:e) : e :=
  match e_6 with
  | (e_ann u5 t5) => e_ann (open_u_wrt_u_rec k u_6 u5) t5
end.

Fixpoint open_u_wrt_t_rec (k:nat) (s5:t) (u_6:u) {struct u_6}: u :=
  match u_6 with
  | (u_var_b nat) => u_var_b nat
  | (u_var_f x5) => u_var_f x5
  | (u_int i5) => u_int i5
  | (u_lam t5 e5) => u_lam (open_t_wrt_t_rec k s5 t5) (open_e_wrt_t_rec k s5 e5)
  | (u_app e1 e2) => u_app (open_e_wrt_t_rec k s5 e1) (open_e_wrt_t_rec k s5 e2)
  | (u_pair e1 e2) => u_pair (open_e_wrt_t_rec k s5 e1) (open_e_wrt_t_rec k s5 e2)
  | (u_prl e5) => u_prl (open_e_wrt_t_rec k s5 e5)
  | (u_prr e5) => u_prr (open_e_wrt_t_rec k s5 e5)
  | (u_prim e1 p5 e2) => u_prim (open_e_wrt_t_rec k s5 e1) p5 (open_e_wrt_t_rec k s5 e2)
  | (u_if0 e1 e2 e3) => u_if0 (open_e_wrt_t_rec k s5 e1) (open_e_wrt_t_rec k s5 e2) (open_e_wrt_t_rec k s5 e3)
  | (u_let e5 u5) => u_let (open_e_wrt_t_rec k s5 e5) (open_u_wrt_t_rec k s5 u5)
  | (u_halt e5) => u_halt (open_e_wrt_t_rec k s5 e5)
end
with open_e_wrt_t_rec (k:nat) (s5:t) (e_6:e) : e :=
  match e_6 with
  | (e_ann u5 t5) => e_ann (open_u_wrt_t_rec k s5 u5) (open_t_wrt_t_rec k s5 t5)
end.

Definition open_u_wrt_u u_6 u__7 := open_u_wrt_u_rec 0 u__7 u_6.

Definition open_e_wrt_u u_6 e_6 := open_e_wrt_u_rec 0 e_6 u_6.

Definition open_u_wrt_t s5 u_6 := open_u_wrt_t_rec 0 u_6 s5.

Definition open_e_wrt_t s5 e_6 := open_e_wrt_t_rec 0 e_6 s5.

Definition open_t_wrt_t s5 s_6 := open_t_wrt_t_rec 0 s_6 s5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_t *)
Inductive lc_t : t -> Prop :=    (* defn lc_t *)
 | lc_t_var_f : forall (a5:a),
     (lc_t (t_var_f a5))
 | lc_t_int : 
     (lc_t t_int)
 | lc_t_void : 
     (lc_t t_void)
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

(* defns LC_u_e *)
Inductive lc_u : u -> Prop :=    (* defn lc_u *)
 | lc_u_var_f : forall (x5:x),
     (lc_u (u_var_f x5))
 | lc_u_int : forall (i5:i),
     (lc_u (u_int i5))
 | lc_u_lam : forall (t5:t) (e5:e),
     (lc_t t5) ->
      ( forall x5 , lc_e  ( open_e_wrt_u e5 (u_var_f x5) )  )  ->
     (lc_u (u_lam t5 e5))
 | lc_u_app : forall (e1 e2:e),
     (lc_e e1) ->
     (lc_e e2) ->
     (lc_u (u_app e1 e2))
 | lc_u_pair : forall (e1 e2:e),
     (lc_e e1) ->
     (lc_e e2) ->
     (lc_u (u_pair e1 e2))
 | lc_u_prl : forall (e5:e),
     (lc_e e5) ->
     (lc_u (u_prl e5))
 | lc_u_prr : forall (e5:e),
     (lc_e e5) ->
     (lc_u (u_prr e5))
 | lc_u_prim : forall (e1:e) (p5:p) (e2:e),
     (lc_e e1) ->
     (lc_e e2) ->
     (lc_u (u_prim e1 p5 e2))
 | lc_u_if0 : forall (e1 e2 e3:e),
     (lc_e e1) ->
     (lc_e e2) ->
     (lc_e e3) ->
     (lc_u (u_if0 e1 e2 e3))
 | lc_u_let : forall (e5:e) (u5:u),
     (lc_e e5) ->
      ( forall x5 , lc_u  ( open_u_wrt_u u5 (u_var_f x5) )  )  ->
     (lc_u (u_let e5 u5))
 | lc_u_halt : forall (e5:e),
     (lc_e e5) ->
     (lc_u (u_halt e5))
with lc_e : e -> Prop :=    (* defn lc_e *)
 | lc_e_ann : forall (u5:u) (t5:t),
     (lc_u u5) ->
     (lc_t t5) ->
     (lc_e (e_ann u5 t5)).
(** free variables *)
Fixpoint tt_fv_t (s5:t) : vars :=
  match s5 with
  | (t_var_b nat) => {}
  | (t_var_f a5) => {{a5}}
  | t_int => {}
  | t_void => {}
  | (t_arr t1 t2) => (tt_fv_t t1) \u (tt_fv_t t2)
  | (t_all t5) => (tt_fv_t t5)
  | (t_prod t1 t2) => (tt_fv_t t1) \u (tt_fv_t t2)
end.

Fixpoint tt_fv_u (u_6:u) : vars :=
  match u_6 with
  | (u_var_b nat) => {}
  | (u_var_f x5) => {}
  | (u_int i5) => {}
  | (u_lam t5 e5) => (tt_fv_t t5) \u (tt_fv_e e5)
  | (u_app e1 e2) => (tt_fv_e e1) \u (tt_fv_e e2)
  | (u_pair e1 e2) => (tt_fv_e e1) \u (tt_fv_e e2)
  | (u_prl e5) => (tt_fv_e e5)
  | (u_prr e5) => (tt_fv_e e5)
  | (u_prim e1 p5 e2) => (tt_fv_e e1) \u (tt_fv_e e2)
  | (u_if0 e1 e2 e3) => (tt_fv_e e1) \u (tt_fv_e e2) \u (tt_fv_e e3)
  | (u_let e5 u5) => (tt_fv_e e5) \u (tt_fv_u u5)
  | (u_halt e5) => (tt_fv_e e5)
end
with tt_fv_e (e_6:e) : vars :=
  match e_6 with
  | (e_ann u5 t5) => (tt_fv_u u5) \u (tt_fv_t t5)
end.

Fixpoint u_fv_u (u_6:u) : vars :=
  match u_6 with
  | (u_var_b nat) => {}
  | (u_var_f x5) => {{x5}}
  | (u_int i5) => {}
  | (u_lam t5 e5) => (u_fv_e e5)
  | (u_app e1 e2) => (u_fv_e e1) \u (u_fv_e e2)
  | (u_pair e1 e2) => (u_fv_e e1) \u (u_fv_e e2)
  | (u_prl e5) => (u_fv_e e5)
  | (u_prr e5) => (u_fv_e e5)
  | (u_prim e1 p5 e2) => (u_fv_e e1) \u (u_fv_e e2)
  | (u_if0 e1 e2 e3) => (u_fv_e e1) \u (u_fv_e e2) \u (u_fv_e e3)
  | (u_let e5 u5) => (u_fv_e e5) \u (u_fv_u u5)
  | (u_halt e5) => (u_fv_e e5)
end
with u_fv_e (e_6:e) : vars :=
  match e_6 with
  | (e_ann u5 t5) => (u_fv_u u5)
end.

(** substitutions *)
Fixpoint t_subst_t (s5:t) (a_6:a) (s_6:t) {struct s_6} : t :=
  match s_6 with
  | (t_var_b nat) => t_var_b nat
  | (t_var_f a5) => (if eq_var a5 a_6 then s5 else (t_var_f a5))
  | t_int => t_int 
  | t_void => t_void 
  | (t_arr t1 t2) => t_arr (t_subst_t s5 a_6 t1) (t_subst_t s5 a_6 t2)
  | (t_all t5) => t_all (t_subst_t s5 a_6 t5)
  | (t_prod t1 t2) => t_prod (t_subst_t s5 a_6 t1) (t_subst_t s5 a_6 t2)
end.

Fixpoint u_subst_u (u_6:u) (x_6:x) (u__7:u) {struct u__7} : u :=
  match u__7 with
  | (u_var_b nat) => u_var_b nat
  | (u_var_f x5) => (if eq_var x5 x_6 then u_6 else (u_var_f x5))
  | (u_int i5) => u_int i5
  | (u_lam t5 e5) => u_lam t5 (u_subst_e u_6 x_6 e5)
  | (u_app e1 e2) => u_app (u_subst_e u_6 x_6 e1) (u_subst_e u_6 x_6 e2)
  | (u_pair e1 e2) => u_pair (u_subst_e u_6 x_6 e1) (u_subst_e u_6 x_6 e2)
  | (u_prl e5) => u_prl (u_subst_e u_6 x_6 e5)
  | (u_prr e5) => u_prr (u_subst_e u_6 x_6 e5)
  | (u_prim e1 p5 e2) => u_prim (u_subst_e u_6 x_6 e1) p5 (u_subst_e u_6 x_6 e2)
  | (u_if0 e1 e2 e3) => u_if0 (u_subst_e u_6 x_6 e1) (u_subst_e u_6 x_6 e2) (u_subst_e u_6 x_6 e3)
  | (u_let e5 u5) => u_let (u_subst_e u_6 x_6 e5) (u_subst_u u_6 x_6 u5)
  | (u_halt e5) => u_halt (u_subst_e u_6 x_6 e5)
end
with u_subst_e (u_6:u) (x_6:x) (e_6:e) {struct e_6} : e :=
  match e_6 with
  | (e_ann u5 t5) => e_ann (u_subst_u u_6 x_6 u5) t5
end.

Fixpoint t_subst_u (s5:t) (a5:a) (u_6:u) {struct u_6} : u :=
  match u_6 with
  | (u_var_b nat) => u_var_b nat
  | (u_var_f x5) => u_var_f x5
  | (u_int i5) => u_int i5
  | (u_lam t5 e5) => u_lam (t_subst_t s5 a5 t5) (t_subst_e s5 a5 e5)
  | (u_app e1 e2) => u_app (t_subst_e s5 a5 e1) (t_subst_e s5 a5 e2)
  | (u_pair e1 e2) => u_pair (t_subst_e s5 a5 e1) (t_subst_e s5 a5 e2)
  | (u_prl e5) => u_prl (t_subst_e s5 a5 e5)
  | (u_prr e5) => u_prr (t_subst_e s5 a5 e5)
  | (u_prim e1 p5 e2) => u_prim (t_subst_e s5 a5 e1) p5 (t_subst_e s5 a5 e2)
  | (u_if0 e1 e2 e3) => u_if0 (t_subst_e s5 a5 e1) (t_subst_e s5 a5 e2) (t_subst_e s5 a5 e3)
  | (u_let e5 u5) => u_let (t_subst_e s5 a5 e5) (t_subst_u s5 a5 u5)
  | (u_halt e5) => u_halt (t_subst_e s5 a5 e5)
end
with t_subst_e (s5:t) (a5:a) (e_6:e) {struct e_6} : e :=
  match e_6 with
  | (e_ann u5 t5) => e_ann (t_subst_u s5 a5 u5) (t_subst_t s5 a5 t5)
end.


(** definitions *)

(* defns F *)
Inductive F_type : D -> t -> Prop :=    (* defn type *)
 | F_type_var : forall (D5:D) (a5:a),
      In  a5   D5  ->
     F_type D5 (t_var_f a5)
 | F_type_int : forall (D5:D),
     F_type D5 t_int
 | F_type_arr : forall (D5:D) (t1 t2:t),
     F_type D5 t1 ->
     F_type D5 t2 ->
     F_type D5 (t_arr t1 t2)
 | F_type_all : forall (L:vars) (D5:D) (t5:t),
      ( forall a5 , a5 \notin  L  -> F_type  ( a5  ::  D5 )   ( open_t_wrt_t t5 (t_var_f a5) )  )  ->
     F_type D5 (t_all t5)
 | F_type_prod : forall (D5:D) (t1 t2:t),
     F_type D5 t1 ->
     F_type D5 t2 ->
     F_type D5 (t_prod t1 t2)
with F_ant : D -> G -> e -> t -> Prop :=    (* defn ant *)
 | F_ant_ann : forall (D5:D) (G5:G) (u5:u) (t5:t),
     F_term D5 G5 u5 t5 ->
     F_ant D5 G5 (e_ann u5 t5) t5
with F_term : D -> G -> u -> t -> Prop :=    (* defn term *)
 | F_term_var : forall (D5:D) (G5:G) (x5:x) (t5:t),
     F_type D5 t5 ->
      In ( x5 ,  t5 )  G5  ->
     F_term D5 G5 (u_var_f x5) t5
 | F_term_int : forall (D5:D) (G5:G) (i5:i),
     F_term D5 G5 (u_int i5) t_int
 | F_term_lam : forall (L:vars) (D5:D) (G5:G) (t1:t) (e5:e) (t2:t),
     F_type D5 t1 ->
      ( forall x1 , x1 \notin  L  -> F_ant D5  (( x1 ,  t1 ) ::  G5 )   ( open_e_wrt_u e5 (u_var_f x1) )  t2 )  ->
     F_term D5 G5 (u_lam t1 e5) (t_arr t1 t2)
 | F_term_app : forall (D5:D) (G5:G) (e1 e2:e) (t2 t1:t),
     F_ant D5 G5 e1 (t_arr t1 t2) ->
     F_ant D5 G5 e2 t1 ->
     F_term D5 G5 (u_app e1 e2) t2
 | F_term_pair : forall (D5:D) (G5:G) (e1 e2:e) (t1 t2:t),
     F_ant D5 G5 e1 t1 ->
     F_ant D5 G5 e2 t2 ->
     F_term D5 G5 (u_pair e1 e2) (t_prod t1 t2)
 | F_term_prl : forall (D5:D) (G5:G) (e5:e) (t1 t2:t),
     F_ant D5 G5 e5 (t_prod t1 t2) ->
     F_term D5 G5 (u_prl e5) t1
 | F_term_prr : forall (D5:D) (G5:G) (e5:e) (t2 t1:t),
     F_ant D5 G5 e5 (t_prod t1 t2) ->
     F_term D5 G5 (u_prr e5) t2
 | F_term_prim : forall (D5:D) (G5:G) (e1:e) (p5:p) (e2:e),
     F_ant D5 G5 e1 t_int ->
     F_ant D5 G5 e2 t_int ->
     F_term D5 G5 (u_prim e1 p5 e2) t_int
 | F_term_if0 : forall (D5:D) (G5:G) (e1 e2 e3:e) (t5:t),
     F_ant D5 G5 e1 t_int ->
     F_ant D5 G5 e2 t5 ->
     F_ant D5 G5 e3 t5 ->
     F_term D5 G5 (u_if0 e1 e2 e3) t5.

(* defns K *)
Inductive K_type : D -> t -> Prop :=    (* defn type *)
 | K_type_var : forall (D5:D) (a5:a),
      In  a5   D5  ->
     K_type D5 (t_var_f a5)
 | K_type_int : forall (D5:D),
     K_type D5 t_int
 | K_type_arr : forall (D5:D) (t5:t),
     K_type D5 t5 ->
     K_type D5 (t_arr t5 t_void)
 | K_type_prod : forall (D5:D) (t1 t2:t),
     K_type D5 t1 ->
     K_type D5 t2 ->
     K_type D5 (t_prod t1 t2)
with K_ant : D -> G -> e -> t -> Prop :=    (* defn ant *)
 | K_ant_ann : forall (D5:D) (G5:G) (u5:u) (t5:t),
     K_term D5 G5 u5 t5 ->
     K_ant D5 G5 (e_ann u5 t5) t5
with K_term : D -> G -> u -> t -> Prop :=    (* defn term *)
 | K_term_var : forall (D5:D) (G5:G) (x5:x) (t5:t),
     K_type D5 t5 ->
      In ( x5 ,  t5 )  G5  ->
     K_term D5 G5 (u_var_f x5) t5
 | K_term_int : forall (D5:D) (G5:G) (i5:i),
     K_term D5 G5 (u_int i5) t_int
 | K_term_Lam : forall (L:vars) (D5:D) (G5:G) (t5:t) (e5:e),
      ( forall x5 , x5 \notin  L  -> K_ant D5  (( x5 ,  t5 ) ::  G5 )   ( open_e_wrt_u e5 (u_var_f x5) )  t_void )  ->
     K_term D5 G5 (u_lam t5 e5) (t_arr t5 t_void)
 | K_term_pair : forall (D5:D) (G5:G) (e1 e2:e) (t1 t2:t),
     K_ant D5 G5 e1 t1 ->
     K_ant D5 G5 e2 t2 ->
     K_term D5 G5 (u_pair e1 e2) (t_prod t1 t2)
 | K_term_let : forall (L:vars) (D5:D) (G5:G) (e5:e) (u5:u) (t5:t),
     K_ant D5 G5 e5 t5 ->
      ( forall x5 , x5 \notin  L  -> K_term D5  (( x5 ,  t5 ) ::  G5 )   ( open_u_wrt_u u5 (u_var_f x5) )  t_void )  ->
     K_term D5 G5 (u_let e5 u5) t_void
 | K_term_prl : forall (D5:D) (G5:G) (e5:e) (t1 t2:t),
     K_ant D5 G5 e5 (t_prod t1 t2) ->
     K_term D5 G5 (u_prl e5) t1
 | K_term_prr : forall (D5:D) (G5:G) (e5:e) (t2 t1:t),
     K_ant D5 G5 e5 (t_prod t1 t2) ->
     K_term D5 G5 (u_prr e5) t2
 | K_term_prim : forall (D5:D) (G5:G) (e1:e) (p5:p) (e2:e),
     K_ant D5 G5 e1 t_int ->
     K_ant D5 G5 e2 t_int ->
     K_term D5 G5 (u_prim e1 p5 e2) t_int
 | K_term_app : forall (D5:D) (G5:G) (e' e5:e) (t5:t),
     K_ant D5 G5 e' (t_arr t5 t_void) ->
     K_ant D5 G5 e5 t5 ->
     K_term D5 G5 (u_app e' e5) t_void
 | K_term_if0 : forall (D5:D) (G5:G) (e_5 e1 e2:e),
     K_ant D5 G5 e_5 t_int ->
     K_ant D5 G5 e1 t_void ->
     K_ant D5 G5 e2 t_void ->
     K_term D5 G5 (u_if0 e_5 e1 e2) t_void
 | K_term_halt : forall (D5:D) (G5:G) (e5:e) (t5:t),
     K_ant D5 G5 e5 t5 ->
     K_term D5 G5 (u_halt e5) t_void.