Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metatheory.
Require Export LibLNgen.

Require Export k_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme t_ind' := Induction for t Sort Prop.

Definition t_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  t_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme t_rec' := Induction for t Sort Set.

Definition t_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  t_rec' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme p_ind' := Induction for p Sort Prop.

Definition p_mutind :=
  fun H1 H2 H3 =>
  p_ind' H1 H2 H3.

Scheme p_rec' := Induction for p Sort Set.

Definition p_mutrec :=
  fun H1 H2 H3 =>
  p_rec' H1 H2 H3.

Scheme d_ind' := Induction for d Sort Prop
  with e_ind' := Induction for e Sort Prop
  with u_ind' := Induction for u Sort Prop
  with v_ind' := Induction for v Sort Prop.

Definition d_e_u_v_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 =>
  (conj (d_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)
  ((conj (e_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)
  ((conj (u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)
  (v_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)))))).

Scheme d_rec' := Induction for d Sort Set
  with e_rec' := Induction for e Sort Set
  with u_rec' := Induction for u Sort Set
  with v_rec' := Induction for v Sort Set.

Definition d_e_u_v_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 =>
  (pair ((pair ((pair (d_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)
  (e_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)))
  (u_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)))
  (v_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)).


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_t_wrt_t_rec (n1 : nat) (a1 : a) (t1 : t) {struct t1} : t :=
  match t1 with
    | t_var_f a2 => if (a1 == a2) then (t_var_b n1) else (t_var_f a2)
    | t_var_b n2 => if (lt_ge_dec n2 n1) then (t_var_b n2) else (t_var_b (S n2))
    | t_int => t_int
    | t_void => t_void
    | t_arr t2 t3 => t_arr (close_t_wrt_t_rec n1 a1 t2) (close_t_wrt_t_rec n1 a1 t3)
    | t_all t2 => t_all (close_t_wrt_t_rec (S n1) a1 t2)
    | t_prod t2 t3 => t_prod (close_t_wrt_t_rec n1 a1 t2) (close_t_wrt_t_rec n1 a1 t3)
  end.

Definition close_t_wrt_t a1 t1 := close_t_wrt_t_rec 0 a1 t1.

Fixpoint close_d_wrt_t_rec (n1 : nat) (a1 : a) (d1 : d) {struct d1} : d :=
  match d1 with
    | d_val v1 => d_val (close_v_wrt_t_rec n1 a1 v1)
    | d_prl v1 => d_prl (close_v_wrt_t_rec n1 a1 v1)
    | d_prr v1 => d_prr (close_v_wrt_t_rec n1 a1 v1)
    | d_prim v1 p1 v2 => d_prim (close_v_wrt_t_rec n1 a1 v1) p1 (close_v_wrt_t_rec n1 a1 v2)
  end

with close_e_wrt_t_rec (n1 : nat) (a1 : a) (e1 : e) {struct e1} : e :=
  match e1 with
    | e_let d1 e2 => e_let (close_d_wrt_t_rec n1 a1 d1) (close_e_wrt_t_rec n1 a1 e2)
    | e_app v1 v2 => e_app (close_v_wrt_t_rec n1 a1 v1) (close_v_wrt_t_rec n1 a1 v2)
    | e_if0 v1 e2 e3 => e_if0 (close_v_wrt_t_rec n1 a1 v1) (close_e_wrt_t_rec n1 a1 e2) (close_e_wrt_t_rec n1 a1 e3)
    | e_halt t1 v1 => e_halt (close_t_wrt_t_rec n1 a1 t1) (close_v_wrt_t_rec n1 a1 v1)
  end

with close_u_wrt_t_rec (n1 : nat) (a1 : a) (u1 : u) {struct u1} : u :=
  match u1 with
    | u_var_f x1 => u_var_f x1
    | u_var_b n2 => u_var_b n2
    | u_int i1 => u_int i1
    | u_lam t1 v1 => u_lam (close_t_wrt_t_rec n1 a1 t1) (close_v_wrt_t_rec n1 a1 v1)
    | u_Lam t1 e1 => u_Lam (close_t_wrt_t_rec n1 a1 t1) (close_e_wrt_t_rec n1 a1 e1)
    | u_app v1 v2 => u_app (close_v_wrt_t_rec n1 a1 v1) (close_v_wrt_t_rec n1 a1 v2)
    | u_pair v1 v2 => u_pair (close_v_wrt_t_rec n1 a1 v1) (close_v_wrt_t_rec n1 a1 v2)
    | u_prl v1 => u_prl (close_v_wrt_t_rec n1 a1 v1)
    | u_prr v1 => u_prr (close_v_wrt_t_rec n1 a1 v1)
    | u_prim v1 p1 v2 => u_prim (close_v_wrt_t_rec n1 a1 v1) p1 (close_v_wrt_t_rec n1 a1 v2)
    | u_if0 v1 v2 v3 => u_if0 (close_v_wrt_t_rec n1 a1 v1) (close_v_wrt_t_rec n1 a1 v2) (close_v_wrt_t_rec n1 a1 v3)
  end

with close_v_wrt_t_rec (n1 : nat) (a1 : a) (v1 : v) {struct v1} : v :=
  match v1 with
    | v_ann u1 t1 => v_ann (close_u_wrt_t_rec n1 a1 u1) (close_t_wrt_t_rec n1 a1 t1)
  end.

Fixpoint close_d_wrt_u_rec (n1 : nat) (x1 : x) (d1 : d) {struct d1} : d :=
  match d1 with
    | d_val v1 => d_val (close_v_wrt_u_rec n1 x1 v1)
    | d_prl v1 => d_prl (close_v_wrt_u_rec n1 x1 v1)
    | d_prr v1 => d_prr (close_v_wrt_u_rec n1 x1 v1)
    | d_prim v1 p1 v2 => d_prim (close_v_wrt_u_rec n1 x1 v1) p1 (close_v_wrt_u_rec n1 x1 v2)
  end

with close_e_wrt_u_rec (n1 : nat) (x1 : x) (e1 : e) {struct e1} : e :=
  match e1 with
    | e_let d1 e2 => e_let (close_d_wrt_u_rec n1 x1 d1) (close_e_wrt_u_rec (S n1) x1 e2)
    | e_app v1 v2 => e_app (close_v_wrt_u_rec n1 x1 v1) (close_v_wrt_u_rec n1 x1 v2)
    | e_if0 v1 e2 e3 => e_if0 (close_v_wrt_u_rec n1 x1 v1) (close_e_wrt_u_rec n1 x1 e2) (close_e_wrt_u_rec n1 x1 e3)
    | e_halt t1 v1 => e_halt t1 (close_v_wrt_u_rec n1 x1 v1)
  end

with close_u_wrt_u_rec (n1 : nat) (x1 : x) (u1 : u) {struct u1} : u :=
  match u1 with
    | u_var_f x2 => if (x1 == x2) then (u_var_b n1) else (u_var_f x2)
    | u_var_b n2 => if (lt_ge_dec n2 n1) then (u_var_b n2) else (u_var_b (S n2))
    | u_int i1 => u_int i1
    | u_lam t1 v1 => u_lam t1 (close_v_wrt_u_rec (S n1) x1 v1)
    | u_Lam t1 e1 => u_Lam t1 (close_e_wrt_u_rec (S n1) x1 e1)
    | u_app v1 v2 => u_app (close_v_wrt_u_rec n1 x1 v1) (close_v_wrt_u_rec n1 x1 v2)
    | u_pair v1 v2 => u_pair (close_v_wrt_u_rec n1 x1 v1) (close_v_wrt_u_rec n1 x1 v2)
    | u_prl v1 => u_prl (close_v_wrt_u_rec n1 x1 v1)
    | u_prr v1 => u_prr (close_v_wrt_u_rec n1 x1 v1)
    | u_prim v1 p1 v2 => u_prim (close_v_wrt_u_rec n1 x1 v1) p1 (close_v_wrt_u_rec n1 x1 v2)
    | u_if0 v1 v2 v3 => u_if0 (close_v_wrt_u_rec n1 x1 v1) (close_v_wrt_u_rec n1 x1 v2) (close_v_wrt_u_rec n1 x1 v3)
  end

with close_v_wrt_u_rec (n1 : nat) (x1 : x) (v1 : v) {struct v1} : v :=
  match v1 with
    | v_ann u1 t1 => v_ann (close_u_wrt_u_rec n1 x1 u1) t1
  end.

Definition close_d_wrt_t a1 d1 := close_d_wrt_t_rec 0 a1 d1.

Definition close_e_wrt_t a1 e1 := close_e_wrt_t_rec 0 a1 e1.

Definition close_u_wrt_t a1 u1 := close_u_wrt_t_rec 0 a1 u1.

Definition close_v_wrt_t a1 v1 := close_v_wrt_t_rec 0 a1 v1.

Definition close_d_wrt_u x1 d1 := close_d_wrt_u_rec 0 x1 d1.

Definition close_e_wrt_u x1 e1 := close_e_wrt_u_rec 0 x1 e1.

Definition close_u_wrt_u x1 u1 := close_u_wrt_u_rec 0 x1 u1.

Definition close_v_wrt_u x1 v1 := close_v_wrt_u_rec 0 x1 v1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_t (t1 : t) {struct t1} : nat :=
  match t1 with
    | t_var_f a1 => 1
    | t_var_b n1 => 1
    | t_int => 1
    | t_void => 1
    | t_arr t2 t3 => 1 + (size_t t2) + (size_t t3)
    | t_all t2 => 1 + (size_t t2)
    | t_prod t2 t3 => 1 + (size_t t2) + (size_t t3)
  end.

Fixpoint size_p (p1 : p) {struct p1} : nat :=
  match p1 with
    | p_plus => 1
    | p_minus => 1
  end.

Fixpoint size_d (d1 : d) {struct d1} : nat :=
  match d1 with
    | d_val v1 => 1 + (size_v v1)
    | d_prl v1 => 1 + (size_v v1)
    | d_prr v1 => 1 + (size_v v1)
    | d_prim v1 p1 v2 => 1 + (size_v v1) + (size_p p1) + (size_v v2)
  end

with size_e (e1 : e) {struct e1} : nat :=
  match e1 with
    | e_let d1 e2 => 1 + (size_d d1) + (size_e e2)
    | e_app v1 v2 => 1 + (size_v v1) + (size_v v2)
    | e_if0 v1 e2 e3 => 1 + (size_v v1) + (size_e e2) + (size_e e3)
    | e_halt t1 v1 => 1 + (size_t t1) + (size_v v1)
  end

with size_u (u1 : u) {struct u1} : nat :=
  match u1 with
    | u_var_f x1 => 1
    | u_var_b n1 => 1
    | u_int i1 => 1
    | u_lam t1 v1 => 1 + (size_t t1) + (size_v v1)
    | u_Lam t1 e1 => 1 + (size_t t1) + (size_e e1)
    | u_app v1 v2 => 1 + (size_v v1) + (size_v v2)
    | u_pair v1 v2 => 1 + (size_v v1) + (size_v v2)
    | u_prl v1 => 1 + (size_v v1)
    | u_prr v1 => 1 + (size_v v1)
    | u_prim v1 p1 v2 => 1 + (size_v v1) + (size_p p1) + (size_v v2)
    | u_if0 v1 v2 v3 => 1 + (size_v v1) + (size_v v2) + (size_v v3)
  end

with size_v (v1 : v) {struct v1} : nat :=
  match v1 with
    | v_ann u1 t1 => 1 + (size_u u1) + (size_t t1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_t_wrt_t : nat -> t -> Prop :=
  | degree_wrt_t_t_var_f : forall n1 a1,
    degree_t_wrt_t n1 (t_var_f a1)
  | degree_wrt_t_t_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_t_wrt_t n1 (t_var_b n2)
  | degree_wrt_t_t_int : forall n1,
    degree_t_wrt_t n1 (t_int)
  | degree_wrt_t_t_void : forall n1,
    degree_t_wrt_t n1 (t_void)
  | degree_wrt_t_t_arr : forall n1 t1 t2,
    degree_t_wrt_t n1 t1 ->
    degree_t_wrt_t n1 t2 ->
    degree_t_wrt_t n1 (t_arr t1 t2)
  | degree_wrt_t_t_all : forall n1 t1,
    degree_t_wrt_t (S n1) t1 ->
    degree_t_wrt_t n1 (t_all t1)
  | degree_wrt_t_t_prod : forall n1 t1 t2,
    degree_t_wrt_t n1 t1 ->
    degree_t_wrt_t n1 t2 ->
    degree_t_wrt_t n1 (t_prod t1 t2).

Scheme degree_t_wrt_t_ind' := Induction for degree_t_wrt_t Sort Prop.

Definition degree_t_wrt_t_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  degree_t_wrt_t_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Hint Constructors degree_t_wrt_t : core lngen.

Inductive degree_d_wrt_t : nat -> d -> Prop :=
  | degree_wrt_t_d_val : forall n1 v1,
    degree_v_wrt_t n1 v1 ->
    degree_d_wrt_t n1 (d_val v1)
  | degree_wrt_t_d_prl : forall n1 v1,
    degree_v_wrt_t n1 v1 ->
    degree_d_wrt_t n1 (d_prl v1)
  | degree_wrt_t_d_prr : forall n1 v1,
    degree_v_wrt_t n1 v1 ->
    degree_d_wrt_t n1 (d_prr v1)
  | degree_wrt_t_d_prim : forall n1 v1 p1 v2,
    degree_v_wrt_t n1 v1 ->
    degree_v_wrt_t n1 v2 ->
    degree_d_wrt_t n1 (d_prim v1 p1 v2)

with degree_e_wrt_t : nat -> e -> Prop :=
  | degree_wrt_t_e_let : forall n1 d1 e1,
    degree_d_wrt_t n1 d1 ->
    degree_e_wrt_t n1 e1 ->
    degree_e_wrt_t n1 (e_let d1 e1)
  | degree_wrt_t_e_app : forall n1 v1 v2,
    degree_v_wrt_t n1 v1 ->
    degree_v_wrt_t n1 v2 ->
    degree_e_wrt_t n1 (e_app v1 v2)
  | degree_wrt_t_e_if0 : forall n1 v1 e1 e2,
    degree_v_wrt_t n1 v1 ->
    degree_e_wrt_t n1 e1 ->
    degree_e_wrt_t n1 e2 ->
    degree_e_wrt_t n1 (e_if0 v1 e1 e2)
  | degree_wrt_t_e_halt : forall n1 t1 v1,
    degree_t_wrt_t n1 t1 ->
    degree_v_wrt_t n1 v1 ->
    degree_e_wrt_t n1 (e_halt t1 v1)

with degree_u_wrt_t : nat -> u -> Prop :=
  | degree_wrt_t_u_var_f : forall n1 x1,
    degree_u_wrt_t n1 (u_var_f x1)
  | degree_wrt_t_u_var_b : forall n1 n2,
    degree_u_wrt_t n1 (u_var_b n2)
  | degree_wrt_t_u_int : forall n1 i1,
    degree_u_wrt_t n1 (u_int i1)
  | degree_wrt_t_u_lam : forall n1 t1 v1,
    degree_t_wrt_t n1 t1 ->
    degree_v_wrt_t n1 v1 ->
    degree_u_wrt_t n1 (u_lam t1 v1)
  | degree_wrt_t_u_Lam : forall n1 t1 e1,
    degree_t_wrt_t n1 t1 ->
    degree_e_wrt_t n1 e1 ->
    degree_u_wrt_t n1 (u_Lam t1 e1)
  | degree_wrt_t_u_app : forall n1 v1 v2,
    degree_v_wrt_t n1 v1 ->
    degree_v_wrt_t n1 v2 ->
    degree_u_wrt_t n1 (u_app v1 v2)
  | degree_wrt_t_u_pair : forall n1 v1 v2,
    degree_v_wrt_t n1 v1 ->
    degree_v_wrt_t n1 v2 ->
    degree_u_wrt_t n1 (u_pair v1 v2)
  | degree_wrt_t_u_prl : forall n1 v1,
    degree_v_wrt_t n1 v1 ->
    degree_u_wrt_t n1 (u_prl v1)
  | degree_wrt_t_u_prr : forall n1 v1,
    degree_v_wrt_t n1 v1 ->
    degree_u_wrt_t n1 (u_prr v1)
  | degree_wrt_t_u_prim : forall n1 v1 p1 v2,
    degree_v_wrt_t n1 v1 ->
    degree_v_wrt_t n1 v2 ->
    degree_u_wrt_t n1 (u_prim v1 p1 v2)
  | degree_wrt_t_u_if0 : forall n1 v1 v2 v3,
    degree_v_wrt_t n1 v1 ->
    degree_v_wrt_t n1 v2 ->
    degree_v_wrt_t n1 v3 ->
    degree_u_wrt_t n1 (u_if0 v1 v2 v3)

with degree_v_wrt_t : nat -> v -> Prop :=
  | degree_wrt_t_v_ann : forall n1 u1 t1,
    degree_u_wrt_t n1 u1 ->
    degree_t_wrt_t n1 t1 ->
    degree_v_wrt_t n1 (v_ann u1 t1).

Inductive degree_d_wrt_u : nat -> d -> Prop :=
  | degree_wrt_u_d_val : forall n1 v1,
    degree_v_wrt_u n1 v1 ->
    degree_d_wrt_u n1 (d_val v1)
  | degree_wrt_u_d_prl : forall n1 v1,
    degree_v_wrt_u n1 v1 ->
    degree_d_wrt_u n1 (d_prl v1)
  | degree_wrt_u_d_prr : forall n1 v1,
    degree_v_wrt_u n1 v1 ->
    degree_d_wrt_u n1 (d_prr v1)
  | degree_wrt_u_d_prim : forall n1 v1 p1 v2,
    degree_v_wrt_u n1 v1 ->
    degree_v_wrt_u n1 v2 ->
    degree_d_wrt_u n1 (d_prim v1 p1 v2)

with degree_e_wrt_u : nat -> e -> Prop :=
  | degree_wrt_u_e_let : forall n1 d1 e1,
    degree_d_wrt_u n1 d1 ->
    degree_e_wrt_u (S n1) e1 ->
    degree_e_wrt_u n1 (e_let d1 e1)
  | degree_wrt_u_e_app : forall n1 v1 v2,
    degree_v_wrt_u n1 v1 ->
    degree_v_wrt_u n1 v2 ->
    degree_e_wrt_u n1 (e_app v1 v2)
  | degree_wrt_u_e_if0 : forall n1 v1 e1 e2,
    degree_v_wrt_u n1 v1 ->
    degree_e_wrt_u n1 e1 ->
    degree_e_wrt_u n1 e2 ->
    degree_e_wrt_u n1 (e_if0 v1 e1 e2)
  | degree_wrt_u_e_halt : forall n1 t1 v1,
    degree_v_wrt_u n1 v1 ->
    degree_e_wrt_u n1 (e_halt t1 v1)

with degree_u_wrt_u : nat -> u -> Prop :=
  | degree_wrt_u_u_var_f : forall n1 x1,
    degree_u_wrt_u n1 (u_var_f x1)
  | degree_wrt_u_u_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_u_wrt_u n1 (u_var_b n2)
  | degree_wrt_u_u_int : forall n1 i1,
    degree_u_wrt_u n1 (u_int i1)
  | degree_wrt_u_u_lam : forall n1 t1 v1,
    degree_v_wrt_u (S n1) v1 ->
    degree_u_wrt_u n1 (u_lam t1 v1)
  | degree_wrt_u_u_Lam : forall n1 t1 e1,
    degree_e_wrt_u (S n1) e1 ->
    degree_u_wrt_u n1 (u_Lam t1 e1)
  | degree_wrt_u_u_app : forall n1 v1 v2,
    degree_v_wrt_u n1 v1 ->
    degree_v_wrt_u n1 v2 ->
    degree_u_wrt_u n1 (u_app v1 v2)
  | degree_wrt_u_u_pair : forall n1 v1 v2,
    degree_v_wrt_u n1 v1 ->
    degree_v_wrt_u n1 v2 ->
    degree_u_wrt_u n1 (u_pair v1 v2)
  | degree_wrt_u_u_prl : forall n1 v1,
    degree_v_wrt_u n1 v1 ->
    degree_u_wrt_u n1 (u_prl v1)
  | degree_wrt_u_u_prr : forall n1 v1,
    degree_v_wrt_u n1 v1 ->
    degree_u_wrt_u n1 (u_prr v1)
  | degree_wrt_u_u_prim : forall n1 v1 p1 v2,
    degree_v_wrt_u n1 v1 ->
    degree_v_wrt_u n1 v2 ->
    degree_u_wrt_u n1 (u_prim v1 p1 v2)
  | degree_wrt_u_u_if0 : forall n1 v1 v2 v3,
    degree_v_wrt_u n1 v1 ->
    degree_v_wrt_u n1 v2 ->
    degree_v_wrt_u n1 v3 ->
    degree_u_wrt_u n1 (u_if0 v1 v2 v3)

with degree_v_wrt_u : nat -> v -> Prop :=
  | degree_wrt_u_v_ann : forall n1 u1 t1,
    degree_u_wrt_u n1 u1 ->
    degree_v_wrt_u n1 (v_ann u1 t1).

Scheme degree_d_wrt_t_ind' := Induction for degree_d_wrt_t Sort Prop
  with degree_e_wrt_t_ind' := Induction for degree_e_wrt_t Sort Prop
  with degree_u_wrt_t_ind' := Induction for degree_u_wrt_t Sort Prop
  with degree_v_wrt_t_ind' := Induction for degree_v_wrt_t Sort Prop.

Definition degree_d_wrt_t_degree_e_wrt_t_degree_u_wrt_t_degree_v_wrt_t_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 =>
  (conj (degree_d_wrt_t_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)
  ((conj (degree_e_wrt_t_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)
  ((conj (degree_u_wrt_t_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)
  (degree_v_wrt_t_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)))))).

Scheme degree_d_wrt_u_ind' := Induction for degree_d_wrt_u Sort Prop
  with degree_e_wrt_u_ind' := Induction for degree_e_wrt_u Sort Prop
  with degree_u_wrt_u_ind' := Induction for degree_u_wrt_u Sort Prop
  with degree_v_wrt_u_ind' := Induction for degree_v_wrt_u Sort Prop.

Definition degree_d_wrt_u_degree_e_wrt_u_degree_u_wrt_u_degree_v_wrt_u_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 =>
  (conj (degree_d_wrt_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)
  ((conj (degree_e_wrt_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)
  ((conj (degree_u_wrt_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)
  (degree_v_wrt_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)))))).

Hint Constructors degree_d_wrt_t : core lngen.

Hint Constructors degree_e_wrt_t : core lngen.

Hint Constructors degree_u_wrt_t : core lngen.

Hint Constructors degree_v_wrt_t : core lngen.

Hint Constructors degree_d_wrt_u : core lngen.

Hint Constructors degree_e_wrt_u : core lngen.

Hint Constructors degree_u_wrt_u : core lngen.

Hint Constructors degree_v_wrt_u : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_t : t -> Set :=
  | lc_set_t_var_f : forall a1,
    lc_set_t (t_var_f a1)
  | lc_set_t_int :
    lc_set_t (t_int)
  | lc_set_t_void :
    lc_set_t (t_void)
  | lc_set_t_arr : forall t1 t2,
    lc_set_t t1 ->
    lc_set_t t2 ->
    lc_set_t (t_arr t1 t2)
  | lc_set_t_all : forall t1,
    (forall a1 : a, lc_set_t (open_t_wrt_t t1 (t_var_f a1))) ->
    lc_set_t (t_all t1)
  | lc_set_t_prod : forall t1 t2,
    lc_set_t t1 ->
    lc_set_t t2 ->
    lc_set_t (t_prod t1 t2).

Scheme lc_t_ind' := Induction for lc_t Sort Prop.

Definition lc_t_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  lc_t_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme lc_set_t_ind' := Induction for lc_set_t Sort Prop.

Definition lc_set_t_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  lc_set_t_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme lc_set_t_rec' := Induction for lc_set_t Sort Set.

Definition lc_set_t_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  lc_set_t_rec' H1 H2 H3 H4 H5 H6 H7.

Hint Constructors lc_t : core lngen.

Hint Constructors lc_set_t : core lngen.

Inductive lc_set_d : d -> Set :=
  | lc_set_d_val : forall v1,
    lc_set_v v1 ->
    lc_set_d (d_val v1)
  | lc_set_d_prl : forall v1,
    lc_set_v v1 ->
    lc_set_d (d_prl v1)
  | lc_set_d_prr : forall v1,
    lc_set_v v1 ->
    lc_set_d (d_prr v1)
  | lc_set_d_prim : forall v1 p1 v2,
    lc_set_v v1 ->
    lc_set_v v2 ->
    lc_set_d (d_prim v1 p1 v2)

with lc_set_e : e -> Set :=
  | lc_set_e_let : forall d1 e1,
    lc_set_d d1 ->
    (forall x1 : x, lc_set_e (open_e_wrt_u e1 (u_var_f x1))) ->
    lc_set_e (e_let d1 e1)
  | lc_set_e_app : forall v1 v2,
    lc_set_v v1 ->
    lc_set_v v2 ->
    lc_set_e (e_app v1 v2)
  | lc_set_e_if0 : forall v1 e1 e2,
    lc_set_v v1 ->
    lc_set_e e1 ->
    lc_set_e e2 ->
    lc_set_e (e_if0 v1 e1 e2)
  | lc_set_e_halt : forall t1 v1,
    lc_set_t t1 ->
    lc_set_v v1 ->
    lc_set_e (e_halt t1 v1)

with lc_set_u : u -> Set :=
  | lc_set_u_var_f : forall x1,
    lc_set_u (u_var_f x1)
  | lc_set_u_int : forall i1,
    lc_set_u (u_int i1)
  | lc_set_u_lam : forall t1 v1,
    lc_set_t t1 ->
    (forall x1 : x, lc_set_v (open_v_wrt_u v1 (u_var_f x1))) ->
    lc_set_u (u_lam t1 v1)
  | lc_set_u_Lam : forall t1 e1,
    lc_set_t t1 ->
    (forall x1 : x, lc_set_e (open_e_wrt_u e1 (u_var_f x1))) ->
    lc_set_u (u_Lam t1 e1)
  | lc_set_u_app : forall v1 v2,
    lc_set_v v1 ->
    lc_set_v v2 ->
    lc_set_u (u_app v1 v2)
  | lc_set_u_pair : forall v1 v2,
    lc_set_v v1 ->
    lc_set_v v2 ->
    lc_set_u (u_pair v1 v2)
  | lc_set_u_prl : forall v1,
    lc_set_v v1 ->
    lc_set_u (u_prl v1)
  | lc_set_u_prr : forall v1,
    lc_set_v v1 ->
    lc_set_u (u_prr v1)
  | lc_set_u_prim : forall v1 p1 v2,
    lc_set_v v1 ->
    lc_set_v v2 ->
    lc_set_u (u_prim v1 p1 v2)
  | lc_set_u_if0 : forall v1 v2 v3,
    lc_set_v v1 ->
    lc_set_v v2 ->
    lc_set_v v3 ->
    lc_set_u (u_if0 v1 v2 v3)

with lc_set_v : v -> Set :=
  | lc_set_v_ann : forall u1 t1,
    lc_set_u u1 ->
    lc_set_t t1 ->
    lc_set_v (v_ann u1 t1).

Scheme lc_d_ind' := Induction for lc_d Sort Prop
  with lc_e_ind' := Induction for lc_e Sort Prop
  with lc_u_ind' := Induction for lc_u Sort Prop
  with lc_v_ind' := Induction for lc_v Sort Prop.

Definition lc_d_lc_e_lc_u_lc_v_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 =>
  (conj (lc_d_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)
  ((conj (lc_e_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)
  ((conj (lc_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)
  (lc_v_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)))))).

Scheme lc_set_d_ind' := Induction for lc_set_d Sort Prop
  with lc_set_e_ind' := Induction for lc_set_e Sort Prop
  with lc_set_u_ind' := Induction for lc_set_u Sort Prop
  with lc_set_v_ind' := Induction for lc_set_v Sort Prop.

Definition lc_set_d_lc_set_e_lc_set_u_lc_set_v_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 =>
  (conj (lc_set_d_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)
  ((conj (lc_set_e_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)
  ((conj (lc_set_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)
  (lc_set_v_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)))))).

Scheme lc_set_d_rec' := Induction for lc_set_d Sort Set
  with lc_set_e_rec' := Induction for lc_set_e Sort Set
  with lc_set_u_rec' := Induction for lc_set_u Sort Set
  with lc_set_v_rec' := Induction for lc_set_v Sort Set.

Definition lc_set_d_lc_set_e_lc_set_u_lc_set_v_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 =>
  (pair ((pair ((pair (lc_set_d_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)
  (lc_set_e_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)))
  (lc_set_u_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)))
  (lc_set_v_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23)).

Hint Constructors lc_d : core lngen.

Hint Constructors lc_e : core lngen.

Hint Constructors lc_u : core lngen.

Hint Constructors lc_v : core lngen.

Hint Constructors lc_set_d : core lngen.

Hint Constructors lc_set_e : core lngen.

Hint Constructors lc_set_u : core lngen.

Hint Constructors lc_set_v : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_t_wrt_t t1 := forall a1, lc_t (open_t_wrt_t t1 (t_var_f a1)).

Hint Unfold body_t_wrt_t.

Definition body_d_wrt_t d1 := forall a1, lc_d (open_d_wrt_t d1 (t_var_f a1)).

Definition body_e_wrt_t e1 := forall a1, lc_e (open_e_wrt_t e1 (t_var_f a1)).

Definition body_u_wrt_t u1 := forall a1, lc_u (open_u_wrt_t u1 (t_var_f a1)).

Definition body_v_wrt_t v1 := forall a1, lc_v (open_v_wrt_t v1 (t_var_f a1)).

Definition body_d_wrt_u d1 := forall x1, lc_d (open_d_wrt_u d1 (u_var_f x1)).

Definition body_e_wrt_u e1 := forall x1, lc_e (open_e_wrt_u e1 (u_var_f x1)).

Definition body_u_wrt_u u1 := forall x1, lc_u (open_u_wrt_u u1 (u_var_f x1)).

Definition body_v_wrt_u v1 := forall x1, lc_v (open_v_wrt_u v1 (u_var_f x1)).

Hint Unfold body_d_wrt_t.

Hint Unfold body_e_wrt_t.

Hint Unfold body_u_wrt_t.

Hint Unfold body_v_wrt_t.

Hint Unfold body_d_wrt_u.

Hint Unfold body_e_wrt_u.

Hint Unfold body_u_wrt_u.

Hint Unfold body_v_wrt_u.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_t_min_mutual :
(forall t1, 1 <= size_t t1).
Proof. Admitted.

(* end hide *)

Lemma size_t_min :
forall t1, 1 <= size_t t1.
Proof. Admitted.

Hint Resolve size_t_min : lngen.

(* begin hide *)

Lemma size_p_min_mutual :
(forall p1, 1 <= size_p p1).
Proof. Admitted.

(* end hide *)

Lemma size_p_min :
forall p1, 1 <= size_p p1.
Proof. Admitted.

Hint Resolve size_p_min : lngen.

(* begin hide *)

Lemma size_d_min_size_e_min_size_u_min_size_v_min_mutual :
(forall d1, 1 <= size_d d1) /\
(forall e1, 1 <= size_e e1) /\
(forall u1, 1 <= size_u u1) /\
(forall v1, 1 <= size_v v1).
Proof. Admitted.

(* end hide *)

Lemma size_d_min :
forall d1, 1 <= size_d d1.
Proof. Admitted.

Hint Resolve size_d_min : lngen.

Lemma size_e_min :
forall e1, 1 <= size_e e1.
Proof. Admitted.

Hint Resolve size_e_min : lngen.

Lemma size_u_min :
forall u1, 1 <= size_u u1.
Proof. Admitted.

Hint Resolve size_u_min : lngen.

Lemma size_v_min :
forall v1, 1 <= size_v v1.
Proof. Admitted.

Hint Resolve size_v_min : lngen.

(* begin hide *)

Lemma size_t_close_t_wrt_t_rec_mutual :
(forall t1 a1 n1,
  size_t (close_t_wrt_t_rec n1 a1 t1) = size_t t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_t_close_t_wrt_t_rec :
forall t1 a1 n1,
  size_t (close_t_wrt_t_rec n1 a1 t1) = size_t t1.
Proof. Admitted.

Hint Resolve size_t_close_t_wrt_t_rec : lngen.
Hint Rewrite size_t_close_t_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_d_close_d_wrt_t_rec_size_e_close_e_wrt_t_rec_size_u_close_u_wrt_t_rec_size_v_close_v_wrt_t_rec_mutual :
(forall d1 a1 n1,
  size_d (close_d_wrt_t_rec n1 a1 d1) = size_d d1) /\
(forall e1 a1 n1,
  size_e (close_e_wrt_t_rec n1 a1 e1) = size_e e1) /\
(forall u1 a1 n1,
  size_u (close_u_wrt_t_rec n1 a1 u1) = size_u u1) /\
(forall v1 a1 n1,
  size_v (close_v_wrt_t_rec n1 a1 v1) = size_v v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_d_close_d_wrt_t_rec :
forall d1 a1 n1,
  size_d (close_d_wrt_t_rec n1 a1 d1) = size_d d1.
Proof. Admitted.

Hint Resolve size_d_close_d_wrt_t_rec : lngen.
Hint Rewrite size_d_close_d_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_e_close_e_wrt_t_rec :
forall e1 a1 n1,
  size_e (close_e_wrt_t_rec n1 a1 e1) = size_e e1.
Proof. Admitted.

Hint Resolve size_e_close_e_wrt_t_rec : lngen.
Hint Rewrite size_e_close_e_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_u_close_u_wrt_t_rec :
forall u1 a1 n1,
  size_u (close_u_wrt_t_rec n1 a1 u1) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_close_u_wrt_t_rec : lngen.
Hint Rewrite size_u_close_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_v_close_v_wrt_t_rec :
forall v1 a1 n1,
  size_v (close_v_wrt_t_rec n1 a1 v1) = size_v v1.
Proof. Admitted.

Hint Resolve size_v_close_v_wrt_t_rec : lngen.
Hint Rewrite size_v_close_v_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_d_close_d_wrt_u_rec_size_e_close_e_wrt_u_rec_size_u_close_u_wrt_u_rec_size_v_close_v_wrt_u_rec_mutual :
(forall d1 x1 n1,
  size_d (close_d_wrt_u_rec n1 x1 d1) = size_d d1) /\
(forall e1 x1 n1,
  size_e (close_e_wrt_u_rec n1 x1 e1) = size_e e1) /\
(forall u1 x1 n1,
  size_u (close_u_wrt_u_rec n1 x1 u1) = size_u u1) /\
(forall v1 x1 n1,
  size_v (close_v_wrt_u_rec n1 x1 v1) = size_v v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_d_close_d_wrt_u_rec :
forall d1 x1 n1,
  size_d (close_d_wrt_u_rec n1 x1 d1) = size_d d1.
Proof. Admitted.

Hint Resolve size_d_close_d_wrt_u_rec : lngen.
Hint Rewrite size_d_close_d_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_e_close_e_wrt_u_rec :
forall e1 x1 n1,
  size_e (close_e_wrt_u_rec n1 x1 e1) = size_e e1.
Proof. Admitted.

Hint Resolve size_e_close_e_wrt_u_rec : lngen.
Hint Rewrite size_e_close_e_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_u_close_u_wrt_u_rec :
forall u1 x1 n1,
  size_u (close_u_wrt_u_rec n1 x1 u1) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_close_u_wrt_u_rec : lngen.
Hint Rewrite size_u_close_u_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_v_close_v_wrt_u_rec :
forall v1 x1 n1,
  size_v (close_v_wrt_u_rec n1 x1 v1) = size_v v1.
Proof. Admitted.

Hint Resolve size_v_close_v_wrt_u_rec : lngen.
Hint Rewrite size_v_close_v_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_t_close_t_wrt_t :
forall t1 a1,
  size_t (close_t_wrt_t a1 t1) = size_t t1.
Proof. Admitted.

Hint Resolve size_t_close_t_wrt_t : lngen.
Hint Rewrite size_t_close_t_wrt_t using solve [auto] : lngen.

Lemma size_d_close_d_wrt_t :
forall d1 a1,
  size_d (close_d_wrt_t a1 d1) = size_d d1.
Proof. Admitted.

Hint Resolve size_d_close_d_wrt_t : lngen.
Hint Rewrite size_d_close_d_wrt_t using solve [auto] : lngen.

Lemma size_e_close_e_wrt_t :
forall e1 a1,
  size_e (close_e_wrt_t a1 e1) = size_e e1.
Proof. Admitted.

Hint Resolve size_e_close_e_wrt_t : lngen.
Hint Rewrite size_e_close_e_wrt_t using solve [auto] : lngen.

Lemma size_u_close_u_wrt_t :
forall u1 a1,
  size_u (close_u_wrt_t a1 u1) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_close_u_wrt_t : lngen.
Hint Rewrite size_u_close_u_wrt_t using solve [auto] : lngen.

Lemma size_v_close_v_wrt_t :
forall v1 a1,
  size_v (close_v_wrt_t a1 v1) = size_v v1.
Proof. Admitted.

Hint Resolve size_v_close_v_wrt_t : lngen.
Hint Rewrite size_v_close_v_wrt_t using solve [auto] : lngen.

Lemma size_d_close_d_wrt_u :
forall d1 x1,
  size_d (close_d_wrt_u x1 d1) = size_d d1.
Proof. Admitted.

Hint Resolve size_d_close_d_wrt_u : lngen.
Hint Rewrite size_d_close_d_wrt_u using solve [auto] : lngen.

Lemma size_e_close_e_wrt_u :
forall e1 x1,
  size_e (close_e_wrt_u x1 e1) = size_e e1.
Proof. Admitted.

Hint Resolve size_e_close_e_wrt_u : lngen.
Hint Rewrite size_e_close_e_wrt_u using solve [auto] : lngen.

Lemma size_u_close_u_wrt_u :
forall u1 x1,
  size_u (close_u_wrt_u x1 u1) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_close_u_wrt_u : lngen.
Hint Rewrite size_u_close_u_wrt_u using solve [auto] : lngen.

Lemma size_v_close_v_wrt_u :
forall v1 x1,
  size_v (close_v_wrt_u x1 v1) = size_v v1.
Proof. Admitted.

Hint Resolve size_v_close_v_wrt_u : lngen.
Hint Rewrite size_v_close_v_wrt_u using solve [auto] : lngen.

(* begin hide *)

Lemma size_t_open_t_wrt_t_rec_mutual :
(forall t1 t2 n1,
  size_t t1 <= size_t (open_t_wrt_t_rec n1 t2 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_t_open_t_wrt_t_rec :
forall t1 t2 n1,
  size_t t1 <= size_t (open_t_wrt_t_rec n1 t2 t1).
Proof. Admitted.

Hint Resolve size_t_open_t_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_d_open_d_wrt_t_rec_size_e_open_e_wrt_t_rec_size_u_open_u_wrt_t_rec_size_v_open_v_wrt_t_rec_mutual :
(forall d1 t1 n1,
  size_d d1 <= size_d (open_d_wrt_t_rec n1 t1 d1)) /\
(forall e1 t1 n1,
  size_e e1 <= size_e (open_e_wrt_t_rec n1 t1 e1)) /\
(forall u1 t1 n1,
  size_u u1 <= size_u (open_u_wrt_t_rec n1 t1 u1)) /\
(forall v1 t1 n1,
  size_v v1 <= size_v (open_v_wrt_t_rec n1 t1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_d_open_d_wrt_t_rec :
forall d1 t1 n1,
  size_d d1 <= size_d (open_d_wrt_t_rec n1 t1 d1).
Proof. Admitted.

Hint Resolve size_d_open_d_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_e_open_e_wrt_t_rec :
forall e1 t1 n1,
  size_e e1 <= size_e (open_e_wrt_t_rec n1 t1 e1).
Proof. Admitted.

Hint Resolve size_e_open_e_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_t_rec :
forall u1 t1 n1,
  size_u u1 <= size_u (open_u_wrt_t_rec n1 t1 u1).
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_v_open_v_wrt_t_rec :
forall v1 t1 n1,
  size_v v1 <= size_v (open_v_wrt_t_rec n1 t1 v1).
Proof. Admitted.

Hint Resolve size_v_open_v_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_d_open_d_wrt_u_rec_size_e_open_e_wrt_u_rec_size_u_open_u_wrt_u_rec_size_v_open_v_wrt_u_rec_mutual :
(forall d1 u1 n1,
  size_d d1 <= size_d (open_d_wrt_u_rec n1 u1 d1)) /\
(forall e1 u1 n1,
  size_e e1 <= size_e (open_e_wrt_u_rec n1 u1 e1)) /\
(forall u1 u2 n1,
  size_u u1 <= size_u (open_u_wrt_u_rec n1 u2 u1)) /\
(forall v1 u1 n1,
  size_v v1 <= size_v (open_v_wrt_u_rec n1 u1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_d_open_d_wrt_u_rec :
forall d1 u1 n1,
  size_d d1 <= size_d (open_d_wrt_u_rec n1 u1 d1).
Proof. Admitted.

Hint Resolve size_d_open_d_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_e_open_e_wrt_u_rec :
forall e1 u1 n1,
  size_e e1 <= size_e (open_e_wrt_u_rec n1 u1 e1).
Proof. Admitted.

Hint Resolve size_e_open_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_u_rec :
forall u1 u2 n1,
  size_u u1 <= size_u (open_u_wrt_u_rec n1 u2 u1).
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_v_open_v_wrt_u_rec :
forall v1 u1 n1,
  size_v v1 <= size_v (open_v_wrt_u_rec n1 u1 v1).
Proof. Admitted.

Hint Resolve size_v_open_v_wrt_u_rec : lngen.

(* end hide *)

Lemma size_t_open_t_wrt_t :
forall t1 t2,
  size_t t1 <= size_t (open_t_wrt_t t1 t2).
Proof. Admitted.

Hint Resolve size_t_open_t_wrt_t : lngen.

Lemma size_d_open_d_wrt_t :
forall d1 t1,
  size_d d1 <= size_d (open_d_wrt_t d1 t1).
Proof. Admitted.

Hint Resolve size_d_open_d_wrt_t : lngen.

Lemma size_e_open_e_wrt_t :
forall e1 t1,
  size_e e1 <= size_e (open_e_wrt_t e1 t1).
Proof. Admitted.

Hint Resolve size_e_open_e_wrt_t : lngen.

Lemma size_u_open_u_wrt_t :
forall u1 t1,
  size_u u1 <= size_u (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_t : lngen.

Lemma size_v_open_v_wrt_t :
forall v1 t1,
  size_v v1 <= size_v (open_v_wrt_t v1 t1).
Proof. Admitted.

Hint Resolve size_v_open_v_wrt_t : lngen.

Lemma size_d_open_d_wrt_u :
forall d1 u1,
  size_d d1 <= size_d (open_d_wrt_u d1 u1).
Proof. Admitted.

Hint Resolve size_d_open_d_wrt_u : lngen.

Lemma size_e_open_e_wrt_u :
forall e1 u1,
  size_e e1 <= size_e (open_e_wrt_u e1 u1).
Proof. Admitted.

Hint Resolve size_e_open_e_wrt_u : lngen.

Lemma size_u_open_u_wrt_u :
forall u1 u2,
  size_u u1 <= size_u (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_u : lngen.

Lemma size_v_open_v_wrt_u :
forall v1 u1,
  size_v v1 <= size_v (open_v_wrt_u v1 u1).
Proof. Admitted.

Hint Resolve size_v_open_v_wrt_u : lngen.

(* begin hide *)

Lemma size_t_open_t_wrt_t_rec_var_mutual :
(forall t1 a1 n1,
  size_t (open_t_wrt_t_rec n1 (t_var_f a1) t1) = size_t t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_t_open_t_wrt_t_rec_var :
forall t1 a1 n1,
  size_t (open_t_wrt_t_rec n1 (t_var_f a1) t1) = size_t t1.
Proof. Admitted.

Hint Resolve size_t_open_t_wrt_t_rec_var : lngen.
Hint Rewrite size_t_open_t_wrt_t_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_d_open_d_wrt_t_rec_var_size_e_open_e_wrt_t_rec_var_size_u_open_u_wrt_t_rec_var_size_v_open_v_wrt_t_rec_var_mutual :
(forall d1 a1 n1,
  size_d (open_d_wrt_t_rec n1 (t_var_f a1) d1) = size_d d1) /\
(forall e1 a1 n1,
  size_e (open_e_wrt_t_rec n1 (t_var_f a1) e1) = size_e e1) /\
(forall u1 a1 n1,
  size_u (open_u_wrt_t_rec n1 (t_var_f a1) u1) = size_u u1) /\
(forall v1 a1 n1,
  size_v (open_v_wrt_t_rec n1 (t_var_f a1) v1) = size_v v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_d_open_d_wrt_t_rec_var :
forall d1 a1 n1,
  size_d (open_d_wrt_t_rec n1 (t_var_f a1) d1) = size_d d1.
Proof. Admitted.

Hint Resolve size_d_open_d_wrt_t_rec_var : lngen.
Hint Rewrite size_d_open_d_wrt_t_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_e_open_e_wrt_t_rec_var :
forall e1 a1 n1,
  size_e (open_e_wrt_t_rec n1 (t_var_f a1) e1) = size_e e1.
Proof. Admitted.

Hint Resolve size_e_open_e_wrt_t_rec_var : lngen.
Hint Rewrite size_e_open_e_wrt_t_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_t_rec_var :
forall u1 a1 n1,
  size_u (open_u_wrt_t_rec n1 (t_var_f a1) u1) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_t_rec_var : lngen.
Hint Rewrite size_u_open_u_wrt_t_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_v_open_v_wrt_t_rec_var :
forall v1 a1 n1,
  size_v (open_v_wrt_t_rec n1 (t_var_f a1) v1) = size_v v1.
Proof. Admitted.

Hint Resolve size_v_open_v_wrt_t_rec_var : lngen.
Hint Rewrite size_v_open_v_wrt_t_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_d_open_d_wrt_u_rec_var_size_e_open_e_wrt_u_rec_var_size_u_open_u_wrt_u_rec_var_size_v_open_v_wrt_u_rec_var_mutual :
(forall d1 x1 n1,
  size_d (open_d_wrt_u_rec n1 (u_var_f x1) d1) = size_d d1) /\
(forall e1 x1 n1,
  size_e (open_e_wrt_u_rec n1 (u_var_f x1) e1) = size_e e1) /\
(forall u1 x1 n1,
  size_u (open_u_wrt_u_rec n1 (u_var_f x1) u1) = size_u u1) /\
(forall v1 x1 n1,
  size_v (open_v_wrt_u_rec n1 (u_var_f x1) v1) = size_v v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_d_open_d_wrt_u_rec_var :
forall d1 x1 n1,
  size_d (open_d_wrt_u_rec n1 (u_var_f x1) d1) = size_d d1.
Proof. Admitted.

Hint Resolve size_d_open_d_wrt_u_rec_var : lngen.
Hint Rewrite size_d_open_d_wrt_u_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_e_open_e_wrt_u_rec_var :
forall e1 x1 n1,
  size_e (open_e_wrt_u_rec n1 (u_var_f x1) e1) = size_e e1.
Proof. Admitted.

Hint Resolve size_e_open_e_wrt_u_rec_var : lngen.
Hint Rewrite size_e_open_e_wrt_u_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_u_rec_var :
forall u1 x1 n1,
  size_u (open_u_wrt_u_rec n1 (u_var_f x1) u1) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_u_rec_var : lngen.
Hint Rewrite size_u_open_u_wrt_u_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_v_open_v_wrt_u_rec_var :
forall v1 x1 n1,
  size_v (open_v_wrt_u_rec n1 (u_var_f x1) v1) = size_v v1.
Proof. Admitted.

Hint Resolve size_v_open_v_wrt_u_rec_var : lngen.
Hint Rewrite size_v_open_v_wrt_u_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_t_open_t_wrt_t_var :
forall t1 a1,
  size_t (open_t_wrt_t t1 (t_var_f a1)) = size_t t1.
Proof. Admitted.

Hint Resolve size_t_open_t_wrt_t_var : lngen.
Hint Rewrite size_t_open_t_wrt_t_var using solve [auto] : lngen.

Lemma size_d_open_d_wrt_t_var :
forall d1 a1,
  size_d (open_d_wrt_t d1 (t_var_f a1)) = size_d d1.
Proof. Admitted.

Hint Resolve size_d_open_d_wrt_t_var : lngen.
Hint Rewrite size_d_open_d_wrt_t_var using solve [auto] : lngen.

Lemma size_e_open_e_wrt_t_var :
forall e1 a1,
  size_e (open_e_wrt_t e1 (t_var_f a1)) = size_e e1.
Proof. Admitted.

Hint Resolve size_e_open_e_wrt_t_var : lngen.
Hint Rewrite size_e_open_e_wrt_t_var using solve [auto] : lngen.

Lemma size_u_open_u_wrt_t_var :
forall u1 a1,
  size_u (open_u_wrt_t u1 (t_var_f a1)) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_t_var : lngen.
Hint Rewrite size_u_open_u_wrt_t_var using solve [auto] : lngen.

Lemma size_v_open_v_wrt_t_var :
forall v1 a1,
  size_v (open_v_wrt_t v1 (t_var_f a1)) = size_v v1.
Proof. Admitted.

Hint Resolve size_v_open_v_wrt_t_var : lngen.
Hint Rewrite size_v_open_v_wrt_t_var using solve [auto] : lngen.

Lemma size_d_open_d_wrt_u_var :
forall d1 x1,
  size_d (open_d_wrt_u d1 (u_var_f x1)) = size_d d1.
Proof. Admitted.

Hint Resolve size_d_open_d_wrt_u_var : lngen.
Hint Rewrite size_d_open_d_wrt_u_var using solve [auto] : lngen.

Lemma size_e_open_e_wrt_u_var :
forall e1 x1,
  size_e (open_e_wrt_u e1 (u_var_f x1)) = size_e e1.
Proof. Admitted.

Hint Resolve size_e_open_e_wrt_u_var : lngen.
Hint Rewrite size_e_open_e_wrt_u_var using solve [auto] : lngen.

Lemma size_u_open_u_wrt_u_var :
forall u1 x1,
  size_u (open_u_wrt_u u1 (u_var_f x1)) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_u_var : lngen.
Hint Rewrite size_u_open_u_wrt_u_var using solve [auto] : lngen.

Lemma size_v_open_v_wrt_u_var :
forall v1 x1,
  size_v (open_v_wrt_u v1 (u_var_f x1)) = size_v v1.
Proof. Admitted.

Hint Resolve size_v_open_v_wrt_u_var : lngen.
Hint Rewrite size_v_open_v_wrt_u_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_t_wrt_t_S_mutual :
(forall n1 t1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t (S n1) t1).
Proof. Admitted.

(* end hide *)

Lemma degree_t_wrt_t_S :
forall n1 t1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t (S n1) t1.
Proof. Admitted.

Hint Resolve degree_t_wrt_t_S : lngen.

(* begin hide *)

Lemma degree_d_wrt_t_S_degree_e_wrt_t_S_degree_u_wrt_t_S_degree_v_wrt_t_S_mutual :
(forall n1 d1,
  degree_d_wrt_t n1 d1 ->
  degree_d_wrt_t (S n1) d1) /\
(forall n1 e1,
  degree_e_wrt_t n1 e1 ->
  degree_e_wrt_t (S n1) e1) /\
(forall n1 u1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) u1) /\
(forall n1 v1,
  degree_v_wrt_t n1 v1 ->
  degree_v_wrt_t (S n1) v1).
Proof. Admitted.

(* end hide *)

Lemma degree_d_wrt_t_S :
forall n1 d1,
  degree_d_wrt_t n1 d1 ->
  degree_d_wrt_t (S n1) d1.
Proof. Admitted.

Hint Resolve degree_d_wrt_t_S : lngen.

Lemma degree_e_wrt_t_S :
forall n1 e1,
  degree_e_wrt_t n1 e1 ->
  degree_e_wrt_t (S n1) e1.
Proof. Admitted.

Hint Resolve degree_e_wrt_t_S : lngen.

Lemma degree_u_wrt_t_S :
forall n1 u1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_t_S : lngen.

Lemma degree_v_wrt_t_S :
forall n1 v1,
  degree_v_wrt_t n1 v1 ->
  degree_v_wrt_t (S n1) v1.
Proof. Admitted.

Hint Resolve degree_v_wrt_t_S : lngen.

(* begin hide *)

Lemma degree_d_wrt_u_S_degree_e_wrt_u_S_degree_u_wrt_u_S_degree_v_wrt_u_S_mutual :
(forall n1 d1,
  degree_d_wrt_u n1 d1 ->
  degree_d_wrt_u (S n1) d1) /\
(forall n1 e1,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u (S n1) e1) /\
(forall n1 u1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u (S n1) u1) /\
(forall n1 v1,
  degree_v_wrt_u n1 v1 ->
  degree_v_wrt_u (S n1) v1).
Proof. Admitted.

(* end hide *)

Lemma degree_d_wrt_u_S :
forall n1 d1,
  degree_d_wrt_u n1 d1 ->
  degree_d_wrt_u (S n1) d1.
Proof. Admitted.

Hint Resolve degree_d_wrt_u_S : lngen.

Lemma degree_e_wrt_u_S :
forall n1 e1,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u (S n1) e1.
Proof. Admitted.

Hint Resolve degree_e_wrt_u_S : lngen.

Lemma degree_u_wrt_u_S :
forall n1 u1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u (S n1) u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_u_S : lngen.

Lemma degree_v_wrt_u_S :
forall n1 v1,
  degree_v_wrt_u n1 v1 ->
  degree_v_wrt_u (S n1) v1.
Proof. Admitted.

Hint Resolve degree_v_wrt_u_S : lngen.

Lemma degree_t_wrt_t_O :
forall n1 t1,
  degree_t_wrt_t O t1 ->
  degree_t_wrt_t n1 t1.
Proof. Admitted.

Hint Resolve degree_t_wrt_t_O : lngen.

Lemma degree_d_wrt_t_O :
forall n1 d1,
  degree_d_wrt_t O d1 ->
  degree_d_wrt_t n1 d1.
Proof. Admitted.

Hint Resolve degree_d_wrt_t_O : lngen.

Lemma degree_e_wrt_t_O :
forall n1 e1,
  degree_e_wrt_t O e1 ->
  degree_e_wrt_t n1 e1.
Proof. Admitted.

Hint Resolve degree_e_wrt_t_O : lngen.

Lemma degree_u_wrt_t_O :
forall n1 u1,
  degree_u_wrt_t O u1 ->
  degree_u_wrt_t n1 u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_t_O : lngen.

Lemma degree_v_wrt_t_O :
forall n1 v1,
  degree_v_wrt_t O v1 ->
  degree_v_wrt_t n1 v1.
Proof. Admitted.

Hint Resolve degree_v_wrt_t_O : lngen.

Lemma degree_d_wrt_u_O :
forall n1 d1,
  degree_d_wrt_u O d1 ->
  degree_d_wrt_u n1 d1.
Proof. Admitted.

Hint Resolve degree_d_wrt_u_O : lngen.

Lemma degree_e_wrt_u_O :
forall n1 e1,
  degree_e_wrt_u O e1 ->
  degree_e_wrt_u n1 e1.
Proof. Admitted.

Hint Resolve degree_e_wrt_u_O : lngen.

Lemma degree_u_wrt_u_O :
forall n1 u1,
  degree_u_wrt_u O u1 ->
  degree_u_wrt_u n1 u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_u_O : lngen.

Lemma degree_v_wrt_u_O :
forall n1 v1,
  degree_v_wrt_u O v1 ->
  degree_v_wrt_u n1 v1.
Proof. Admitted.

Hint Resolve degree_v_wrt_u_O : lngen.

(* begin hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_rec_mutual :
(forall t1 a1 n1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t (S n1) (close_t_wrt_t_rec n1 a1 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_rec :
forall t1 a1 n1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t (S n1) (close_t_wrt_t_rec n1 a1 t1).
Proof. Admitted.

Hint Resolve degree_t_wrt_t_close_t_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_close_d_wrt_t_rec_degree_e_wrt_t_close_e_wrt_t_rec_degree_u_wrt_t_close_u_wrt_t_rec_degree_v_wrt_t_close_v_wrt_t_rec_mutual :
(forall d1 a1 n1,
  degree_d_wrt_t n1 d1 ->
  degree_d_wrt_t (S n1) (close_d_wrt_t_rec n1 a1 d1)) /\
(forall e1 a1 n1,
  degree_e_wrt_t n1 e1 ->
  degree_e_wrt_t (S n1) (close_e_wrt_t_rec n1 a1 e1)) /\
(forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1)) /\
(forall v1 a1 n1,
  degree_v_wrt_t n1 v1 ->
  degree_v_wrt_t (S n1) (close_v_wrt_t_rec n1 a1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_close_d_wrt_t_rec :
forall d1 a1 n1,
  degree_d_wrt_t n1 d1 ->
  degree_d_wrt_t (S n1) (close_d_wrt_t_rec n1 a1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_t_close_d_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_t_close_e_wrt_t_rec :
forall e1 a1 n1,
  degree_e_wrt_t n1 e1 ->
  degree_e_wrt_t (S n1) (close_e_wrt_t_rec n1 a1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_t_close_e_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_close_u_wrt_t_rec :
forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_close_u_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_t_close_v_wrt_t_rec :
forall v1 a1 n1,
  degree_v_wrt_t n1 v1 ->
  degree_v_wrt_t (S n1) (close_v_wrt_t_rec n1 a1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_t_close_v_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_close_d_wrt_u_rec_degree_e_wrt_t_close_e_wrt_u_rec_degree_u_wrt_t_close_u_wrt_u_rec_degree_v_wrt_t_close_v_wrt_u_rec_mutual :
(forall d1 x1 n1 n2,
  degree_d_wrt_t n2 d1 ->
  degree_d_wrt_t n2 (close_d_wrt_u_rec n1 x1 d1)) /\
(forall e1 x1 n1 n2,
  degree_e_wrt_t n2 e1 ->
  degree_e_wrt_t n2 (close_e_wrt_u_rec n1 x1 e1)) /\
(forall u1 x1 n1 n2,
  degree_u_wrt_t n2 u1 ->
  degree_u_wrt_t n2 (close_u_wrt_u_rec n1 x1 u1)) /\
(forall v1 x1 n1 n2,
  degree_v_wrt_t n2 v1 ->
  degree_v_wrt_t n2 (close_v_wrt_u_rec n1 x1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_close_d_wrt_u_rec :
forall d1 x1 n1 n2,
  degree_d_wrt_t n2 d1 ->
  degree_d_wrt_t n2 (close_d_wrt_u_rec n1 x1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_t_close_d_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_t_close_e_wrt_u_rec :
forall e1 x1 n1 n2,
  degree_e_wrt_t n2 e1 ->
  degree_e_wrt_t n2 (close_e_wrt_u_rec n1 x1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_t_close_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_close_u_wrt_u_rec :
forall u1 x1 n1 n2,
  degree_u_wrt_t n2 u1 ->
  degree_u_wrt_t n2 (close_u_wrt_u_rec n1 x1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_close_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_t_close_v_wrt_u_rec :
forall v1 x1 n1 n2,
  degree_v_wrt_t n2 v1 ->
  degree_v_wrt_t n2 (close_v_wrt_u_rec n1 x1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_t_close_v_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_close_d_wrt_t_rec_degree_e_wrt_u_close_e_wrt_t_rec_degree_u_wrt_u_close_u_wrt_t_rec_degree_v_wrt_u_close_v_wrt_t_rec_mutual :
(forall d1 a1 n1 n2,
  degree_d_wrt_u n2 d1 ->
  degree_d_wrt_u n2 (close_d_wrt_t_rec n1 a1 d1)) /\
(forall e1 a1 n1 n2,
  degree_e_wrt_u n2 e1 ->
  degree_e_wrt_u n2 (close_e_wrt_t_rec n1 a1 e1)) /\
(forall u1 a1 n1 n2,
  degree_u_wrt_u n2 u1 ->
  degree_u_wrt_u n2 (close_u_wrt_t_rec n1 a1 u1)) /\
(forall v1 a1 n1 n2,
  degree_v_wrt_u n2 v1 ->
  degree_v_wrt_u n2 (close_v_wrt_t_rec n1 a1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_close_d_wrt_t_rec :
forall d1 a1 n1 n2,
  degree_d_wrt_u n2 d1 ->
  degree_d_wrt_u n2 (close_d_wrt_t_rec n1 a1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_u_close_d_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_u_close_e_wrt_t_rec :
forall e1 a1 n1 n2,
  degree_e_wrt_u n2 e1 ->
  degree_e_wrt_u n2 (close_e_wrt_t_rec n1 a1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_u_close_e_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_u_close_u_wrt_t_rec :
forall u1 a1 n1 n2,
  degree_u_wrt_u n2 u1 ->
  degree_u_wrt_u n2 (close_u_wrt_t_rec n1 a1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_close_u_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_u_close_v_wrt_t_rec :
forall v1 a1 n1 n2,
  degree_v_wrt_u n2 v1 ->
  degree_v_wrt_u n2 (close_v_wrt_t_rec n1 a1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_u_close_v_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_close_d_wrt_u_rec_degree_e_wrt_u_close_e_wrt_u_rec_degree_u_wrt_u_close_u_wrt_u_rec_degree_v_wrt_u_close_v_wrt_u_rec_mutual :
(forall d1 x1 n1,
  degree_d_wrt_u n1 d1 ->
  degree_d_wrt_u (S n1) (close_d_wrt_u_rec n1 x1 d1)) /\
(forall e1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u (S n1) (close_e_wrt_u_rec n1 x1 e1)) /\
(forall u1 x1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u (S n1) (close_u_wrt_u_rec n1 x1 u1)) /\
(forall v1 x1 n1,
  degree_v_wrt_u n1 v1 ->
  degree_v_wrt_u (S n1) (close_v_wrt_u_rec n1 x1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_close_d_wrt_u_rec :
forall d1 x1 n1,
  degree_d_wrt_u n1 d1 ->
  degree_d_wrt_u (S n1) (close_d_wrt_u_rec n1 x1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_u_close_d_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_u_close_e_wrt_u_rec :
forall e1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u (S n1) (close_e_wrt_u_rec n1 x1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_u_close_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_u_close_u_wrt_u_rec :
forall u1 x1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u (S n1) (close_u_wrt_u_rec n1 x1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_close_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_u_close_v_wrt_u_rec :
forall v1 x1 n1,
  degree_v_wrt_u n1 v1 ->
  degree_v_wrt_u (S n1) (close_v_wrt_u_rec n1 x1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_u_close_v_wrt_u_rec : lngen.

(* end hide *)

Lemma degree_t_wrt_t_close_t_wrt_t :
forall t1 a1,
  degree_t_wrt_t 0 t1 ->
  degree_t_wrt_t 1 (close_t_wrt_t a1 t1).
Proof. Admitted.

Hint Resolve degree_t_wrt_t_close_t_wrt_t : lngen.

Lemma degree_d_wrt_t_close_d_wrt_t :
forall d1 a1,
  degree_d_wrt_t 0 d1 ->
  degree_d_wrt_t 1 (close_d_wrt_t a1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_t_close_d_wrt_t : lngen.

Lemma degree_e_wrt_t_close_e_wrt_t :
forall e1 a1,
  degree_e_wrt_t 0 e1 ->
  degree_e_wrt_t 1 (close_e_wrt_t a1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_t_close_e_wrt_t : lngen.

Lemma degree_u_wrt_t_close_u_wrt_t :
forall u1 a1,
  degree_u_wrt_t 0 u1 ->
  degree_u_wrt_t 1 (close_u_wrt_t a1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_close_u_wrt_t : lngen.

Lemma degree_v_wrt_t_close_v_wrt_t :
forall v1 a1,
  degree_v_wrt_t 0 v1 ->
  degree_v_wrt_t 1 (close_v_wrt_t a1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_t_close_v_wrt_t : lngen.

Lemma degree_d_wrt_t_close_d_wrt_u :
forall d1 x1 n1,
  degree_d_wrt_t n1 d1 ->
  degree_d_wrt_t n1 (close_d_wrt_u x1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_t_close_d_wrt_u : lngen.

Lemma degree_e_wrt_t_close_e_wrt_u :
forall e1 x1 n1,
  degree_e_wrt_t n1 e1 ->
  degree_e_wrt_t n1 (close_e_wrt_u x1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_t_close_e_wrt_u : lngen.

Lemma degree_u_wrt_t_close_u_wrt_u :
forall u1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 (close_u_wrt_u x1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_close_u_wrt_u : lngen.

Lemma degree_v_wrt_t_close_v_wrt_u :
forall v1 x1 n1,
  degree_v_wrt_t n1 v1 ->
  degree_v_wrt_t n1 (close_v_wrt_u x1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_t_close_v_wrt_u : lngen.

Lemma degree_d_wrt_u_close_d_wrt_t :
forall d1 a1 n1,
  degree_d_wrt_u n1 d1 ->
  degree_d_wrt_u n1 (close_d_wrt_t a1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_u_close_d_wrt_t : lngen.

Lemma degree_e_wrt_u_close_e_wrt_t :
forall e1 a1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u n1 (close_e_wrt_t a1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_u_close_e_wrt_t : lngen.

Lemma degree_u_wrt_u_close_u_wrt_t :
forall u1 a1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (close_u_wrt_t a1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_close_u_wrt_t : lngen.

Lemma degree_v_wrt_u_close_v_wrt_t :
forall v1 a1 n1,
  degree_v_wrt_u n1 v1 ->
  degree_v_wrt_u n1 (close_v_wrt_t a1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_u_close_v_wrt_t : lngen.

Lemma degree_d_wrt_u_close_d_wrt_u :
forall d1 x1,
  degree_d_wrt_u 0 d1 ->
  degree_d_wrt_u 1 (close_d_wrt_u x1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_u_close_d_wrt_u : lngen.

Lemma degree_e_wrt_u_close_e_wrt_u :
forall e1 x1,
  degree_e_wrt_u 0 e1 ->
  degree_e_wrt_u 1 (close_e_wrt_u x1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_u_close_e_wrt_u : lngen.

Lemma degree_u_wrt_u_close_u_wrt_u :
forall u1 x1,
  degree_u_wrt_u 0 u1 ->
  degree_u_wrt_u 1 (close_u_wrt_u x1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_close_u_wrt_u : lngen.

Lemma degree_v_wrt_u_close_v_wrt_u :
forall v1 x1,
  degree_v_wrt_u 0 v1 ->
  degree_v_wrt_u 1 (close_v_wrt_u x1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_u_close_v_wrt_u : lngen.

(* begin hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_rec_inv_mutual :
(forall t1 a1 n1,
  degree_t_wrt_t (S n1) (close_t_wrt_t_rec n1 a1 t1) ->
  degree_t_wrt_t n1 t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_rec_inv :
forall t1 a1 n1,
  degree_t_wrt_t (S n1) (close_t_wrt_t_rec n1 a1 t1) ->
  degree_t_wrt_t n1 t1.
Proof. Admitted.

Hint Immediate degree_t_wrt_t_close_t_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_close_d_wrt_t_rec_inv_degree_e_wrt_t_close_e_wrt_t_rec_inv_degree_u_wrt_t_close_u_wrt_t_rec_inv_degree_v_wrt_t_close_v_wrt_t_rec_inv_mutual :
(forall d1 a1 n1,
  degree_d_wrt_t (S n1) (close_d_wrt_t_rec n1 a1 d1) ->
  degree_d_wrt_t n1 d1) /\
(forall e1 a1 n1,
  degree_e_wrt_t (S n1) (close_e_wrt_t_rec n1 a1 e1) ->
  degree_e_wrt_t n1 e1) /\
(forall u1 a1 n1,
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1) ->
  degree_u_wrt_t n1 u1) /\
(forall v1 a1 n1,
  degree_v_wrt_t (S n1) (close_v_wrt_t_rec n1 a1 v1) ->
  degree_v_wrt_t n1 v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_close_d_wrt_t_rec_inv :
forall d1 a1 n1,
  degree_d_wrt_t (S n1) (close_d_wrt_t_rec n1 a1 d1) ->
  degree_d_wrt_t n1 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_t_close_d_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_t_close_e_wrt_t_rec_inv :
forall e1 a1 n1,
  degree_e_wrt_t (S n1) (close_e_wrt_t_rec n1 a1 e1) ->
  degree_e_wrt_t n1 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_t_close_e_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_close_u_wrt_t_rec_inv :
forall u1 a1 n1,
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1) ->
  degree_u_wrt_t n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_close_u_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_t_close_v_wrt_t_rec_inv :
forall v1 a1 n1,
  degree_v_wrt_t (S n1) (close_v_wrt_t_rec n1 a1 v1) ->
  degree_v_wrt_t n1 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_t_close_v_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_close_d_wrt_u_rec_inv_degree_e_wrt_t_close_e_wrt_u_rec_inv_degree_u_wrt_t_close_u_wrt_u_rec_inv_degree_v_wrt_t_close_v_wrt_u_rec_inv_mutual :
(forall d1 x1 n1 n2,
  degree_d_wrt_t n2 (close_d_wrt_u_rec n1 x1 d1) ->
  degree_d_wrt_t n2 d1) /\
(forall e1 x1 n1 n2,
  degree_e_wrt_t n2 (close_e_wrt_u_rec n1 x1 e1) ->
  degree_e_wrt_t n2 e1) /\
(forall u1 x1 n1 n2,
  degree_u_wrt_t n2 (close_u_wrt_u_rec n1 x1 u1) ->
  degree_u_wrt_t n2 u1) /\
(forall v1 x1 n1 n2,
  degree_v_wrt_t n2 (close_v_wrt_u_rec n1 x1 v1) ->
  degree_v_wrt_t n2 v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_close_d_wrt_u_rec_inv :
forall d1 x1 n1 n2,
  degree_d_wrt_t n2 (close_d_wrt_u_rec n1 x1 d1) ->
  degree_d_wrt_t n2 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_t_close_d_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_t_close_e_wrt_u_rec_inv :
forall e1 x1 n1 n2,
  degree_e_wrt_t n2 (close_e_wrt_u_rec n1 x1 e1) ->
  degree_e_wrt_t n2 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_t_close_e_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_close_u_wrt_u_rec_inv :
forall u1 x1 n1 n2,
  degree_u_wrt_t n2 (close_u_wrt_u_rec n1 x1 u1) ->
  degree_u_wrt_t n2 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_close_u_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_t_close_v_wrt_u_rec_inv :
forall v1 x1 n1 n2,
  degree_v_wrt_t n2 (close_v_wrt_u_rec n1 x1 v1) ->
  degree_v_wrt_t n2 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_t_close_v_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_close_d_wrt_t_rec_inv_degree_e_wrt_u_close_e_wrt_t_rec_inv_degree_u_wrt_u_close_u_wrt_t_rec_inv_degree_v_wrt_u_close_v_wrt_t_rec_inv_mutual :
(forall d1 a1 n1 n2,
  degree_d_wrt_u n2 (close_d_wrt_t_rec n1 a1 d1) ->
  degree_d_wrt_u n2 d1) /\
(forall e1 a1 n1 n2,
  degree_e_wrt_u n2 (close_e_wrt_t_rec n1 a1 e1) ->
  degree_e_wrt_u n2 e1) /\
(forall u1 a1 n1 n2,
  degree_u_wrt_u n2 (close_u_wrt_t_rec n1 a1 u1) ->
  degree_u_wrt_u n2 u1) /\
(forall v1 a1 n1 n2,
  degree_v_wrt_u n2 (close_v_wrt_t_rec n1 a1 v1) ->
  degree_v_wrt_u n2 v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_close_d_wrt_t_rec_inv :
forall d1 a1 n1 n2,
  degree_d_wrt_u n2 (close_d_wrt_t_rec n1 a1 d1) ->
  degree_d_wrt_u n2 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_u_close_d_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_u_close_e_wrt_t_rec_inv :
forall e1 a1 n1 n2,
  degree_e_wrt_u n2 (close_e_wrt_t_rec n1 a1 e1) ->
  degree_e_wrt_u n2 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_u_close_e_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_u_close_u_wrt_t_rec_inv :
forall u1 a1 n1 n2,
  degree_u_wrt_u n2 (close_u_wrt_t_rec n1 a1 u1) ->
  degree_u_wrt_u n2 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_close_u_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_u_close_v_wrt_t_rec_inv :
forall v1 a1 n1 n2,
  degree_v_wrt_u n2 (close_v_wrt_t_rec n1 a1 v1) ->
  degree_v_wrt_u n2 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_u_close_v_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_close_d_wrt_u_rec_inv_degree_e_wrt_u_close_e_wrt_u_rec_inv_degree_u_wrt_u_close_u_wrt_u_rec_inv_degree_v_wrt_u_close_v_wrt_u_rec_inv_mutual :
(forall d1 x1 n1,
  degree_d_wrt_u (S n1) (close_d_wrt_u_rec n1 x1 d1) ->
  degree_d_wrt_u n1 d1) /\
(forall e1 x1 n1,
  degree_e_wrt_u (S n1) (close_e_wrt_u_rec n1 x1 e1) ->
  degree_e_wrt_u n1 e1) /\
(forall u1 x1 n1,
  degree_u_wrt_u (S n1) (close_u_wrt_u_rec n1 x1 u1) ->
  degree_u_wrt_u n1 u1) /\
(forall v1 x1 n1,
  degree_v_wrt_u (S n1) (close_v_wrt_u_rec n1 x1 v1) ->
  degree_v_wrt_u n1 v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_close_d_wrt_u_rec_inv :
forall d1 x1 n1,
  degree_d_wrt_u (S n1) (close_d_wrt_u_rec n1 x1 d1) ->
  degree_d_wrt_u n1 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_u_close_d_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_u_close_e_wrt_u_rec_inv :
forall e1 x1 n1,
  degree_e_wrt_u (S n1) (close_e_wrt_u_rec n1 x1 e1) ->
  degree_e_wrt_u n1 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_u_close_e_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_u_close_u_wrt_u_rec_inv :
forall u1 x1 n1,
  degree_u_wrt_u (S n1) (close_u_wrt_u_rec n1 x1 u1) ->
  degree_u_wrt_u n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_close_u_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_u_close_v_wrt_u_rec_inv :
forall v1 x1 n1,
  degree_v_wrt_u (S n1) (close_v_wrt_u_rec n1 x1 v1) ->
  degree_v_wrt_u n1 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_u_close_v_wrt_u_rec_inv : lngen.

(* end hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_inv :
forall t1 a1,
  degree_t_wrt_t 1 (close_t_wrt_t a1 t1) ->
  degree_t_wrt_t 0 t1.
Proof. Admitted.

Hint Immediate degree_t_wrt_t_close_t_wrt_t_inv : lngen.

Lemma degree_d_wrt_t_close_d_wrt_t_inv :
forall d1 a1,
  degree_d_wrt_t 1 (close_d_wrt_t a1 d1) ->
  degree_d_wrt_t 0 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_t_close_d_wrt_t_inv : lngen.

Lemma degree_e_wrt_t_close_e_wrt_t_inv :
forall e1 a1,
  degree_e_wrt_t 1 (close_e_wrt_t a1 e1) ->
  degree_e_wrt_t 0 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_t_close_e_wrt_t_inv : lngen.

Lemma degree_u_wrt_t_close_u_wrt_t_inv :
forall u1 a1,
  degree_u_wrt_t 1 (close_u_wrt_t a1 u1) ->
  degree_u_wrt_t 0 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_close_u_wrt_t_inv : lngen.

Lemma degree_v_wrt_t_close_v_wrt_t_inv :
forall v1 a1,
  degree_v_wrt_t 1 (close_v_wrt_t a1 v1) ->
  degree_v_wrt_t 0 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_t_close_v_wrt_t_inv : lngen.

Lemma degree_d_wrt_t_close_d_wrt_u_inv :
forall d1 x1 n1,
  degree_d_wrt_t n1 (close_d_wrt_u x1 d1) ->
  degree_d_wrt_t n1 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_t_close_d_wrt_u_inv : lngen.

Lemma degree_e_wrt_t_close_e_wrt_u_inv :
forall e1 x1 n1,
  degree_e_wrt_t n1 (close_e_wrt_u x1 e1) ->
  degree_e_wrt_t n1 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_t_close_e_wrt_u_inv : lngen.

Lemma degree_u_wrt_t_close_u_wrt_u_inv :
forall u1 x1 n1,
  degree_u_wrt_t n1 (close_u_wrt_u x1 u1) ->
  degree_u_wrt_t n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_close_u_wrt_u_inv : lngen.

Lemma degree_v_wrt_t_close_v_wrt_u_inv :
forall v1 x1 n1,
  degree_v_wrt_t n1 (close_v_wrt_u x1 v1) ->
  degree_v_wrt_t n1 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_t_close_v_wrt_u_inv : lngen.

Lemma degree_d_wrt_u_close_d_wrt_t_inv :
forall d1 a1 n1,
  degree_d_wrt_u n1 (close_d_wrt_t a1 d1) ->
  degree_d_wrt_u n1 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_u_close_d_wrt_t_inv : lngen.

Lemma degree_e_wrt_u_close_e_wrt_t_inv :
forall e1 a1 n1,
  degree_e_wrt_u n1 (close_e_wrt_t a1 e1) ->
  degree_e_wrt_u n1 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_u_close_e_wrt_t_inv : lngen.

Lemma degree_u_wrt_u_close_u_wrt_t_inv :
forall u1 a1 n1,
  degree_u_wrt_u n1 (close_u_wrt_t a1 u1) ->
  degree_u_wrt_u n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_close_u_wrt_t_inv : lngen.

Lemma degree_v_wrt_u_close_v_wrt_t_inv :
forall v1 a1 n1,
  degree_v_wrt_u n1 (close_v_wrt_t a1 v1) ->
  degree_v_wrt_u n1 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_u_close_v_wrt_t_inv : lngen.

Lemma degree_d_wrt_u_close_d_wrt_u_inv :
forall d1 x1,
  degree_d_wrt_u 1 (close_d_wrt_u x1 d1) ->
  degree_d_wrt_u 0 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_u_close_d_wrt_u_inv : lngen.

Lemma degree_e_wrt_u_close_e_wrt_u_inv :
forall e1 x1,
  degree_e_wrt_u 1 (close_e_wrt_u x1 e1) ->
  degree_e_wrt_u 0 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_u_close_e_wrt_u_inv : lngen.

Lemma degree_u_wrt_u_close_u_wrt_u_inv :
forall u1 x1,
  degree_u_wrt_u 1 (close_u_wrt_u x1 u1) ->
  degree_u_wrt_u 0 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_close_u_wrt_u_inv : lngen.

Lemma degree_v_wrt_u_close_v_wrt_u_inv :
forall v1 x1,
  degree_v_wrt_u 1 (close_v_wrt_u x1 v1) ->
  degree_v_wrt_u 0 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_u_close_v_wrt_u_inv : lngen.

(* begin hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_rec_mutual :
(forall t1 t2 n1,
  degree_t_wrt_t (S n1) t1 ->
  degree_t_wrt_t n1 t2 ->
  degree_t_wrt_t n1 (open_t_wrt_t_rec n1 t2 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_rec :
forall t1 t2 n1,
  degree_t_wrt_t (S n1) t1 ->
  degree_t_wrt_t n1 t2 ->
  degree_t_wrt_t n1 (open_t_wrt_t_rec n1 t2 t1).
Proof. Admitted.

Hint Resolve degree_t_wrt_t_open_t_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_open_d_wrt_t_rec_degree_e_wrt_t_open_e_wrt_t_rec_degree_u_wrt_t_open_u_wrt_t_rec_degree_v_wrt_t_open_v_wrt_t_rec_mutual :
(forall d1 t1 n1,
  degree_d_wrt_t (S n1) d1 ->
  degree_t_wrt_t n1 t1 ->
  degree_d_wrt_t n1 (open_d_wrt_t_rec n1 t1 d1)) /\
(forall e1 t1 n1,
  degree_e_wrt_t (S n1) e1 ->
  degree_t_wrt_t n1 t1 ->
  degree_e_wrt_t n1 (open_e_wrt_t_rec n1 t1 e1)) /\
(forall u1 t1 n1,
  degree_u_wrt_t (S n1) u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1)) /\
(forall v1 t1 n1,
  degree_v_wrt_t (S n1) v1 ->
  degree_t_wrt_t n1 t1 ->
  degree_v_wrt_t n1 (open_v_wrt_t_rec n1 t1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_open_d_wrt_t_rec :
forall d1 t1 n1,
  degree_d_wrt_t (S n1) d1 ->
  degree_t_wrt_t n1 t1 ->
  degree_d_wrt_t n1 (open_d_wrt_t_rec n1 t1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_t_open_d_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_t_open_e_wrt_t_rec :
forall e1 t1 n1,
  degree_e_wrt_t (S n1) e1 ->
  degree_t_wrt_t n1 t1 ->
  degree_e_wrt_t n1 (open_e_wrt_t_rec n1 t1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_t_open_e_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_open_u_wrt_t_rec :
forall u1 t1 n1,
  degree_u_wrt_t (S n1) u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_open_u_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_t_open_v_wrt_t_rec :
forall v1 t1 n1,
  degree_v_wrt_t (S n1) v1 ->
  degree_t_wrt_t n1 t1 ->
  degree_v_wrt_t n1 (open_v_wrt_t_rec n1 t1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_t_open_v_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_open_d_wrt_u_rec_degree_e_wrt_t_open_e_wrt_u_rec_degree_u_wrt_t_open_u_wrt_u_rec_degree_v_wrt_t_open_v_wrt_u_rec_mutual :
(forall d1 u1 n1 n2,
  degree_d_wrt_t n1 d1 ->
  degree_u_wrt_t n1 u1 ->
  degree_d_wrt_t n1 (open_d_wrt_u_rec n2 u1 d1)) /\
(forall e1 u1 n1 n2,
  degree_e_wrt_t n1 e1 ->
  degree_u_wrt_t n1 u1 ->
  degree_e_wrt_t n1 (open_e_wrt_u_rec n2 u1 e1)) /\
(forall u1 u2 n1 n2,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 u2 ->
  degree_u_wrt_t n1 (open_u_wrt_u_rec n2 u2 u1)) /\
(forall v1 u1 n1 n2,
  degree_v_wrt_t n1 v1 ->
  degree_u_wrt_t n1 u1 ->
  degree_v_wrt_t n1 (open_v_wrt_u_rec n2 u1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_open_d_wrt_u_rec :
forall d1 u1 n1 n2,
  degree_d_wrt_t n1 d1 ->
  degree_u_wrt_t n1 u1 ->
  degree_d_wrt_t n1 (open_d_wrt_u_rec n2 u1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_t_open_d_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_t_open_e_wrt_u_rec :
forall e1 u1 n1 n2,
  degree_e_wrt_t n1 e1 ->
  degree_u_wrt_t n1 u1 ->
  degree_e_wrt_t n1 (open_e_wrt_u_rec n2 u1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_t_open_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_open_u_wrt_u_rec :
forall u1 u2 n1 n2,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 u2 ->
  degree_u_wrt_t n1 (open_u_wrt_u_rec n2 u2 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_open_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_t_open_v_wrt_u_rec :
forall v1 u1 n1 n2,
  degree_v_wrt_t n1 v1 ->
  degree_u_wrt_t n1 u1 ->
  degree_v_wrt_t n1 (open_v_wrt_u_rec n2 u1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_t_open_v_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_open_d_wrt_t_rec_degree_e_wrt_u_open_e_wrt_t_rec_degree_u_wrt_u_open_u_wrt_t_rec_degree_v_wrt_u_open_v_wrt_t_rec_mutual :
(forall d1 t1 n1 n2,
  degree_d_wrt_u n1 d1 ->
  degree_d_wrt_u n1 (open_d_wrt_t_rec n2 t1 d1)) /\
(forall e1 t1 n1 n2,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u n1 (open_e_wrt_t_rec n2 t1 e1)) /\
(forall u1 t1 n1 n2,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (open_u_wrt_t_rec n2 t1 u1)) /\
(forall v1 t1 n1 n2,
  degree_v_wrt_u n1 v1 ->
  degree_v_wrt_u n1 (open_v_wrt_t_rec n2 t1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_open_d_wrt_t_rec :
forall d1 t1 n1 n2,
  degree_d_wrt_u n1 d1 ->
  degree_d_wrt_u n1 (open_d_wrt_t_rec n2 t1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_u_open_d_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_u_open_e_wrt_t_rec :
forall e1 t1 n1 n2,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u n1 (open_e_wrt_t_rec n2 t1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_u_open_e_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_u_open_u_wrt_t_rec :
forall u1 t1 n1 n2,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (open_u_wrt_t_rec n2 t1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_open_u_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_u_open_v_wrt_t_rec :
forall v1 t1 n1 n2,
  degree_v_wrt_u n1 v1 ->
  degree_v_wrt_u n1 (open_v_wrt_t_rec n2 t1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_u_open_v_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_open_d_wrt_u_rec_degree_e_wrt_u_open_e_wrt_u_rec_degree_u_wrt_u_open_u_wrt_u_rec_degree_v_wrt_u_open_v_wrt_u_rec_mutual :
(forall d1 u1 n1,
  degree_d_wrt_u (S n1) d1 ->
  degree_u_wrt_u n1 u1 ->
  degree_d_wrt_u n1 (open_d_wrt_u_rec n1 u1 d1)) /\
(forall e1 u1 n1,
  degree_e_wrt_u (S n1) e1 ->
  degree_u_wrt_u n1 u1 ->
  degree_e_wrt_u n1 (open_e_wrt_u_rec n1 u1 e1)) /\
(forall u1 u2 n1,
  degree_u_wrt_u (S n1) u1 ->
  degree_u_wrt_u n1 u2 ->
  degree_u_wrt_u n1 (open_u_wrt_u_rec n1 u2 u1)) /\
(forall v1 u1 n1,
  degree_v_wrt_u (S n1) v1 ->
  degree_u_wrt_u n1 u1 ->
  degree_v_wrt_u n1 (open_v_wrt_u_rec n1 u1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_open_d_wrt_u_rec :
forall d1 u1 n1,
  degree_d_wrt_u (S n1) d1 ->
  degree_u_wrt_u n1 u1 ->
  degree_d_wrt_u n1 (open_d_wrt_u_rec n1 u1 d1).
Proof. Admitted.

Hint Resolve degree_d_wrt_u_open_d_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_u_open_e_wrt_u_rec :
forall e1 u1 n1,
  degree_e_wrt_u (S n1) e1 ->
  degree_u_wrt_u n1 u1 ->
  degree_e_wrt_u n1 (open_e_wrt_u_rec n1 u1 e1).
Proof. Admitted.

Hint Resolve degree_e_wrt_u_open_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_u_open_u_wrt_u_rec :
forall u1 u2 n1,
  degree_u_wrt_u (S n1) u1 ->
  degree_u_wrt_u n1 u2 ->
  degree_u_wrt_u n1 (open_u_wrt_u_rec n1 u2 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_open_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_u_open_v_wrt_u_rec :
forall v1 u1 n1,
  degree_v_wrt_u (S n1) v1 ->
  degree_u_wrt_u n1 u1 ->
  degree_v_wrt_u n1 (open_v_wrt_u_rec n1 u1 v1).
Proof. Admitted.

Hint Resolve degree_v_wrt_u_open_v_wrt_u_rec : lngen.

(* end hide *)

Lemma degree_t_wrt_t_open_t_wrt_t :
forall t1 t2,
  degree_t_wrt_t 1 t1 ->
  degree_t_wrt_t 0 t2 ->
  degree_t_wrt_t 0 (open_t_wrt_t t1 t2).
Proof. Admitted.

Hint Resolve degree_t_wrt_t_open_t_wrt_t : lngen.

Lemma degree_d_wrt_t_open_d_wrt_t :
forall d1 t1,
  degree_d_wrt_t 1 d1 ->
  degree_t_wrt_t 0 t1 ->
  degree_d_wrt_t 0 (open_d_wrt_t d1 t1).
Proof. Admitted.

Hint Resolve degree_d_wrt_t_open_d_wrt_t : lngen.

Lemma degree_e_wrt_t_open_e_wrt_t :
forall e1 t1,
  degree_e_wrt_t 1 e1 ->
  degree_t_wrt_t 0 t1 ->
  degree_e_wrt_t 0 (open_e_wrt_t e1 t1).
Proof. Admitted.

Hint Resolve degree_e_wrt_t_open_e_wrt_t : lngen.

Lemma degree_u_wrt_t_open_u_wrt_t :
forall u1 t1,
  degree_u_wrt_t 1 u1 ->
  degree_t_wrt_t 0 t1 ->
  degree_u_wrt_t 0 (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_open_u_wrt_t : lngen.

Lemma degree_v_wrt_t_open_v_wrt_t :
forall v1 t1,
  degree_v_wrt_t 1 v1 ->
  degree_t_wrt_t 0 t1 ->
  degree_v_wrt_t 0 (open_v_wrt_t v1 t1).
Proof. Admitted.

Hint Resolve degree_v_wrt_t_open_v_wrt_t : lngen.

Lemma degree_d_wrt_t_open_d_wrt_u :
forall d1 u1 n1,
  degree_d_wrt_t n1 d1 ->
  degree_u_wrt_t n1 u1 ->
  degree_d_wrt_t n1 (open_d_wrt_u d1 u1).
Proof. Admitted.

Hint Resolve degree_d_wrt_t_open_d_wrt_u : lngen.

Lemma degree_e_wrt_t_open_e_wrt_u :
forall e1 u1 n1,
  degree_e_wrt_t n1 e1 ->
  degree_u_wrt_t n1 u1 ->
  degree_e_wrt_t n1 (open_e_wrt_u e1 u1).
Proof. Admitted.

Hint Resolve degree_e_wrt_t_open_e_wrt_u : lngen.

Lemma degree_u_wrt_t_open_u_wrt_u :
forall u1 u2 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 u2 ->
  degree_u_wrt_t n1 (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_open_u_wrt_u : lngen.

Lemma degree_v_wrt_t_open_v_wrt_u :
forall v1 u1 n1,
  degree_v_wrt_t n1 v1 ->
  degree_u_wrt_t n1 u1 ->
  degree_v_wrt_t n1 (open_v_wrt_u v1 u1).
Proof. Admitted.

Hint Resolve degree_v_wrt_t_open_v_wrt_u : lngen.

Lemma degree_d_wrt_u_open_d_wrt_t :
forall d1 t1 n1,
  degree_d_wrt_u n1 d1 ->
  degree_d_wrt_u n1 (open_d_wrt_t d1 t1).
Proof. Admitted.

Hint Resolve degree_d_wrt_u_open_d_wrt_t : lngen.

Lemma degree_e_wrt_u_open_e_wrt_t :
forall e1 t1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u n1 (open_e_wrt_t e1 t1).
Proof. Admitted.

Hint Resolve degree_e_wrt_u_open_e_wrt_t : lngen.

Lemma degree_u_wrt_u_open_u_wrt_t :
forall u1 t1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_open_u_wrt_t : lngen.

Lemma degree_v_wrt_u_open_v_wrt_t :
forall v1 t1 n1,
  degree_v_wrt_u n1 v1 ->
  degree_v_wrt_u n1 (open_v_wrt_t v1 t1).
Proof. Admitted.

Hint Resolve degree_v_wrt_u_open_v_wrt_t : lngen.

Lemma degree_d_wrt_u_open_d_wrt_u :
forall d1 u1,
  degree_d_wrt_u 1 d1 ->
  degree_u_wrt_u 0 u1 ->
  degree_d_wrt_u 0 (open_d_wrt_u d1 u1).
Proof. Admitted.

Hint Resolve degree_d_wrt_u_open_d_wrt_u : lngen.

Lemma degree_e_wrt_u_open_e_wrt_u :
forall e1 u1,
  degree_e_wrt_u 1 e1 ->
  degree_u_wrt_u 0 u1 ->
  degree_e_wrt_u 0 (open_e_wrt_u e1 u1).
Proof. Admitted.

Hint Resolve degree_e_wrt_u_open_e_wrt_u : lngen.

Lemma degree_u_wrt_u_open_u_wrt_u :
forall u1 u2,
  degree_u_wrt_u 1 u1 ->
  degree_u_wrt_u 0 u2 ->
  degree_u_wrt_u 0 (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_open_u_wrt_u : lngen.

Lemma degree_v_wrt_u_open_v_wrt_u :
forall v1 u1,
  degree_v_wrt_u 1 v1 ->
  degree_u_wrt_u 0 u1 ->
  degree_v_wrt_u 0 (open_v_wrt_u v1 u1).
Proof. Admitted.

Hint Resolve degree_v_wrt_u_open_v_wrt_u : lngen.

(* begin hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_rec_inv_mutual :
(forall t1 t2 n1,
  degree_t_wrt_t n1 (open_t_wrt_t_rec n1 t2 t1) ->
  degree_t_wrt_t (S n1) t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_rec_inv :
forall t1 t2 n1,
  degree_t_wrt_t n1 (open_t_wrt_t_rec n1 t2 t1) ->
  degree_t_wrt_t (S n1) t1.
Proof. Admitted.

Hint Immediate degree_t_wrt_t_open_t_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_open_d_wrt_t_rec_inv_degree_e_wrt_t_open_e_wrt_t_rec_inv_degree_u_wrt_t_open_u_wrt_t_rec_inv_degree_v_wrt_t_open_v_wrt_t_rec_inv_mutual :
(forall d1 t1 n1,
  degree_d_wrt_t n1 (open_d_wrt_t_rec n1 t1 d1) ->
  degree_d_wrt_t (S n1) d1) /\
(forall e1 t1 n1,
  degree_e_wrt_t n1 (open_e_wrt_t_rec n1 t1 e1) ->
  degree_e_wrt_t (S n1) e1) /\
(forall u1 t1 n1,
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1) ->
  degree_u_wrt_t (S n1) u1) /\
(forall v1 t1 n1,
  degree_v_wrt_t n1 (open_v_wrt_t_rec n1 t1 v1) ->
  degree_v_wrt_t (S n1) v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_open_d_wrt_t_rec_inv :
forall d1 t1 n1,
  degree_d_wrt_t n1 (open_d_wrt_t_rec n1 t1 d1) ->
  degree_d_wrt_t (S n1) d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_t_open_d_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_t_open_e_wrt_t_rec_inv :
forall e1 t1 n1,
  degree_e_wrt_t n1 (open_e_wrt_t_rec n1 t1 e1) ->
  degree_e_wrt_t (S n1) e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_t_open_e_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_open_u_wrt_t_rec_inv :
forall u1 t1 n1,
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1) ->
  degree_u_wrt_t (S n1) u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_open_u_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_t_open_v_wrt_t_rec_inv :
forall v1 t1 n1,
  degree_v_wrt_t n1 (open_v_wrt_t_rec n1 t1 v1) ->
  degree_v_wrt_t (S n1) v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_t_open_v_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_open_d_wrt_u_rec_inv_degree_e_wrt_t_open_e_wrt_u_rec_inv_degree_u_wrt_t_open_u_wrt_u_rec_inv_degree_v_wrt_t_open_v_wrt_u_rec_inv_mutual :
(forall d1 u1 n1 n2,
  degree_d_wrt_t n1 (open_d_wrt_u_rec n2 u1 d1) ->
  degree_d_wrt_t n1 d1) /\
(forall e1 u1 n1 n2,
  degree_e_wrt_t n1 (open_e_wrt_u_rec n2 u1 e1) ->
  degree_e_wrt_t n1 e1) /\
(forall u1 u2 n1 n2,
  degree_u_wrt_t n1 (open_u_wrt_u_rec n2 u2 u1) ->
  degree_u_wrt_t n1 u1) /\
(forall v1 u1 n1 n2,
  degree_v_wrt_t n1 (open_v_wrt_u_rec n2 u1 v1) ->
  degree_v_wrt_t n1 v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_t_open_d_wrt_u_rec_inv :
forall d1 u1 n1 n2,
  degree_d_wrt_t n1 (open_d_wrt_u_rec n2 u1 d1) ->
  degree_d_wrt_t n1 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_t_open_d_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_t_open_e_wrt_u_rec_inv :
forall e1 u1 n1 n2,
  degree_e_wrt_t n1 (open_e_wrt_u_rec n2 u1 e1) ->
  degree_e_wrt_t n1 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_t_open_e_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_open_u_wrt_u_rec_inv :
forall u1 u2 n1 n2,
  degree_u_wrt_t n1 (open_u_wrt_u_rec n2 u2 u1) ->
  degree_u_wrt_t n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_open_u_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_t_open_v_wrt_u_rec_inv :
forall v1 u1 n1 n2,
  degree_v_wrt_t n1 (open_v_wrt_u_rec n2 u1 v1) ->
  degree_v_wrt_t n1 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_t_open_v_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_open_d_wrt_t_rec_inv_degree_e_wrt_u_open_e_wrt_t_rec_inv_degree_u_wrt_u_open_u_wrt_t_rec_inv_degree_v_wrt_u_open_v_wrt_t_rec_inv_mutual :
(forall d1 t1 n1 n2,
  degree_d_wrt_u n1 (open_d_wrt_t_rec n2 t1 d1) ->
  degree_d_wrt_u n1 d1) /\
(forall e1 t1 n1 n2,
  degree_e_wrt_u n1 (open_e_wrt_t_rec n2 t1 e1) ->
  degree_e_wrt_u n1 e1) /\
(forall u1 t1 n1 n2,
  degree_u_wrt_u n1 (open_u_wrt_t_rec n2 t1 u1) ->
  degree_u_wrt_u n1 u1) /\
(forall v1 t1 n1 n2,
  degree_v_wrt_u n1 (open_v_wrt_t_rec n2 t1 v1) ->
  degree_v_wrt_u n1 v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_open_d_wrt_t_rec_inv :
forall d1 t1 n1 n2,
  degree_d_wrt_u n1 (open_d_wrt_t_rec n2 t1 d1) ->
  degree_d_wrt_u n1 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_u_open_d_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_u_open_e_wrt_t_rec_inv :
forall e1 t1 n1 n2,
  degree_e_wrt_u n1 (open_e_wrt_t_rec n2 t1 e1) ->
  degree_e_wrt_u n1 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_u_open_e_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_u_open_u_wrt_t_rec_inv :
forall u1 t1 n1 n2,
  degree_u_wrt_u n1 (open_u_wrt_t_rec n2 t1 u1) ->
  degree_u_wrt_u n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_open_u_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_u_open_v_wrt_t_rec_inv :
forall v1 t1 n1 n2,
  degree_v_wrt_u n1 (open_v_wrt_t_rec n2 t1 v1) ->
  degree_v_wrt_u n1 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_u_open_v_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_open_d_wrt_u_rec_inv_degree_e_wrt_u_open_e_wrt_u_rec_inv_degree_u_wrt_u_open_u_wrt_u_rec_inv_degree_v_wrt_u_open_v_wrt_u_rec_inv_mutual :
(forall d1 u1 n1,
  degree_d_wrt_u n1 (open_d_wrt_u_rec n1 u1 d1) ->
  degree_d_wrt_u (S n1) d1) /\
(forall e1 u1 n1,
  degree_e_wrt_u n1 (open_e_wrt_u_rec n1 u1 e1) ->
  degree_e_wrt_u (S n1) e1) /\
(forall u1 u2 n1,
  degree_u_wrt_u n1 (open_u_wrt_u_rec n1 u2 u1) ->
  degree_u_wrt_u (S n1) u1) /\
(forall v1 u1 n1,
  degree_v_wrt_u n1 (open_v_wrt_u_rec n1 u1 v1) ->
  degree_v_wrt_u (S n1) v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_d_wrt_u_open_d_wrt_u_rec_inv :
forall d1 u1 n1,
  degree_d_wrt_u n1 (open_d_wrt_u_rec n1 u1 d1) ->
  degree_d_wrt_u (S n1) d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_u_open_d_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_u_open_e_wrt_u_rec_inv :
forall e1 u1 n1,
  degree_e_wrt_u n1 (open_e_wrt_u_rec n1 u1 e1) ->
  degree_e_wrt_u (S n1) e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_u_open_e_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_u_open_u_wrt_u_rec_inv :
forall u1 u2 n1,
  degree_u_wrt_u n1 (open_u_wrt_u_rec n1 u2 u1) ->
  degree_u_wrt_u (S n1) u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_open_u_wrt_u_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_v_wrt_u_open_v_wrt_u_rec_inv :
forall v1 u1 n1,
  degree_v_wrt_u n1 (open_v_wrt_u_rec n1 u1 v1) ->
  degree_v_wrt_u (S n1) v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_u_open_v_wrt_u_rec_inv : lngen.

(* end hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_inv :
forall t1 t2,
  degree_t_wrt_t 0 (open_t_wrt_t t1 t2) ->
  degree_t_wrt_t 1 t1.
Proof. Admitted.

Hint Immediate degree_t_wrt_t_open_t_wrt_t_inv : lngen.

Lemma degree_d_wrt_t_open_d_wrt_t_inv :
forall d1 t1,
  degree_d_wrt_t 0 (open_d_wrt_t d1 t1) ->
  degree_d_wrt_t 1 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_t_open_d_wrt_t_inv : lngen.

Lemma degree_e_wrt_t_open_e_wrt_t_inv :
forall e1 t1,
  degree_e_wrt_t 0 (open_e_wrt_t e1 t1) ->
  degree_e_wrt_t 1 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_t_open_e_wrt_t_inv : lngen.

Lemma degree_u_wrt_t_open_u_wrt_t_inv :
forall u1 t1,
  degree_u_wrt_t 0 (open_u_wrt_t u1 t1) ->
  degree_u_wrt_t 1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_open_u_wrt_t_inv : lngen.

Lemma degree_v_wrt_t_open_v_wrt_t_inv :
forall v1 t1,
  degree_v_wrt_t 0 (open_v_wrt_t v1 t1) ->
  degree_v_wrt_t 1 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_t_open_v_wrt_t_inv : lngen.

Lemma degree_d_wrt_t_open_d_wrt_u_inv :
forall d1 u1 n1,
  degree_d_wrt_t n1 (open_d_wrt_u d1 u1) ->
  degree_d_wrt_t n1 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_t_open_d_wrt_u_inv : lngen.

Lemma degree_e_wrt_t_open_e_wrt_u_inv :
forall e1 u1 n1,
  degree_e_wrt_t n1 (open_e_wrt_u e1 u1) ->
  degree_e_wrt_t n1 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_t_open_e_wrt_u_inv : lngen.

Lemma degree_u_wrt_t_open_u_wrt_u_inv :
forall u1 u2 n1,
  degree_u_wrt_t n1 (open_u_wrt_u u1 u2) ->
  degree_u_wrt_t n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_open_u_wrt_u_inv : lngen.

Lemma degree_v_wrt_t_open_v_wrt_u_inv :
forall v1 u1 n1,
  degree_v_wrt_t n1 (open_v_wrt_u v1 u1) ->
  degree_v_wrt_t n1 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_t_open_v_wrt_u_inv : lngen.

Lemma degree_d_wrt_u_open_d_wrt_t_inv :
forall d1 t1 n1,
  degree_d_wrt_u n1 (open_d_wrt_t d1 t1) ->
  degree_d_wrt_u n1 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_u_open_d_wrt_t_inv : lngen.

Lemma degree_e_wrt_u_open_e_wrt_t_inv :
forall e1 t1 n1,
  degree_e_wrt_u n1 (open_e_wrt_t e1 t1) ->
  degree_e_wrt_u n1 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_u_open_e_wrt_t_inv : lngen.

Lemma degree_u_wrt_u_open_u_wrt_t_inv :
forall u1 t1 n1,
  degree_u_wrt_u n1 (open_u_wrt_t u1 t1) ->
  degree_u_wrt_u n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_open_u_wrt_t_inv : lngen.

Lemma degree_v_wrt_u_open_v_wrt_t_inv :
forall v1 t1 n1,
  degree_v_wrt_u n1 (open_v_wrt_t v1 t1) ->
  degree_v_wrt_u n1 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_u_open_v_wrt_t_inv : lngen.

Lemma degree_d_wrt_u_open_d_wrt_u_inv :
forall d1 u1,
  degree_d_wrt_u 0 (open_d_wrt_u d1 u1) ->
  degree_d_wrt_u 1 d1.
Proof. Admitted.

Hint Immediate degree_d_wrt_u_open_d_wrt_u_inv : lngen.

Lemma degree_e_wrt_u_open_e_wrt_u_inv :
forall e1 u1,
  degree_e_wrt_u 0 (open_e_wrt_u e1 u1) ->
  degree_e_wrt_u 1 e1.
Proof. Admitted.

Hint Immediate degree_e_wrt_u_open_e_wrt_u_inv : lngen.

Lemma degree_u_wrt_u_open_u_wrt_u_inv :
forall u1 u2,
  degree_u_wrt_u 0 (open_u_wrt_u u1 u2) ->
  degree_u_wrt_u 1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_open_u_wrt_u_inv : lngen.

Lemma degree_v_wrt_u_open_v_wrt_u_inv :
forall v1 u1,
  degree_v_wrt_u 0 (open_v_wrt_u v1 u1) ->
  degree_v_wrt_u 1 v1.
Proof. Admitted.

Hint Immediate degree_v_wrt_u_open_v_wrt_u_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_t_wrt_t_rec_inj_mutual :
(forall t1 t2 a1 n1,
  close_t_wrt_t_rec n1 a1 t1 = close_t_wrt_t_rec n1 a1 t2 ->
  t1 = t2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_t_wrt_t_rec_inj :
forall t1 t2 a1 n1,
  close_t_wrt_t_rec n1 a1 t1 = close_t_wrt_t_rec n1 a1 t2 ->
  t1 = t2.
Proof. Admitted.

Hint Immediate close_t_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_t_rec_inj_close_e_wrt_t_rec_inj_close_u_wrt_t_rec_inj_close_v_wrt_t_rec_inj_mutual :
(forall d1 d2 a1 n1,
  close_d_wrt_t_rec n1 a1 d1 = close_d_wrt_t_rec n1 a1 d2 ->
  d1 = d2) /\
(forall e1 e2 a1 n1,
  close_e_wrt_t_rec n1 a1 e1 = close_e_wrt_t_rec n1 a1 e2 ->
  e1 = e2) /\
(forall u1 u2 a1 n1,
  close_u_wrt_t_rec n1 a1 u1 = close_u_wrt_t_rec n1 a1 u2 ->
  u1 = u2) /\
(forall v1 v2 a1 n1,
  close_v_wrt_t_rec n1 a1 v1 = close_v_wrt_t_rec n1 a1 v2 ->
  v1 = v2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_t_rec_inj :
forall d1 d2 a1 n1,
  close_d_wrt_t_rec n1 a1 d1 = close_d_wrt_t_rec n1 a1 d2 ->
  d1 = d2.
Proof. Admitted.

Hint Immediate close_d_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_t_rec_inj :
forall e1 e2 a1 n1,
  close_e_wrt_t_rec n1 a1 e1 = close_e_wrt_t_rec n1 a1 e2 ->
  e1 = e2.
Proof. Admitted.

Hint Immediate close_e_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_t_rec_inj :
forall u1 u2 a1 n1,
  close_u_wrt_t_rec n1 a1 u1 = close_u_wrt_t_rec n1 a1 u2 ->
  u1 = u2.
Proof. Admitted.

Hint Immediate close_u_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_v_wrt_t_rec_inj :
forall v1 v2 a1 n1,
  close_v_wrt_t_rec n1 a1 v1 = close_v_wrt_t_rec n1 a1 v2 ->
  v1 = v2.
Proof. Admitted.

Hint Immediate close_v_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_u_rec_inj_close_e_wrt_u_rec_inj_close_u_wrt_u_rec_inj_close_v_wrt_u_rec_inj_mutual :
(forall d1 d2 x1 n1,
  close_d_wrt_u_rec n1 x1 d1 = close_d_wrt_u_rec n1 x1 d2 ->
  d1 = d2) /\
(forall e1 e2 x1 n1,
  close_e_wrt_u_rec n1 x1 e1 = close_e_wrt_u_rec n1 x1 e2 ->
  e1 = e2) /\
(forall u1 u2 x1 n1,
  close_u_wrt_u_rec n1 x1 u1 = close_u_wrt_u_rec n1 x1 u2 ->
  u1 = u2) /\
(forall v1 v2 x1 n1,
  close_v_wrt_u_rec n1 x1 v1 = close_v_wrt_u_rec n1 x1 v2 ->
  v1 = v2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_u_rec_inj :
forall d1 d2 x1 n1,
  close_d_wrt_u_rec n1 x1 d1 = close_d_wrt_u_rec n1 x1 d2 ->
  d1 = d2.
Proof. Admitted.

Hint Immediate close_d_wrt_u_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_u_rec_inj :
forall e1 e2 x1 n1,
  close_e_wrt_u_rec n1 x1 e1 = close_e_wrt_u_rec n1 x1 e2 ->
  e1 = e2.
Proof. Admitted.

Hint Immediate close_e_wrt_u_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_u_rec_inj :
forall u1 u2 x1 n1,
  close_u_wrt_u_rec n1 x1 u1 = close_u_wrt_u_rec n1 x1 u2 ->
  u1 = u2.
Proof. Admitted.

Hint Immediate close_u_wrt_u_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_v_wrt_u_rec_inj :
forall v1 v2 x1 n1,
  close_v_wrt_u_rec n1 x1 v1 = close_v_wrt_u_rec n1 x1 v2 ->
  v1 = v2.
Proof. Admitted.

Hint Immediate close_v_wrt_u_rec_inj : lngen.

(* end hide *)

Lemma close_t_wrt_t_inj :
forall t1 t2 a1,
  close_t_wrt_t a1 t1 = close_t_wrt_t a1 t2 ->
  t1 = t2.
Proof. Admitted.

Hint Immediate close_t_wrt_t_inj : lngen.

Lemma close_d_wrt_t_inj :
forall d1 d2 a1,
  close_d_wrt_t a1 d1 = close_d_wrt_t a1 d2 ->
  d1 = d2.
Proof. Admitted.

Hint Immediate close_d_wrt_t_inj : lngen.

Lemma close_e_wrt_t_inj :
forall e1 e2 a1,
  close_e_wrt_t a1 e1 = close_e_wrt_t a1 e2 ->
  e1 = e2.
Proof. Admitted.

Hint Immediate close_e_wrt_t_inj : lngen.

Lemma close_u_wrt_t_inj :
forall u1 u2 a1,
  close_u_wrt_t a1 u1 = close_u_wrt_t a1 u2 ->
  u1 = u2.
Proof. Admitted.

Hint Immediate close_u_wrt_t_inj : lngen.

Lemma close_v_wrt_t_inj :
forall v1 v2 a1,
  close_v_wrt_t a1 v1 = close_v_wrt_t a1 v2 ->
  v1 = v2.
Proof. Admitted.

Hint Immediate close_v_wrt_t_inj : lngen.

Lemma close_d_wrt_u_inj :
forall d1 d2 x1,
  close_d_wrt_u x1 d1 = close_d_wrt_u x1 d2 ->
  d1 = d2.
Proof. Admitted.

Hint Immediate close_d_wrt_u_inj : lngen.

Lemma close_e_wrt_u_inj :
forall e1 e2 x1,
  close_e_wrt_u x1 e1 = close_e_wrt_u x1 e2 ->
  e1 = e2.
Proof. Admitted.

Hint Immediate close_e_wrt_u_inj : lngen.

Lemma close_u_wrt_u_inj :
forall u1 u2 x1,
  close_u_wrt_u x1 u1 = close_u_wrt_u x1 u2 ->
  u1 = u2.
Proof. Admitted.

Hint Immediate close_u_wrt_u_inj : lngen.

Lemma close_v_wrt_u_inj :
forall v1 v2 x1,
  close_v_wrt_u x1 v1 = close_v_wrt_u x1 v2 ->
  v1 = v2.
Proof. Admitted.

Hint Immediate close_v_wrt_u_inj : lngen.

(* begin hide *)

Lemma close_t_wrt_t_rec_open_t_wrt_t_rec_mutual :
(forall t1 a1 n1,
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t_rec n1 a1 (open_t_wrt_t_rec n1 (t_var_f a1) t1) = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_t_wrt_t_rec_open_t_wrt_t_rec :
forall t1 a1 n1,
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t_rec n1 a1 (open_t_wrt_t_rec n1 (t_var_f a1) t1) = t1.
Proof. Admitted.

Hint Resolve close_t_wrt_t_rec_open_t_wrt_t_rec : lngen.
Hint Rewrite close_t_wrt_t_rec_open_t_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_t_rec_open_d_wrt_t_rec_close_e_wrt_t_rec_open_e_wrt_t_rec_close_u_wrt_t_rec_open_u_wrt_t_rec_close_v_wrt_t_rec_open_v_wrt_t_rec_mutual :
(forall d1 a1 n1,
  a1 `notin` tt_fv_d d1 ->
  close_d_wrt_t_rec n1 a1 (open_d_wrt_t_rec n1 (t_var_f a1) d1) = d1) /\
(forall e1 a1 n1,
  a1 `notin` tt_fv_e e1 ->
  close_e_wrt_t_rec n1 a1 (open_e_wrt_t_rec n1 (t_var_f a1) e1) = e1) /\
(forall u1 a1 n1,
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t_rec n1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1) = u1) /\
(forall v1 a1 n1,
  a1 `notin` tt_fv_v v1 ->
  close_v_wrt_t_rec n1 a1 (open_v_wrt_t_rec n1 (t_var_f a1) v1) = v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_t_rec_open_d_wrt_t_rec :
forall d1 a1 n1,
  a1 `notin` tt_fv_d d1 ->
  close_d_wrt_t_rec n1 a1 (open_d_wrt_t_rec n1 (t_var_f a1) d1) = d1.
Proof. Admitted.

Hint Resolve close_d_wrt_t_rec_open_d_wrt_t_rec : lngen.
Hint Rewrite close_d_wrt_t_rec_open_d_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_t_rec_open_e_wrt_t_rec :
forall e1 a1 n1,
  a1 `notin` tt_fv_e e1 ->
  close_e_wrt_t_rec n1 a1 (open_e_wrt_t_rec n1 (t_var_f a1) e1) = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_t_rec_open_e_wrt_t_rec : lngen.
Hint Rewrite close_e_wrt_t_rec_open_e_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_t_rec_open_u_wrt_t_rec :
forall u1 a1 n1,
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t_rec n1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1) = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_t_rec_open_u_wrt_t_rec : lngen.
Hint Rewrite close_u_wrt_t_rec_open_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_v_wrt_t_rec_open_v_wrt_t_rec :
forall v1 a1 n1,
  a1 `notin` tt_fv_v v1 ->
  close_v_wrt_t_rec n1 a1 (open_v_wrt_t_rec n1 (t_var_f a1) v1) = v1.
Proof. Admitted.

Hint Resolve close_v_wrt_t_rec_open_v_wrt_t_rec : lngen.
Hint Rewrite close_v_wrt_t_rec_open_v_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_u_rec_open_d_wrt_u_rec_close_e_wrt_u_rec_open_e_wrt_u_rec_close_u_wrt_u_rec_open_u_wrt_u_rec_close_v_wrt_u_rec_open_v_wrt_u_rec_mutual :
(forall d1 x1 n1,
  x1 `notin` e_fv_d d1 ->
  close_d_wrt_u_rec n1 x1 (open_d_wrt_u_rec n1 (u_var_f x1) d1) = d1) /\
(forall e1 x1 n1,
  x1 `notin` e_fv_e e1 ->
  close_e_wrt_u_rec n1 x1 (open_e_wrt_u_rec n1 (u_var_f x1) e1) = e1) /\
(forall u1 x1 n1,
  x1 `notin` e_fv_u u1 ->
  close_u_wrt_u_rec n1 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1) = u1) /\
(forall v1 x1 n1,
  x1 `notin` e_fv_v v1 ->
  close_v_wrt_u_rec n1 x1 (open_v_wrt_u_rec n1 (u_var_f x1) v1) = v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_u_rec_open_d_wrt_u_rec :
forall d1 x1 n1,
  x1 `notin` e_fv_d d1 ->
  close_d_wrt_u_rec n1 x1 (open_d_wrt_u_rec n1 (u_var_f x1) d1) = d1.
Proof. Admitted.

Hint Resolve close_d_wrt_u_rec_open_d_wrt_u_rec : lngen.
Hint Rewrite close_d_wrt_u_rec_open_d_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_u_rec_open_e_wrt_u_rec :
forall e1 x1 n1,
  x1 `notin` e_fv_e e1 ->
  close_e_wrt_u_rec n1 x1 (open_e_wrt_u_rec n1 (u_var_f x1) e1) = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_u_rec_open_e_wrt_u_rec : lngen.
Hint Rewrite close_e_wrt_u_rec_open_e_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_u_rec_open_u_wrt_u_rec :
forall u1 x1 n1,
  x1 `notin` e_fv_u u1 ->
  close_u_wrt_u_rec n1 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1) = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_u_rec_open_u_wrt_u_rec : lngen.
Hint Rewrite close_u_wrt_u_rec_open_u_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_v_wrt_u_rec_open_v_wrt_u_rec :
forall v1 x1 n1,
  x1 `notin` e_fv_v v1 ->
  close_v_wrt_u_rec n1 x1 (open_v_wrt_u_rec n1 (u_var_f x1) v1) = v1.
Proof. Admitted.

Hint Resolve close_v_wrt_u_rec_open_v_wrt_u_rec : lngen.
Hint Rewrite close_v_wrt_u_rec_open_v_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_t_wrt_t_open_t_wrt_t :
forall t1 a1,
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t a1 (open_t_wrt_t t1 (t_var_f a1)) = t1.
Proof. Admitted.

Hint Resolve close_t_wrt_t_open_t_wrt_t : lngen.
Hint Rewrite close_t_wrt_t_open_t_wrt_t using solve [auto] : lngen.

Lemma close_d_wrt_t_open_d_wrt_t :
forall d1 a1,
  a1 `notin` tt_fv_d d1 ->
  close_d_wrt_t a1 (open_d_wrt_t d1 (t_var_f a1)) = d1.
Proof. Admitted.

Hint Resolve close_d_wrt_t_open_d_wrt_t : lngen.
Hint Rewrite close_d_wrt_t_open_d_wrt_t using solve [auto] : lngen.

Lemma close_e_wrt_t_open_e_wrt_t :
forall e1 a1,
  a1 `notin` tt_fv_e e1 ->
  close_e_wrt_t a1 (open_e_wrt_t e1 (t_var_f a1)) = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_t_open_e_wrt_t : lngen.
Hint Rewrite close_e_wrt_t_open_e_wrt_t using solve [auto] : lngen.

Lemma close_u_wrt_t_open_u_wrt_t :
forall u1 a1,
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t a1 (open_u_wrt_t u1 (t_var_f a1)) = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_t_open_u_wrt_t : lngen.
Hint Rewrite close_u_wrt_t_open_u_wrt_t using solve [auto] : lngen.

Lemma close_v_wrt_t_open_v_wrt_t :
forall v1 a1,
  a1 `notin` tt_fv_v v1 ->
  close_v_wrt_t a1 (open_v_wrt_t v1 (t_var_f a1)) = v1.
Proof. Admitted.

Hint Resolve close_v_wrt_t_open_v_wrt_t : lngen.
Hint Rewrite close_v_wrt_t_open_v_wrt_t using solve [auto] : lngen.

Lemma close_d_wrt_u_open_d_wrt_u :
forall d1 x1,
  x1 `notin` e_fv_d d1 ->
  close_d_wrt_u x1 (open_d_wrt_u d1 (u_var_f x1)) = d1.
Proof. Admitted.

Hint Resolve close_d_wrt_u_open_d_wrt_u : lngen.
Hint Rewrite close_d_wrt_u_open_d_wrt_u using solve [auto] : lngen.

Lemma close_e_wrt_u_open_e_wrt_u :
forall e1 x1,
  x1 `notin` e_fv_e e1 ->
  close_e_wrt_u x1 (open_e_wrt_u e1 (u_var_f x1)) = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_u_open_e_wrt_u : lngen.
Hint Rewrite close_e_wrt_u_open_e_wrt_u using solve [auto] : lngen.

Lemma close_u_wrt_u_open_u_wrt_u :
forall u1 x1,
  x1 `notin` e_fv_u u1 ->
  close_u_wrt_u x1 (open_u_wrt_u u1 (u_var_f x1)) = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_u_open_u_wrt_u : lngen.
Hint Rewrite close_u_wrt_u_open_u_wrt_u using solve [auto] : lngen.

Lemma close_v_wrt_u_open_v_wrt_u :
forall v1 x1,
  x1 `notin` e_fv_v v1 ->
  close_v_wrt_u x1 (open_v_wrt_u v1 (u_var_f x1)) = v1.
Proof. Admitted.

Hint Resolve close_v_wrt_u_open_v_wrt_u : lngen.
Hint Rewrite close_v_wrt_u_open_v_wrt_u using solve [auto] : lngen.

(* begin hide *)

Lemma open_t_wrt_t_rec_close_t_wrt_t_rec_mutual :
(forall t1 a1 n1,
  open_t_wrt_t_rec n1 (t_var_f a1) (close_t_wrt_t_rec n1 a1 t1) = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_t_wrt_t_rec_close_t_wrt_t_rec :
forall t1 a1 n1,
  open_t_wrt_t_rec n1 (t_var_f a1) (close_t_wrt_t_rec n1 a1 t1) = t1.
Proof. Admitted.

Hint Resolve open_t_wrt_t_rec_close_t_wrt_t_rec : lngen.
Hint Rewrite open_t_wrt_t_rec_close_t_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_t_rec_close_d_wrt_t_rec_open_e_wrt_t_rec_close_e_wrt_t_rec_open_u_wrt_t_rec_close_u_wrt_t_rec_open_v_wrt_t_rec_close_v_wrt_t_rec_mutual :
(forall d1 a1 n1,
  open_d_wrt_t_rec n1 (t_var_f a1) (close_d_wrt_t_rec n1 a1 d1) = d1) /\
(forall e1 a1 n1,
  open_e_wrt_t_rec n1 (t_var_f a1) (close_e_wrt_t_rec n1 a1 e1) = e1) /\
(forall u1 a1 n1,
  open_u_wrt_t_rec n1 (t_var_f a1) (close_u_wrt_t_rec n1 a1 u1) = u1) /\
(forall v1 a1 n1,
  open_v_wrt_t_rec n1 (t_var_f a1) (close_v_wrt_t_rec n1 a1 v1) = v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_t_rec_close_d_wrt_t_rec :
forall d1 a1 n1,
  open_d_wrt_t_rec n1 (t_var_f a1) (close_d_wrt_t_rec n1 a1 d1) = d1.
Proof. Admitted.

Hint Resolve open_d_wrt_t_rec_close_d_wrt_t_rec : lngen.
Hint Rewrite open_d_wrt_t_rec_close_d_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_t_rec_close_e_wrt_t_rec :
forall e1 a1 n1,
  open_e_wrt_t_rec n1 (t_var_f a1) (close_e_wrt_t_rec n1 a1 e1) = e1.
Proof. Admitted.

Hint Resolve open_e_wrt_t_rec_close_e_wrt_t_rec : lngen.
Hint Rewrite open_e_wrt_t_rec_close_e_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_t_rec_close_u_wrt_t_rec :
forall u1 a1 n1,
  open_u_wrt_t_rec n1 (t_var_f a1) (close_u_wrt_t_rec n1 a1 u1) = u1.
Proof. Admitted.

Hint Resolve open_u_wrt_t_rec_close_u_wrt_t_rec : lngen.
Hint Rewrite open_u_wrt_t_rec_close_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_v_wrt_t_rec_close_v_wrt_t_rec :
forall v1 a1 n1,
  open_v_wrt_t_rec n1 (t_var_f a1) (close_v_wrt_t_rec n1 a1 v1) = v1.
Proof. Admitted.

Hint Resolve open_v_wrt_t_rec_close_v_wrt_t_rec : lngen.
Hint Rewrite open_v_wrt_t_rec_close_v_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_u_rec_close_d_wrt_u_rec_open_e_wrt_u_rec_close_e_wrt_u_rec_open_u_wrt_u_rec_close_u_wrt_u_rec_open_v_wrt_u_rec_close_v_wrt_u_rec_mutual :
(forall d1 x1 n1,
  open_d_wrt_u_rec n1 (u_var_f x1) (close_d_wrt_u_rec n1 x1 d1) = d1) /\
(forall e1 x1 n1,
  open_e_wrt_u_rec n1 (u_var_f x1) (close_e_wrt_u_rec n1 x1 e1) = e1) /\
(forall u1 x1 n1,
  open_u_wrt_u_rec n1 (u_var_f x1) (close_u_wrt_u_rec n1 x1 u1) = u1) /\
(forall v1 x1 n1,
  open_v_wrt_u_rec n1 (u_var_f x1) (close_v_wrt_u_rec n1 x1 v1) = v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_u_rec_close_d_wrt_u_rec :
forall d1 x1 n1,
  open_d_wrt_u_rec n1 (u_var_f x1) (close_d_wrt_u_rec n1 x1 d1) = d1.
Proof. Admitted.

Hint Resolve open_d_wrt_u_rec_close_d_wrt_u_rec : lngen.
Hint Rewrite open_d_wrt_u_rec_close_d_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_u_rec_close_e_wrt_u_rec :
forall e1 x1 n1,
  open_e_wrt_u_rec n1 (u_var_f x1) (close_e_wrt_u_rec n1 x1 e1) = e1.
Proof. Admitted.

Hint Resolve open_e_wrt_u_rec_close_e_wrt_u_rec : lngen.
Hint Rewrite open_e_wrt_u_rec_close_e_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_u_rec_close_u_wrt_u_rec :
forall u1 x1 n1,
  open_u_wrt_u_rec n1 (u_var_f x1) (close_u_wrt_u_rec n1 x1 u1) = u1.
Proof. Admitted.

Hint Resolve open_u_wrt_u_rec_close_u_wrt_u_rec : lngen.
Hint Rewrite open_u_wrt_u_rec_close_u_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_v_wrt_u_rec_close_v_wrt_u_rec :
forall v1 x1 n1,
  open_v_wrt_u_rec n1 (u_var_f x1) (close_v_wrt_u_rec n1 x1 v1) = v1.
Proof. Admitted.

Hint Resolve open_v_wrt_u_rec_close_v_wrt_u_rec : lngen.
Hint Rewrite open_v_wrt_u_rec_close_v_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_t_wrt_t_close_t_wrt_t :
forall t1 a1,
  open_t_wrt_t (close_t_wrt_t a1 t1) (t_var_f a1) = t1.
Proof. Admitted.

Hint Resolve open_t_wrt_t_close_t_wrt_t : lngen.
Hint Rewrite open_t_wrt_t_close_t_wrt_t using solve [auto] : lngen.

Lemma open_d_wrt_t_close_d_wrt_t :
forall d1 a1,
  open_d_wrt_t (close_d_wrt_t a1 d1) (t_var_f a1) = d1.
Proof. Admitted.

Hint Resolve open_d_wrt_t_close_d_wrt_t : lngen.
Hint Rewrite open_d_wrt_t_close_d_wrt_t using solve [auto] : lngen.

Lemma open_e_wrt_t_close_e_wrt_t :
forall e1 a1,
  open_e_wrt_t (close_e_wrt_t a1 e1) (t_var_f a1) = e1.
Proof. Admitted.

Hint Resolve open_e_wrt_t_close_e_wrt_t : lngen.
Hint Rewrite open_e_wrt_t_close_e_wrt_t using solve [auto] : lngen.

Lemma open_u_wrt_t_close_u_wrt_t :
forall u1 a1,
  open_u_wrt_t (close_u_wrt_t a1 u1) (t_var_f a1) = u1.
Proof. Admitted.

Hint Resolve open_u_wrt_t_close_u_wrt_t : lngen.
Hint Rewrite open_u_wrt_t_close_u_wrt_t using solve [auto] : lngen.

Lemma open_v_wrt_t_close_v_wrt_t :
forall v1 a1,
  open_v_wrt_t (close_v_wrt_t a1 v1) (t_var_f a1) = v1.
Proof. Admitted.

Hint Resolve open_v_wrt_t_close_v_wrt_t : lngen.
Hint Rewrite open_v_wrt_t_close_v_wrt_t using solve [auto] : lngen.

Lemma open_d_wrt_u_close_d_wrt_u :
forall d1 x1,
  open_d_wrt_u (close_d_wrt_u x1 d1) (u_var_f x1) = d1.
Proof. Admitted.

Hint Resolve open_d_wrt_u_close_d_wrt_u : lngen.
Hint Rewrite open_d_wrt_u_close_d_wrt_u using solve [auto] : lngen.

Lemma open_e_wrt_u_close_e_wrt_u :
forall e1 x1,
  open_e_wrt_u (close_e_wrt_u x1 e1) (u_var_f x1) = e1.
Proof. Admitted.

Hint Resolve open_e_wrt_u_close_e_wrt_u : lngen.
Hint Rewrite open_e_wrt_u_close_e_wrt_u using solve [auto] : lngen.

Lemma open_u_wrt_u_close_u_wrt_u :
forall u1 x1,
  open_u_wrt_u (close_u_wrt_u x1 u1) (u_var_f x1) = u1.
Proof. Admitted.

Hint Resolve open_u_wrt_u_close_u_wrt_u : lngen.
Hint Rewrite open_u_wrt_u_close_u_wrt_u using solve [auto] : lngen.

Lemma open_v_wrt_u_close_v_wrt_u :
forall v1 x1,
  open_v_wrt_u (close_v_wrt_u x1 v1) (u_var_f x1) = v1.
Proof. Admitted.

Hint Resolve open_v_wrt_u_close_v_wrt_u : lngen.
Hint Rewrite open_v_wrt_u_close_v_wrt_u using solve [auto] : lngen.

(* begin hide *)

Lemma open_t_wrt_t_rec_inj_mutual :
(forall t2 t1 a1 n1,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t_rec n1 (t_var_f a1) t2 = open_t_wrt_t_rec n1 (t_var_f a1) t1 ->
  t2 = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_t_wrt_t_rec_inj :
forall t2 t1 a1 n1,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t_rec n1 (t_var_f a1) t2 = open_t_wrt_t_rec n1 (t_var_f a1) t1 ->
  t2 = t1.
Proof. Admitted.

Hint Immediate open_t_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_t_rec_inj_open_e_wrt_t_rec_inj_open_u_wrt_t_rec_inj_open_v_wrt_t_rec_inj_mutual :
(forall d2 d1 a1 n1,
  a1 `notin` tt_fv_d d2 ->
  a1 `notin` tt_fv_d d1 ->
  open_d_wrt_t_rec n1 (t_var_f a1) d2 = open_d_wrt_t_rec n1 (t_var_f a1) d1 ->
  d2 = d1) /\
(forall e2 e1 a1 n1,
  a1 `notin` tt_fv_e e2 ->
  a1 `notin` tt_fv_e e1 ->
  open_e_wrt_t_rec n1 (t_var_f a1) e2 = open_e_wrt_t_rec n1 (t_var_f a1) e1 ->
  e2 = e1) /\
(forall u2 u1 a1 n1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 (t_var_f a1) u2 = open_u_wrt_t_rec n1 (t_var_f a1) u1 ->
  u2 = u1) /\
(forall v2 v1 a1 n1,
  a1 `notin` tt_fv_v v2 ->
  a1 `notin` tt_fv_v v1 ->
  open_v_wrt_t_rec n1 (t_var_f a1) v2 = open_v_wrt_t_rec n1 (t_var_f a1) v1 ->
  v2 = v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_t_rec_inj :
forall d2 d1 a1 n1,
  a1 `notin` tt_fv_d d2 ->
  a1 `notin` tt_fv_d d1 ->
  open_d_wrt_t_rec n1 (t_var_f a1) d2 = open_d_wrt_t_rec n1 (t_var_f a1) d1 ->
  d2 = d1.
Proof. Admitted.

Hint Immediate open_d_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_t_rec_inj :
forall e2 e1 a1 n1,
  a1 `notin` tt_fv_e e2 ->
  a1 `notin` tt_fv_e e1 ->
  open_e_wrt_t_rec n1 (t_var_f a1) e2 = open_e_wrt_t_rec n1 (t_var_f a1) e1 ->
  e2 = e1.
Proof. Admitted.

Hint Immediate open_e_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_t_rec_inj :
forall u2 u1 a1 n1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 (t_var_f a1) u2 = open_u_wrt_t_rec n1 (t_var_f a1) u1 ->
  u2 = u1.
Proof. Admitted.

Hint Immediate open_u_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_v_wrt_t_rec_inj :
forall v2 v1 a1 n1,
  a1 `notin` tt_fv_v v2 ->
  a1 `notin` tt_fv_v v1 ->
  open_v_wrt_t_rec n1 (t_var_f a1) v2 = open_v_wrt_t_rec n1 (t_var_f a1) v1 ->
  v2 = v1.
Proof. Admitted.

Hint Immediate open_v_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_u_rec_inj_open_e_wrt_u_rec_inj_open_u_wrt_u_rec_inj_open_v_wrt_u_rec_inj_mutual :
(forall d2 d1 x1 n1,
  x1 `notin` e_fv_d d2 ->
  x1 `notin` e_fv_d d1 ->
  open_d_wrt_u_rec n1 (u_var_f x1) d2 = open_d_wrt_u_rec n1 (u_var_f x1) d1 ->
  d2 = d1) /\
(forall e2 e1 x1 n1,
  x1 `notin` e_fv_e e2 ->
  x1 `notin` e_fv_e e1 ->
  open_e_wrt_u_rec n1 (u_var_f x1) e2 = open_e_wrt_u_rec n1 (u_var_f x1) e1 ->
  e2 = e1) /\
(forall u2 u1 x1 n1,
  x1 `notin` e_fv_u u2 ->
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u_rec n1 (u_var_f x1) u2 = open_u_wrt_u_rec n1 (u_var_f x1) u1 ->
  u2 = u1) /\
(forall v2 v1 x1 n1,
  x1 `notin` e_fv_v v2 ->
  x1 `notin` e_fv_v v1 ->
  open_v_wrt_u_rec n1 (u_var_f x1) v2 = open_v_wrt_u_rec n1 (u_var_f x1) v1 ->
  v2 = v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_u_rec_inj :
forall d2 d1 x1 n1,
  x1 `notin` e_fv_d d2 ->
  x1 `notin` e_fv_d d1 ->
  open_d_wrt_u_rec n1 (u_var_f x1) d2 = open_d_wrt_u_rec n1 (u_var_f x1) d1 ->
  d2 = d1.
Proof. Admitted.

Hint Immediate open_d_wrt_u_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_u_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` e_fv_e e2 ->
  x1 `notin` e_fv_e e1 ->
  open_e_wrt_u_rec n1 (u_var_f x1) e2 = open_e_wrt_u_rec n1 (u_var_f x1) e1 ->
  e2 = e1.
Proof. Admitted.

Hint Immediate open_e_wrt_u_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_u_rec_inj :
forall u2 u1 x1 n1,
  x1 `notin` e_fv_u u2 ->
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u_rec n1 (u_var_f x1) u2 = open_u_wrt_u_rec n1 (u_var_f x1) u1 ->
  u2 = u1.
Proof. Admitted.

Hint Immediate open_u_wrt_u_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_v_wrt_u_rec_inj :
forall v2 v1 x1 n1,
  x1 `notin` e_fv_v v2 ->
  x1 `notin` e_fv_v v1 ->
  open_v_wrt_u_rec n1 (u_var_f x1) v2 = open_v_wrt_u_rec n1 (u_var_f x1) v1 ->
  v2 = v1.
Proof. Admitted.

Hint Immediate open_v_wrt_u_rec_inj : lngen.

(* end hide *)

Lemma open_t_wrt_t_inj :
forall t2 t1 a1,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t t2 (t_var_f a1) = open_t_wrt_t t1 (t_var_f a1) ->
  t2 = t1.
Proof. Admitted.

Hint Immediate open_t_wrt_t_inj : lngen.

Lemma open_d_wrt_t_inj :
forall d2 d1 a1,
  a1 `notin` tt_fv_d d2 ->
  a1 `notin` tt_fv_d d1 ->
  open_d_wrt_t d2 (t_var_f a1) = open_d_wrt_t d1 (t_var_f a1) ->
  d2 = d1.
Proof. Admitted.

Hint Immediate open_d_wrt_t_inj : lngen.

Lemma open_e_wrt_t_inj :
forall e2 e1 a1,
  a1 `notin` tt_fv_e e2 ->
  a1 `notin` tt_fv_e e1 ->
  open_e_wrt_t e2 (t_var_f a1) = open_e_wrt_t e1 (t_var_f a1) ->
  e2 = e1.
Proof. Admitted.

Hint Immediate open_e_wrt_t_inj : lngen.

Lemma open_u_wrt_t_inj :
forall u2 u1 a1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t u2 (t_var_f a1) = open_u_wrt_t u1 (t_var_f a1) ->
  u2 = u1.
Proof. Admitted.

Hint Immediate open_u_wrt_t_inj : lngen.

Lemma open_v_wrt_t_inj :
forall v2 v1 a1,
  a1 `notin` tt_fv_v v2 ->
  a1 `notin` tt_fv_v v1 ->
  open_v_wrt_t v2 (t_var_f a1) = open_v_wrt_t v1 (t_var_f a1) ->
  v2 = v1.
Proof. Admitted.

Hint Immediate open_v_wrt_t_inj : lngen.

Lemma open_d_wrt_u_inj :
forall d2 d1 x1,
  x1 `notin` e_fv_d d2 ->
  x1 `notin` e_fv_d d1 ->
  open_d_wrt_u d2 (u_var_f x1) = open_d_wrt_u d1 (u_var_f x1) ->
  d2 = d1.
Proof. Admitted.

Hint Immediate open_d_wrt_u_inj : lngen.

Lemma open_e_wrt_u_inj :
forall e2 e1 x1,
  x1 `notin` e_fv_e e2 ->
  x1 `notin` e_fv_e e1 ->
  open_e_wrt_u e2 (u_var_f x1) = open_e_wrt_u e1 (u_var_f x1) ->
  e2 = e1.
Proof. Admitted.

Hint Immediate open_e_wrt_u_inj : lngen.

Lemma open_u_wrt_u_inj :
forall u2 u1 x1,
  x1 `notin` e_fv_u u2 ->
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u u2 (u_var_f x1) = open_u_wrt_u u1 (u_var_f x1) ->
  u2 = u1.
Proof. Admitted.

Hint Immediate open_u_wrt_u_inj : lngen.

Lemma open_v_wrt_u_inj :
forall v2 v1 x1,
  x1 `notin` e_fv_v v2 ->
  x1 `notin` e_fv_v v1 ->
  open_v_wrt_u v2 (u_var_f x1) = open_v_wrt_u v1 (u_var_f x1) ->
  v2 = v1.
Proof. Admitted.

Hint Immediate open_v_wrt_u_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_t_wrt_t_of_lc_t_mutual :
(forall t1,
  lc_t t1 ->
  degree_t_wrt_t 0 t1).
Proof. Admitted.

(* end hide *)

Lemma degree_t_wrt_t_of_lc_t :
forall t1,
  lc_t t1 ->
  degree_t_wrt_t 0 t1.
Proof. Admitted.

Hint Resolve degree_t_wrt_t_of_lc_t : lngen.

(* begin hide *)

Lemma degree_d_wrt_t_of_lc_d_degree_e_wrt_t_of_lc_e_degree_u_wrt_t_of_lc_u_degree_v_wrt_t_of_lc_v_mutual :
(forall d1,
  lc_d d1 ->
  degree_d_wrt_t 0 d1) /\
(forall e1,
  lc_e e1 ->
  degree_e_wrt_t 0 e1) /\
(forall u1,
  lc_u u1 ->
  degree_u_wrt_t 0 u1) /\
(forall v1,
  lc_v v1 ->
  degree_v_wrt_t 0 v1).
Proof. Admitted.

(* end hide *)

Lemma degree_d_wrt_t_of_lc_d :
forall d1,
  lc_d d1 ->
  degree_d_wrt_t 0 d1.
Proof. Admitted.

Hint Resolve degree_d_wrt_t_of_lc_d : lngen.

Lemma degree_e_wrt_t_of_lc_e :
forall e1,
  lc_e e1 ->
  degree_e_wrt_t 0 e1.
Proof. Admitted.

Hint Resolve degree_e_wrt_t_of_lc_e : lngen.

Lemma degree_u_wrt_t_of_lc_u :
forall u1,
  lc_u u1 ->
  degree_u_wrt_t 0 u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_t_of_lc_u : lngen.

Lemma degree_v_wrt_t_of_lc_v :
forall v1,
  lc_v v1 ->
  degree_v_wrt_t 0 v1.
Proof. Admitted.

Hint Resolve degree_v_wrt_t_of_lc_v : lngen.

(* begin hide *)

Lemma degree_d_wrt_u_of_lc_d_degree_e_wrt_u_of_lc_e_degree_u_wrt_u_of_lc_u_degree_v_wrt_u_of_lc_v_mutual :
(forall d1,
  lc_d d1 ->
  degree_d_wrt_u 0 d1) /\
(forall e1,
  lc_e e1 ->
  degree_e_wrt_u 0 e1) /\
(forall u1,
  lc_u u1 ->
  degree_u_wrt_u 0 u1) /\
(forall v1,
  lc_v v1 ->
  degree_v_wrt_u 0 v1).
Proof. Admitted.

(* end hide *)

Lemma degree_d_wrt_u_of_lc_d :
forall d1,
  lc_d d1 ->
  degree_d_wrt_u 0 d1.
Proof. Admitted.

Hint Resolve degree_d_wrt_u_of_lc_d : lngen.

Lemma degree_e_wrt_u_of_lc_e :
forall e1,
  lc_e e1 ->
  degree_e_wrt_u 0 e1.
Proof. Admitted.

Hint Resolve degree_e_wrt_u_of_lc_e : lngen.

Lemma degree_u_wrt_u_of_lc_u :
forall u1,
  lc_u u1 ->
  degree_u_wrt_u 0 u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_u_of_lc_u : lngen.

Lemma degree_v_wrt_u_of_lc_v :
forall v1,
  lc_v v1 ->
  degree_v_wrt_u 0 v1.
Proof. Admitted.

Hint Resolve degree_v_wrt_u_of_lc_v : lngen.

(* begin hide *)

Lemma lc_t_of_degree_size_mutual :
forall i1,
(forall t1,
  size_t t1 = i1 ->
  degree_t_wrt_t 0 t1 ->
  lc_t t1).
Proof. Admitted.

(* end hide *)

Lemma lc_t_of_degree :
forall t1,
  degree_t_wrt_t 0 t1 ->
  lc_t t1.
Proof. Admitted.

Hint Resolve lc_t_of_degree : lngen.

(* begin hide *)

Lemma lc_d_of_degree_lc_e_of_degree_lc_u_of_degree_lc_v_of_degree_size_mutual :
forall i1,
(forall d1,
  size_d d1 = i1 ->
  degree_d_wrt_t 0 d1 ->
  degree_d_wrt_u 0 d1 ->
  lc_d d1) /\
(forall e1,
  size_e e1 = i1 ->
  degree_e_wrt_t 0 e1 ->
  degree_e_wrt_u 0 e1 ->
  lc_e e1) /\
(forall u1,
  size_u u1 = i1 ->
  degree_u_wrt_t 0 u1 ->
  degree_u_wrt_u 0 u1 ->
  lc_u u1) /\
(forall v1,
  size_v v1 = i1 ->
  degree_v_wrt_t 0 v1 ->
  degree_v_wrt_u 0 v1 ->
  lc_v v1).
Proof. Admitted.

(* end hide *)

Lemma lc_d_of_degree :
forall d1,
  degree_d_wrt_t 0 d1 ->
  degree_d_wrt_u 0 d1 ->
  lc_d d1.
Proof. Admitted.

Hint Resolve lc_d_of_degree : lngen.

Lemma lc_e_of_degree :
forall e1,
  degree_e_wrt_t 0 e1 ->
  degree_e_wrt_u 0 e1 ->
  lc_e e1.
Proof. Admitted.

Hint Resolve lc_e_of_degree : lngen.

Lemma lc_u_of_degree :
forall u1,
  degree_u_wrt_t 0 u1 ->
  degree_u_wrt_u 0 u1 ->
  lc_u u1.
Proof. Admitted.

Hint Resolve lc_u_of_degree : lngen.

Lemma lc_v_of_degree :
forall v1,
  degree_v_wrt_t 0 v1 ->
  degree_v_wrt_u 0 v1 ->
  lc_v v1.
Proof. Admitted.

Hint Resolve lc_v_of_degree : lngen.

Ltac t_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_t_wrt_t_of_lc_t in J1; clear H
          end).

Ltac p_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac d_e_u_v_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_d_wrt_t_of_lc_d in J1;
              let J2 := fresh in pose proof H as J2; apply degree_d_wrt_u_of_lc_d in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_e_wrt_t_of_lc_e in J1;
              let J2 := fresh in pose proof H as J2; apply degree_e_wrt_u_of_lc_e in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_u_wrt_t_of_lc_u in J1;
              let J2 := fresh in pose proof H as J2; apply degree_u_wrt_u_of_lc_u in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_v_wrt_t_of_lc_v in J1;
              let J2 := fresh in pose proof H as J2; apply degree_v_wrt_u_of_lc_v in J2; clear H
          end).

Lemma lc_t_all_exists :
forall a1 t1,
  lc_t (open_t_wrt_t t1 (t_var_f a1)) ->
  lc_t (t_all t1).
Proof. Admitted.

Lemma lc_e_let_exists :
forall x1 d1 e1,
  lc_d d1 ->
  lc_e (open_e_wrt_u e1 (u_var_f x1)) ->
  lc_e (e_let d1 e1).
Proof. Admitted.

Lemma lc_u_lam_exists :
forall x1 t1 v1,
  lc_t t1 ->
  lc_v (open_v_wrt_u v1 (u_var_f x1)) ->
  lc_u (u_lam t1 v1).
Proof. Admitted.

Lemma lc_u_Lam_exists :
forall x1 t1 e1,
  lc_t t1 ->
  lc_e (open_e_wrt_u e1 (u_var_f x1)) ->
  lc_u (u_Lam t1 e1).
Proof. Admitted.

Hint Extern 1 (lc_t (t_all _)) =>
  let a1 := fresh in
  pick_fresh a1;
  apply (lc_t_all_exists a1).

Hint Extern 1 (lc_e (e_let _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_let_exists x1).

Hint Extern 1 (lc_u (u_lam _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_u_lam_exists x1).

Hint Extern 1 (lc_u (u_Lam _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_u_Lam_exists x1).

Lemma lc_body_t_wrt_t :
forall t1 t2,
  body_t_wrt_t t1 ->
  lc_t t2 ->
  lc_t (open_t_wrt_t t1 t2).
Proof. Admitted.

Hint Resolve lc_body_t_wrt_t : lngen.

Lemma lc_body_d_wrt_t :
forall d1 t1,
  body_d_wrt_t d1 ->
  lc_t t1 ->
  lc_d (open_d_wrt_t d1 t1).
Proof. Admitted.

Hint Resolve lc_body_d_wrt_t : lngen.

Lemma lc_body_e_wrt_t :
forall e1 t1,
  body_e_wrt_t e1 ->
  lc_t t1 ->
  lc_e (open_e_wrt_t e1 t1).
Proof. Admitted.

Hint Resolve lc_body_e_wrt_t : lngen.

Lemma lc_body_u_wrt_t :
forall u1 t1,
  body_u_wrt_t u1 ->
  lc_t t1 ->
  lc_u (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve lc_body_u_wrt_t : lngen.

Lemma lc_body_v_wrt_t :
forall v1 t1,
  body_v_wrt_t v1 ->
  lc_t t1 ->
  lc_v (open_v_wrt_t v1 t1).
Proof. Admitted.

Hint Resolve lc_body_v_wrt_t : lngen.

Lemma lc_body_d_wrt_u :
forall d1 u1,
  body_d_wrt_u d1 ->
  lc_u u1 ->
  lc_d (open_d_wrt_u d1 u1).
Proof. Admitted.

Hint Resolve lc_body_d_wrt_u : lngen.

Lemma lc_body_e_wrt_u :
forall e1 u1,
  body_e_wrt_u e1 ->
  lc_u u1 ->
  lc_e (open_e_wrt_u e1 u1).
Proof. Admitted.

Hint Resolve lc_body_e_wrt_u : lngen.

Lemma lc_body_u_wrt_u :
forall u1 u2,
  body_u_wrt_u u1 ->
  lc_u u2 ->
  lc_u (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve lc_body_u_wrt_u : lngen.

Lemma lc_body_v_wrt_u :
forall v1 u1,
  body_v_wrt_u v1 ->
  lc_u u1 ->
  lc_v (open_v_wrt_u v1 u1).
Proof. Admitted.

Hint Resolve lc_body_v_wrt_u : lngen.

Lemma lc_body_t_all_1 :
forall t1,
  lc_t (t_all t1) ->
  body_t_wrt_t t1.
Proof. Admitted.

Hint Resolve lc_body_t_all_1 : lngen.

Lemma lc_body_e_let_2 :
forall d1 e1,
  lc_e (e_let d1 e1) ->
  body_e_wrt_u e1.
Proof. Admitted.

Hint Resolve lc_body_e_let_2 : lngen.

Lemma lc_body_u_lam_2 :
forall t1 v1,
  lc_u (u_lam t1 v1) ->
  body_v_wrt_u v1.
Proof. Admitted.

Hint Resolve lc_body_u_lam_2 : lngen.

Lemma lc_body_u_Lam_2 :
forall t1 e1,
  lc_u (u_Lam t1 e1) ->
  body_e_wrt_u e1.
Proof. Admitted.

Hint Resolve lc_body_u_Lam_2 : lngen.

(* begin hide *)

Lemma lc_t_unique_mutual :
(forall t1 (proof2 proof3 : lc_t t1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_t_unique :
forall t1 (proof2 proof3 : lc_t t1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_t_unique : lngen.

(* begin hide *)

Lemma lc_d_unique_lc_e_unique_lc_u_unique_lc_v_unique_mutual :
(forall d1 (proof2 proof3 : lc_d d1), proof2 = proof3) /\
(forall e1 (proof2 proof3 : lc_e e1), proof2 = proof3) /\
(forall u1 (proof2 proof3 : lc_u u1), proof2 = proof3) /\
(forall v1 (proof2 proof3 : lc_v v1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_d_unique :
forall d1 (proof2 proof3 : lc_d d1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_d_unique : lngen.

Lemma lc_e_unique :
forall e1 (proof2 proof3 : lc_e e1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_e_unique : lngen.

Lemma lc_u_unique :
forall u1 (proof2 proof3 : lc_u u1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_u_unique : lngen.

Lemma lc_v_unique :
forall v1 (proof2 proof3 : lc_v v1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_v_unique : lngen.

(* begin hide *)

Lemma lc_t_of_lc_set_t_mutual :
(forall t1, lc_set_t t1 -> lc_t t1).
Proof. Admitted.

(* end hide *)

Lemma lc_t_of_lc_set_t :
forall t1, lc_set_t t1 -> lc_t t1.
Proof. Admitted.

Hint Resolve lc_t_of_lc_set_t : lngen.

(* begin hide *)

Lemma lc_d_of_lc_set_d_lc_e_of_lc_set_e_lc_u_of_lc_set_u_lc_v_of_lc_set_v_mutual :
(forall d1, lc_set_d d1 -> lc_d d1) /\
(forall e1, lc_set_e e1 -> lc_e e1) /\
(forall u1, lc_set_u u1 -> lc_u u1) /\
(forall v1, lc_set_v v1 -> lc_v v1).
Proof. Admitted.

(* end hide *)

Lemma lc_d_of_lc_set_d :
forall d1, lc_set_d d1 -> lc_d d1.
Proof. Admitted.

Hint Resolve lc_d_of_lc_set_d : lngen.

Lemma lc_e_of_lc_set_e :
forall e1, lc_set_e e1 -> lc_e e1.
Proof. Admitted.

Hint Resolve lc_e_of_lc_set_e : lngen.

Lemma lc_u_of_lc_set_u :
forall u1, lc_set_u u1 -> lc_u u1.
Proof. Admitted.

Hint Resolve lc_u_of_lc_set_u : lngen.

Lemma lc_v_of_lc_set_v :
forall v1, lc_set_v v1 -> lc_v v1.
Proof. Admitted.

Hint Resolve lc_v_of_lc_set_v : lngen.

(* begin hide *)

Lemma lc_set_t_of_lc_t_size_mutual :
forall i1,
(forall t1,
  size_t t1 = i1 ->
  lc_t t1 ->
  lc_set_t t1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_t_of_lc_t :
forall t1,
  lc_t t1 ->
  lc_set_t t1.
Proof. Admitted.

Hint Resolve lc_set_t_of_lc_t : lngen.

(* begin hide *)

Lemma lc_set_d_of_lc_d_lc_set_e_of_lc_e_lc_set_u_of_lc_u_lc_set_v_of_lc_v_size_mutual :
forall i1,
(forall d1,
  size_d d1 = i1 ->
  lc_d d1 ->
  lc_set_d d1) *
(forall e1,
  size_e e1 = i1 ->
  lc_e e1 ->
  lc_set_e e1) *
(forall u1,
  size_u u1 = i1 ->
  lc_u u1 ->
  lc_set_u u1) *
(forall v1,
  size_v v1 = i1 ->
  lc_v v1 ->
  lc_set_v v1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_d_of_lc_d :
forall d1,
  lc_d d1 ->
  lc_set_d d1.
Proof. Admitted.

Hint Resolve lc_set_d_of_lc_d : lngen.

Lemma lc_set_e_of_lc_e :
forall e1,
  lc_e e1 ->
  lc_set_e e1.
Proof. Admitted.

Hint Resolve lc_set_e_of_lc_e : lngen.

Lemma lc_set_u_of_lc_u :
forall u1,
  lc_u u1 ->
  lc_set_u u1.
Proof. Admitted.

Hint Resolve lc_set_u_of_lc_u : lngen.

Lemma lc_set_v_of_lc_v :
forall v1,
  lc_v v1 ->
  lc_set_v v1.
Proof. Admitted.

Hint Resolve lc_set_v_of_lc_v : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_t_wrt_t_rec_degree_t_wrt_t_mutual :
(forall t1 a1 n1,
  degree_t_wrt_t n1 t1 ->
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t_rec n1 a1 t1 = t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_t_wrt_t_rec_degree_t_wrt_t :
forall t1 a1 n1,
  degree_t_wrt_t n1 t1 ->
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t_rec n1 a1 t1 = t1.
Proof. Admitted.

Hint Resolve close_t_wrt_t_rec_degree_t_wrt_t : lngen.
Hint Rewrite close_t_wrt_t_rec_degree_t_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_t_rec_degree_d_wrt_t_close_e_wrt_t_rec_degree_e_wrt_t_close_u_wrt_t_rec_degree_u_wrt_t_close_v_wrt_t_rec_degree_v_wrt_t_mutual :
(forall d1 a1 n1,
  degree_d_wrt_t n1 d1 ->
  a1 `notin` tt_fv_d d1 ->
  close_d_wrt_t_rec n1 a1 d1 = d1) /\
(forall e1 a1 n1,
  degree_e_wrt_t n1 e1 ->
  a1 `notin` tt_fv_e e1 ->
  close_e_wrt_t_rec n1 a1 e1 = e1) /\
(forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t_rec n1 a1 u1 = u1) /\
(forall v1 a1 n1,
  degree_v_wrt_t n1 v1 ->
  a1 `notin` tt_fv_v v1 ->
  close_v_wrt_t_rec n1 a1 v1 = v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_t_rec_degree_d_wrt_t :
forall d1 a1 n1,
  degree_d_wrt_t n1 d1 ->
  a1 `notin` tt_fv_d d1 ->
  close_d_wrt_t_rec n1 a1 d1 = d1.
Proof. Admitted.

Hint Resolve close_d_wrt_t_rec_degree_d_wrt_t : lngen.
Hint Rewrite close_d_wrt_t_rec_degree_d_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_t_rec_degree_e_wrt_t :
forall e1 a1 n1,
  degree_e_wrt_t n1 e1 ->
  a1 `notin` tt_fv_e e1 ->
  close_e_wrt_t_rec n1 a1 e1 = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_t_rec_degree_e_wrt_t : lngen.
Hint Rewrite close_e_wrt_t_rec_degree_e_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_t_rec_degree_u_wrt_t :
forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t_rec n1 a1 u1 = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_t_rec_degree_u_wrt_t : lngen.
Hint Rewrite close_u_wrt_t_rec_degree_u_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_v_wrt_t_rec_degree_v_wrt_t :
forall v1 a1 n1,
  degree_v_wrt_t n1 v1 ->
  a1 `notin` tt_fv_v v1 ->
  close_v_wrt_t_rec n1 a1 v1 = v1.
Proof. Admitted.

Hint Resolve close_v_wrt_t_rec_degree_v_wrt_t : lngen.
Hint Rewrite close_v_wrt_t_rec_degree_v_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_u_rec_degree_d_wrt_u_close_e_wrt_u_rec_degree_e_wrt_u_close_u_wrt_u_rec_degree_u_wrt_u_close_v_wrt_u_rec_degree_v_wrt_u_mutual :
(forall d1 x1 n1,
  degree_d_wrt_u n1 d1 ->
  x1 `notin` e_fv_d d1 ->
  close_d_wrt_u_rec n1 x1 d1 = d1) /\
(forall e1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  x1 `notin` e_fv_e e1 ->
  close_e_wrt_u_rec n1 x1 e1 = e1) /\
(forall u1 x1 n1,
  degree_u_wrt_u n1 u1 ->
  x1 `notin` e_fv_u u1 ->
  close_u_wrt_u_rec n1 x1 u1 = u1) /\
(forall v1 x1 n1,
  degree_v_wrt_u n1 v1 ->
  x1 `notin` e_fv_v v1 ->
  close_v_wrt_u_rec n1 x1 v1 = v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_d_wrt_u_rec_degree_d_wrt_u :
forall d1 x1 n1,
  degree_d_wrt_u n1 d1 ->
  x1 `notin` e_fv_d d1 ->
  close_d_wrt_u_rec n1 x1 d1 = d1.
Proof. Admitted.

Hint Resolve close_d_wrt_u_rec_degree_d_wrt_u : lngen.
Hint Rewrite close_d_wrt_u_rec_degree_d_wrt_u using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_u_rec_degree_e_wrt_u :
forall e1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  x1 `notin` e_fv_e e1 ->
  close_e_wrt_u_rec n1 x1 e1 = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_u_rec_degree_e_wrt_u : lngen.
Hint Rewrite close_e_wrt_u_rec_degree_e_wrt_u using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_u_rec_degree_u_wrt_u :
forall u1 x1 n1,
  degree_u_wrt_u n1 u1 ->
  x1 `notin` e_fv_u u1 ->
  close_u_wrt_u_rec n1 x1 u1 = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_u_rec_degree_u_wrt_u : lngen.
Hint Rewrite close_u_wrt_u_rec_degree_u_wrt_u using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_v_wrt_u_rec_degree_v_wrt_u :
forall v1 x1 n1,
  degree_v_wrt_u n1 v1 ->
  x1 `notin` e_fv_v v1 ->
  close_v_wrt_u_rec n1 x1 v1 = v1.
Proof. Admitted.

Hint Resolve close_v_wrt_u_rec_degree_v_wrt_u : lngen.
Hint Rewrite close_v_wrt_u_rec_degree_v_wrt_u using solve [auto] : lngen.

(* end hide *)

Lemma close_t_wrt_t_lc_t :
forall t1 a1,
  lc_t t1 ->
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t a1 t1 = t1.
Proof. Admitted.

Hint Resolve close_t_wrt_t_lc_t : lngen.
Hint Rewrite close_t_wrt_t_lc_t using solve [auto] : lngen.

Lemma close_d_wrt_t_lc_d :
forall d1 a1,
  lc_d d1 ->
  a1 `notin` tt_fv_d d1 ->
  close_d_wrt_t a1 d1 = d1.
Proof. Admitted.

Hint Resolve close_d_wrt_t_lc_d : lngen.
Hint Rewrite close_d_wrt_t_lc_d using solve [auto] : lngen.

Lemma close_e_wrt_t_lc_e :
forall e1 a1,
  lc_e e1 ->
  a1 `notin` tt_fv_e e1 ->
  close_e_wrt_t a1 e1 = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_t_lc_e : lngen.
Hint Rewrite close_e_wrt_t_lc_e using solve [auto] : lngen.

Lemma close_u_wrt_t_lc_u :
forall u1 a1,
  lc_u u1 ->
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t a1 u1 = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_t_lc_u : lngen.
Hint Rewrite close_u_wrt_t_lc_u using solve [auto] : lngen.

Lemma close_v_wrt_t_lc_v :
forall v1 a1,
  lc_v v1 ->
  a1 `notin` tt_fv_v v1 ->
  close_v_wrt_t a1 v1 = v1.
Proof. Admitted.

Hint Resolve close_v_wrt_t_lc_v : lngen.
Hint Rewrite close_v_wrt_t_lc_v using solve [auto] : lngen.

Lemma close_d_wrt_u_lc_d :
forall d1 x1,
  lc_d d1 ->
  x1 `notin` e_fv_d d1 ->
  close_d_wrt_u x1 d1 = d1.
Proof. Admitted.

Hint Resolve close_d_wrt_u_lc_d : lngen.
Hint Rewrite close_d_wrt_u_lc_d using solve [auto] : lngen.

Lemma close_e_wrt_u_lc_e :
forall e1 x1,
  lc_e e1 ->
  x1 `notin` e_fv_e e1 ->
  close_e_wrt_u x1 e1 = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_u_lc_e : lngen.
Hint Rewrite close_e_wrt_u_lc_e using solve [auto] : lngen.

Lemma close_u_wrt_u_lc_u :
forall u1 x1,
  lc_u u1 ->
  x1 `notin` e_fv_u u1 ->
  close_u_wrt_u x1 u1 = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_u_lc_u : lngen.
Hint Rewrite close_u_wrt_u_lc_u using solve [auto] : lngen.

Lemma close_v_wrt_u_lc_v :
forall v1 x1,
  lc_v v1 ->
  x1 `notin` e_fv_v v1 ->
  close_v_wrt_u x1 v1 = v1.
Proof. Admitted.

Hint Resolve close_v_wrt_u_lc_v : lngen.
Hint Rewrite close_v_wrt_u_lc_v using solve [auto] : lngen.

(* begin hide *)

Lemma open_t_wrt_t_rec_degree_t_wrt_t_mutual :
(forall t2 t1 n1,
  degree_t_wrt_t n1 t2 ->
  open_t_wrt_t_rec n1 t1 t2 = t2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_t_wrt_t_rec_degree_t_wrt_t :
forall t2 t1 n1,
  degree_t_wrt_t n1 t2 ->
  open_t_wrt_t_rec n1 t1 t2 = t2.
Proof. Admitted.

Hint Resolve open_t_wrt_t_rec_degree_t_wrt_t : lngen.
Hint Rewrite open_t_wrt_t_rec_degree_t_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_t_rec_degree_d_wrt_t_open_e_wrt_t_rec_degree_e_wrt_t_open_u_wrt_t_rec_degree_u_wrt_t_open_v_wrt_t_rec_degree_v_wrt_t_mutual :
(forall d1 t1 n1,
  degree_d_wrt_t n1 d1 ->
  open_d_wrt_t_rec n1 t1 d1 = d1) /\
(forall e1 t1 n1,
  degree_e_wrt_t n1 e1 ->
  open_e_wrt_t_rec n1 t1 e1 = e1) /\
(forall u1 t1 n1,
  degree_u_wrt_t n1 u1 ->
  open_u_wrt_t_rec n1 t1 u1 = u1) /\
(forall v1 t1 n1,
  degree_v_wrt_t n1 v1 ->
  open_v_wrt_t_rec n1 t1 v1 = v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_t_rec_degree_d_wrt_t :
forall d1 t1 n1,
  degree_d_wrt_t n1 d1 ->
  open_d_wrt_t_rec n1 t1 d1 = d1.
Proof. Admitted.

Hint Resolve open_d_wrt_t_rec_degree_d_wrt_t : lngen.
Hint Rewrite open_d_wrt_t_rec_degree_d_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_t_rec_degree_e_wrt_t :
forall e1 t1 n1,
  degree_e_wrt_t n1 e1 ->
  open_e_wrt_t_rec n1 t1 e1 = e1.
Proof. Admitted.

Hint Resolve open_e_wrt_t_rec_degree_e_wrt_t : lngen.
Hint Rewrite open_e_wrt_t_rec_degree_e_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_t_rec_degree_u_wrt_t :
forall u1 t1 n1,
  degree_u_wrt_t n1 u1 ->
  open_u_wrt_t_rec n1 t1 u1 = u1.
Proof. Admitted.

Hint Resolve open_u_wrt_t_rec_degree_u_wrt_t : lngen.
Hint Rewrite open_u_wrt_t_rec_degree_u_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_v_wrt_t_rec_degree_v_wrt_t :
forall v1 t1 n1,
  degree_v_wrt_t n1 v1 ->
  open_v_wrt_t_rec n1 t1 v1 = v1.
Proof. Admitted.

Hint Resolve open_v_wrt_t_rec_degree_v_wrt_t : lngen.
Hint Rewrite open_v_wrt_t_rec_degree_v_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_u_rec_degree_d_wrt_u_open_e_wrt_u_rec_degree_e_wrt_u_open_u_wrt_u_rec_degree_u_wrt_u_open_v_wrt_u_rec_degree_v_wrt_u_mutual :
(forall d1 u1 n1,
  degree_d_wrt_u n1 d1 ->
  open_d_wrt_u_rec n1 u1 d1 = d1) /\
(forall e1 u1 n1,
  degree_e_wrt_u n1 e1 ->
  open_e_wrt_u_rec n1 u1 e1 = e1) /\
(forall u2 u1 n1,
  degree_u_wrt_u n1 u2 ->
  open_u_wrt_u_rec n1 u1 u2 = u2) /\
(forall v1 u1 n1,
  degree_v_wrt_u n1 v1 ->
  open_v_wrt_u_rec n1 u1 v1 = v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_d_wrt_u_rec_degree_d_wrt_u :
forall d1 u1 n1,
  degree_d_wrt_u n1 d1 ->
  open_d_wrt_u_rec n1 u1 d1 = d1.
Proof. Admitted.

Hint Resolve open_d_wrt_u_rec_degree_d_wrt_u : lngen.
Hint Rewrite open_d_wrt_u_rec_degree_d_wrt_u using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_u_rec_degree_e_wrt_u :
forall e1 u1 n1,
  degree_e_wrt_u n1 e1 ->
  open_e_wrt_u_rec n1 u1 e1 = e1.
Proof. Admitted.

Hint Resolve open_e_wrt_u_rec_degree_e_wrt_u : lngen.
Hint Rewrite open_e_wrt_u_rec_degree_e_wrt_u using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_u_rec_degree_u_wrt_u :
forall u2 u1 n1,
  degree_u_wrt_u n1 u2 ->
  open_u_wrt_u_rec n1 u1 u2 = u2.
Proof. Admitted.

Hint Resolve open_u_wrt_u_rec_degree_u_wrt_u : lngen.
Hint Rewrite open_u_wrt_u_rec_degree_u_wrt_u using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_v_wrt_u_rec_degree_v_wrt_u :
forall v1 u1 n1,
  degree_v_wrt_u n1 v1 ->
  open_v_wrt_u_rec n1 u1 v1 = v1.
Proof. Admitted.

Hint Resolve open_v_wrt_u_rec_degree_v_wrt_u : lngen.
Hint Rewrite open_v_wrt_u_rec_degree_v_wrt_u using solve [auto] : lngen.

(* end hide *)

Lemma open_t_wrt_t_lc_t :
forall t2 t1,
  lc_t t2 ->
  open_t_wrt_t t2 t1 = t2.
Proof. Admitted.

Hint Resolve open_t_wrt_t_lc_t : lngen.
Hint Rewrite open_t_wrt_t_lc_t using solve [auto] : lngen.

Lemma open_d_wrt_t_lc_d :
forall d1 t1,
  lc_d d1 ->
  open_d_wrt_t d1 t1 = d1.
Proof. Admitted.

Hint Resolve open_d_wrt_t_lc_d : lngen.
Hint Rewrite open_d_wrt_t_lc_d using solve [auto] : lngen.

Lemma open_e_wrt_t_lc_e :
forall e1 t1,
  lc_e e1 ->
  open_e_wrt_t e1 t1 = e1.
Proof. Admitted.

Hint Resolve open_e_wrt_t_lc_e : lngen.
Hint Rewrite open_e_wrt_t_lc_e using solve [auto] : lngen.

Lemma open_u_wrt_t_lc_u :
forall u1 t1,
  lc_u u1 ->
  open_u_wrt_t u1 t1 = u1.
Proof. Admitted.

Hint Resolve open_u_wrt_t_lc_u : lngen.
Hint Rewrite open_u_wrt_t_lc_u using solve [auto] : lngen.

Lemma open_v_wrt_t_lc_v :
forall v1 t1,
  lc_v v1 ->
  open_v_wrt_t v1 t1 = v1.
Proof. Admitted.

Hint Resolve open_v_wrt_t_lc_v : lngen.
Hint Rewrite open_v_wrt_t_lc_v using solve [auto] : lngen.

Lemma open_d_wrt_u_lc_d :
forall d1 u1,
  lc_d d1 ->
  open_d_wrt_u d1 u1 = d1.
Proof. Admitted.

Hint Resolve open_d_wrt_u_lc_d : lngen.
Hint Rewrite open_d_wrt_u_lc_d using solve [auto] : lngen.

Lemma open_e_wrt_u_lc_e :
forall e1 u1,
  lc_e e1 ->
  open_e_wrt_u e1 u1 = e1.
Proof. Admitted.

Hint Resolve open_e_wrt_u_lc_e : lngen.
Hint Rewrite open_e_wrt_u_lc_e using solve [auto] : lngen.

Lemma open_u_wrt_u_lc_u :
forall u2 u1,
  lc_u u2 ->
  open_u_wrt_u u2 u1 = u2.
Proof. Admitted.

Hint Resolve open_u_wrt_u_lc_u : lngen.
Hint Rewrite open_u_wrt_u_lc_u using solve [auto] : lngen.

Lemma open_v_wrt_u_lc_v :
forall v1 u1,
  lc_v v1 ->
  open_v_wrt_u v1 u1 = v1.
Proof. Admitted.

Hint Resolve open_v_wrt_u_lc_v : lngen.
Hint Rewrite open_v_wrt_u_lc_v using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma tt_fv_t_close_t_wrt_t_rec_mutual :
(forall t1 a1 n1,
  tt_fv_t (close_t_wrt_t_rec n1 a1 t1) [=] remove a1 (tt_fv_t t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_t_close_t_wrt_t_rec :
forall t1 a1 n1,
  tt_fv_t (close_t_wrt_t_rec n1 a1 t1) [=] remove a1 (tt_fv_t t1).
Proof. Admitted.

Hint Resolve tt_fv_t_close_t_wrt_t_rec : lngen.
Hint Rewrite tt_fv_t_close_t_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_close_d_wrt_t_rec_tt_fv_e_close_e_wrt_t_rec_tt_fv_u_close_u_wrt_t_rec_tt_fv_v_close_v_wrt_t_rec_mutual :
(forall d1 a1 n1,
  tt_fv_d (close_d_wrt_t_rec n1 a1 d1) [=] remove a1 (tt_fv_d d1)) /\
(forall e1 a1 n1,
  tt_fv_e (close_e_wrt_t_rec n1 a1 e1) [=] remove a1 (tt_fv_e e1)) /\
(forall u1 a1 n1,
  tt_fv_u (close_u_wrt_t_rec n1 a1 u1) [=] remove a1 (tt_fv_u u1)) /\
(forall v1 a1 n1,
  tt_fv_v (close_v_wrt_t_rec n1 a1 v1) [=] remove a1 (tt_fv_v v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_close_d_wrt_t_rec :
forall d1 a1 n1,
  tt_fv_d (close_d_wrt_t_rec n1 a1 d1) [=] remove a1 (tt_fv_d d1).
Proof. Admitted.

Hint Resolve tt_fv_d_close_d_wrt_t_rec : lngen.
Hint Rewrite tt_fv_d_close_d_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_e_close_e_wrt_t_rec :
forall e1 a1 n1,
  tt_fv_e (close_e_wrt_t_rec n1 a1 e1) [=] remove a1 (tt_fv_e e1).
Proof. Admitted.

Hint Resolve tt_fv_e_close_e_wrt_t_rec : lngen.
Hint Rewrite tt_fv_e_close_e_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_close_u_wrt_t_rec :
forall u1 a1 n1,
  tt_fv_u (close_u_wrt_t_rec n1 a1 u1) [=] remove a1 (tt_fv_u u1).
Proof. Admitted.

Hint Resolve tt_fv_u_close_u_wrt_t_rec : lngen.
Hint Rewrite tt_fv_u_close_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_v_close_v_wrt_t_rec :
forall v1 a1 n1,
  tt_fv_v (close_v_wrt_t_rec n1 a1 v1) [=] remove a1 (tt_fv_v v1).
Proof. Admitted.

Hint Resolve tt_fv_v_close_v_wrt_t_rec : lngen.
Hint Rewrite tt_fv_v_close_v_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_close_d_wrt_u_rec_tt_fv_e_close_e_wrt_u_rec_tt_fv_u_close_u_wrt_u_rec_tt_fv_v_close_v_wrt_u_rec_mutual :
(forall d1 x1 n1,
  tt_fv_d (close_d_wrt_u_rec n1 x1 d1) [=] tt_fv_d d1) /\
(forall e1 x1 n1,
  tt_fv_e (close_e_wrt_u_rec n1 x1 e1) [=] tt_fv_e e1) /\
(forall u1 x1 n1,
  tt_fv_u (close_u_wrt_u_rec n1 x1 u1) [=] tt_fv_u u1) /\
(forall v1 x1 n1,
  tt_fv_v (close_v_wrt_u_rec n1 x1 v1) [=] tt_fv_v v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_close_d_wrt_u_rec :
forall d1 x1 n1,
  tt_fv_d (close_d_wrt_u_rec n1 x1 d1) [=] tt_fv_d d1.
Proof. Admitted.

Hint Resolve tt_fv_d_close_d_wrt_u_rec : lngen.
Hint Rewrite tt_fv_d_close_d_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_e_close_e_wrt_u_rec :
forall e1 x1 n1,
  tt_fv_e (close_e_wrt_u_rec n1 x1 e1) [=] tt_fv_e e1.
Proof. Admitted.

Hint Resolve tt_fv_e_close_e_wrt_u_rec : lngen.
Hint Rewrite tt_fv_e_close_e_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_close_u_wrt_u_rec :
forall u1 x1 n1,
  tt_fv_u (close_u_wrt_u_rec n1 x1 u1) [=] tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_close_u_wrt_u_rec : lngen.
Hint Rewrite tt_fv_u_close_u_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_v_close_v_wrt_u_rec :
forall v1 x1 n1,
  tt_fv_v (close_v_wrt_u_rec n1 x1 v1) [=] tt_fv_v v1.
Proof. Admitted.

Hint Resolve tt_fv_v_close_v_wrt_u_rec : lngen.
Hint Rewrite tt_fv_v_close_v_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_close_d_wrt_t_rec_e_fv_e_close_e_wrt_t_rec_e_fv_u_close_u_wrt_t_rec_e_fv_v_close_v_wrt_t_rec_mutual :
(forall d1 a1 n1,
  e_fv_d (close_d_wrt_t_rec n1 a1 d1) [=] e_fv_d d1) /\
(forall e1 a1 n1,
  e_fv_e (close_e_wrt_t_rec n1 a1 e1) [=] e_fv_e e1) /\
(forall u1 a1 n1,
  e_fv_u (close_u_wrt_t_rec n1 a1 u1) [=] e_fv_u u1) /\
(forall v1 a1 n1,
  e_fv_v (close_v_wrt_t_rec n1 a1 v1) [=] e_fv_v v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_close_d_wrt_t_rec :
forall d1 a1 n1,
  e_fv_d (close_d_wrt_t_rec n1 a1 d1) [=] e_fv_d d1.
Proof. Admitted.

Hint Resolve e_fv_d_close_d_wrt_t_rec : lngen.
Hint Rewrite e_fv_d_close_d_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_e_close_e_wrt_t_rec :
forall e1 a1 n1,
  e_fv_e (close_e_wrt_t_rec n1 a1 e1) [=] e_fv_e e1.
Proof. Admitted.

Hint Resolve e_fv_e_close_e_wrt_t_rec : lngen.
Hint Rewrite e_fv_e_close_e_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_close_u_wrt_t_rec :
forall u1 a1 n1,
  e_fv_u (close_u_wrt_t_rec n1 a1 u1) [=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_close_u_wrt_t_rec : lngen.
Hint Rewrite e_fv_u_close_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_v_close_v_wrt_t_rec :
forall v1 a1 n1,
  e_fv_v (close_v_wrt_t_rec n1 a1 v1) [=] e_fv_v v1.
Proof. Admitted.

Hint Resolve e_fv_v_close_v_wrt_t_rec : lngen.
Hint Rewrite e_fv_v_close_v_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_close_d_wrt_u_rec_e_fv_e_close_e_wrt_u_rec_e_fv_u_close_u_wrt_u_rec_e_fv_v_close_v_wrt_u_rec_mutual :
(forall d1 x1 n1,
  e_fv_d (close_d_wrt_u_rec n1 x1 d1) [=] remove x1 (e_fv_d d1)) /\
(forall e1 x1 n1,
  e_fv_e (close_e_wrt_u_rec n1 x1 e1) [=] remove x1 (e_fv_e e1)) /\
(forall u1 x1 n1,
  e_fv_u (close_u_wrt_u_rec n1 x1 u1) [=] remove x1 (e_fv_u u1)) /\
(forall v1 x1 n1,
  e_fv_v (close_v_wrt_u_rec n1 x1 v1) [=] remove x1 (e_fv_v v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_close_d_wrt_u_rec :
forall d1 x1 n1,
  e_fv_d (close_d_wrt_u_rec n1 x1 d1) [=] remove x1 (e_fv_d d1).
Proof. Admitted.

Hint Resolve e_fv_d_close_d_wrt_u_rec : lngen.
Hint Rewrite e_fv_d_close_d_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_e_close_e_wrt_u_rec :
forall e1 x1 n1,
  e_fv_e (close_e_wrt_u_rec n1 x1 e1) [=] remove x1 (e_fv_e e1).
Proof. Admitted.

Hint Resolve e_fv_e_close_e_wrt_u_rec : lngen.
Hint Rewrite e_fv_e_close_e_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_close_u_wrt_u_rec :
forall u1 x1 n1,
  e_fv_u (close_u_wrt_u_rec n1 x1 u1) [=] remove x1 (e_fv_u u1).
Proof. Admitted.

Hint Resolve e_fv_u_close_u_wrt_u_rec : lngen.
Hint Rewrite e_fv_u_close_u_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_v_close_v_wrt_u_rec :
forall v1 x1 n1,
  e_fv_v (close_v_wrt_u_rec n1 x1 v1) [=] remove x1 (e_fv_v v1).
Proof. Admitted.

Hint Resolve e_fv_v_close_v_wrt_u_rec : lngen.
Hint Rewrite e_fv_v_close_v_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

Lemma tt_fv_t_close_t_wrt_t :
forall t1 a1,
  tt_fv_t (close_t_wrt_t a1 t1) [=] remove a1 (tt_fv_t t1).
Proof. Admitted.

Hint Resolve tt_fv_t_close_t_wrt_t : lngen.
Hint Rewrite tt_fv_t_close_t_wrt_t using solve [auto] : lngen.

Lemma tt_fv_d_close_d_wrt_t :
forall d1 a1,
  tt_fv_d (close_d_wrt_t a1 d1) [=] remove a1 (tt_fv_d d1).
Proof. Admitted.

Hint Resolve tt_fv_d_close_d_wrt_t : lngen.
Hint Rewrite tt_fv_d_close_d_wrt_t using solve [auto] : lngen.

Lemma tt_fv_e_close_e_wrt_t :
forall e1 a1,
  tt_fv_e (close_e_wrt_t a1 e1) [=] remove a1 (tt_fv_e e1).
Proof. Admitted.

Hint Resolve tt_fv_e_close_e_wrt_t : lngen.
Hint Rewrite tt_fv_e_close_e_wrt_t using solve [auto] : lngen.

Lemma tt_fv_u_close_u_wrt_t :
forall u1 a1,
  tt_fv_u (close_u_wrt_t a1 u1) [=] remove a1 (tt_fv_u u1).
Proof. Admitted.

Hint Resolve tt_fv_u_close_u_wrt_t : lngen.
Hint Rewrite tt_fv_u_close_u_wrt_t using solve [auto] : lngen.

Lemma tt_fv_v_close_v_wrt_t :
forall v1 a1,
  tt_fv_v (close_v_wrt_t a1 v1) [=] remove a1 (tt_fv_v v1).
Proof. Admitted.

Hint Resolve tt_fv_v_close_v_wrt_t : lngen.
Hint Rewrite tt_fv_v_close_v_wrt_t using solve [auto] : lngen.

Lemma tt_fv_d_close_d_wrt_u :
forall d1 x1,
  tt_fv_d (close_d_wrt_u x1 d1) [=] tt_fv_d d1.
Proof. Admitted.

Hint Resolve tt_fv_d_close_d_wrt_u : lngen.
Hint Rewrite tt_fv_d_close_d_wrt_u using solve [auto] : lngen.

Lemma tt_fv_e_close_e_wrt_u :
forall e1 x1,
  tt_fv_e (close_e_wrt_u x1 e1) [=] tt_fv_e e1.
Proof. Admitted.

Hint Resolve tt_fv_e_close_e_wrt_u : lngen.
Hint Rewrite tt_fv_e_close_e_wrt_u using solve [auto] : lngen.

Lemma tt_fv_u_close_u_wrt_u :
forall u1 x1,
  tt_fv_u (close_u_wrt_u x1 u1) [=] tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_close_u_wrt_u : lngen.
Hint Rewrite tt_fv_u_close_u_wrt_u using solve [auto] : lngen.

Lemma tt_fv_v_close_v_wrt_u :
forall v1 x1,
  tt_fv_v (close_v_wrt_u x1 v1) [=] tt_fv_v v1.
Proof. Admitted.

Hint Resolve tt_fv_v_close_v_wrt_u : lngen.
Hint Rewrite tt_fv_v_close_v_wrt_u using solve [auto] : lngen.

Lemma e_fv_d_close_d_wrt_t :
forall d1 a1,
  e_fv_d (close_d_wrt_t a1 d1) [=] e_fv_d d1.
Proof. Admitted.

Hint Resolve e_fv_d_close_d_wrt_t : lngen.
Hint Rewrite e_fv_d_close_d_wrt_t using solve [auto] : lngen.

Lemma e_fv_e_close_e_wrt_t :
forall e1 a1,
  e_fv_e (close_e_wrt_t a1 e1) [=] e_fv_e e1.
Proof. Admitted.

Hint Resolve e_fv_e_close_e_wrt_t : lngen.
Hint Rewrite e_fv_e_close_e_wrt_t using solve [auto] : lngen.

Lemma e_fv_u_close_u_wrt_t :
forall u1 a1,
  e_fv_u (close_u_wrt_t a1 u1) [=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_close_u_wrt_t : lngen.
Hint Rewrite e_fv_u_close_u_wrt_t using solve [auto] : lngen.

Lemma e_fv_v_close_v_wrt_t :
forall v1 a1,
  e_fv_v (close_v_wrt_t a1 v1) [=] e_fv_v v1.
Proof. Admitted.

Hint Resolve e_fv_v_close_v_wrt_t : lngen.
Hint Rewrite e_fv_v_close_v_wrt_t using solve [auto] : lngen.

Lemma e_fv_d_close_d_wrt_u :
forall d1 x1,
  e_fv_d (close_d_wrt_u x1 d1) [=] remove x1 (e_fv_d d1).
Proof. Admitted.

Hint Resolve e_fv_d_close_d_wrt_u : lngen.
Hint Rewrite e_fv_d_close_d_wrt_u using solve [auto] : lngen.

Lemma e_fv_e_close_e_wrt_u :
forall e1 x1,
  e_fv_e (close_e_wrt_u x1 e1) [=] remove x1 (e_fv_e e1).
Proof. Admitted.

Hint Resolve e_fv_e_close_e_wrt_u : lngen.
Hint Rewrite e_fv_e_close_e_wrt_u using solve [auto] : lngen.

Lemma e_fv_u_close_u_wrt_u :
forall u1 x1,
  e_fv_u (close_u_wrt_u x1 u1) [=] remove x1 (e_fv_u u1).
Proof. Admitted.

Hint Resolve e_fv_u_close_u_wrt_u : lngen.
Hint Rewrite e_fv_u_close_u_wrt_u using solve [auto] : lngen.

Lemma e_fv_v_close_v_wrt_u :
forall v1 x1,
  e_fv_v (close_v_wrt_u x1 v1) [=] remove x1 (e_fv_v v1).
Proof. Admitted.

Hint Resolve e_fv_v_close_v_wrt_u : lngen.
Hint Rewrite e_fv_v_close_v_wrt_u using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_t_open_t_wrt_t_rec_lower_mutual :
(forall t1 t2 n1,
  tt_fv_t t1 [<=] tt_fv_t (open_t_wrt_t_rec n1 t2 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_t_open_t_wrt_t_rec_lower :
forall t1 t2 n1,
  tt_fv_t t1 [<=] tt_fv_t (open_t_wrt_t_rec n1 t2 t1).
Proof. Admitted.

Hint Resolve tt_fv_t_open_t_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_open_d_wrt_t_rec_lower_tt_fv_e_open_e_wrt_t_rec_lower_tt_fv_u_open_u_wrt_t_rec_lower_tt_fv_v_open_v_wrt_t_rec_lower_mutual :
(forall d1 t1 n1,
  tt_fv_d d1 [<=] tt_fv_d (open_d_wrt_t_rec n1 t1 d1)) /\
(forall e1 t1 n1,
  tt_fv_e e1 [<=] tt_fv_e (open_e_wrt_t_rec n1 t1 e1)) /\
(forall u1 t1 n1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_t_rec n1 t1 u1)) /\
(forall v1 t1 n1,
  tt_fv_v v1 [<=] tt_fv_v (open_v_wrt_t_rec n1 t1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_open_d_wrt_t_rec_lower :
forall d1 t1 n1,
  tt_fv_d d1 [<=] tt_fv_d (open_d_wrt_t_rec n1 t1 d1).
Proof. Admitted.

Hint Resolve tt_fv_d_open_d_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_e_open_e_wrt_t_rec_lower :
forall e1 t1 n1,
  tt_fv_e e1 [<=] tt_fv_e (open_e_wrt_t_rec n1 t1 e1).
Proof. Admitted.

Hint Resolve tt_fv_e_open_e_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_t_rec_lower :
forall u1 t1 n1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_t_rec n1 t1 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_v_open_v_wrt_t_rec_lower :
forall v1 t1 n1,
  tt_fv_v v1 [<=] tt_fv_v (open_v_wrt_t_rec n1 t1 v1).
Proof. Admitted.

Hint Resolve tt_fv_v_open_v_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_open_d_wrt_u_rec_lower_tt_fv_e_open_e_wrt_u_rec_lower_tt_fv_u_open_u_wrt_u_rec_lower_tt_fv_v_open_v_wrt_u_rec_lower_mutual :
(forall d1 u1 n1,
  tt_fv_d d1 [<=] tt_fv_d (open_d_wrt_u_rec n1 u1 d1)) /\
(forall e1 u1 n1,
  tt_fv_e e1 [<=] tt_fv_e (open_e_wrt_u_rec n1 u1 e1)) /\
(forall u1 u2 n1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_u_rec n1 u2 u1)) /\
(forall v1 u1 n1,
  tt_fv_v v1 [<=] tt_fv_v (open_v_wrt_u_rec n1 u1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_open_d_wrt_u_rec_lower :
forall d1 u1 n1,
  tt_fv_d d1 [<=] tt_fv_d (open_d_wrt_u_rec n1 u1 d1).
Proof. Admitted.

Hint Resolve tt_fv_d_open_d_wrt_u_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_e_open_e_wrt_u_rec_lower :
forall e1 u1 n1,
  tt_fv_e e1 [<=] tt_fv_e (open_e_wrt_u_rec n1 u1 e1).
Proof. Admitted.

Hint Resolve tt_fv_e_open_e_wrt_u_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_u_rec_lower :
forall u1 u2 n1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_u_rec n1 u2 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_u_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_v_open_v_wrt_u_rec_lower :
forall v1 u1 n1,
  tt_fv_v v1 [<=] tt_fv_v (open_v_wrt_u_rec n1 u1 v1).
Proof. Admitted.

Hint Resolve tt_fv_v_open_v_wrt_u_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_open_d_wrt_t_rec_lower_e_fv_e_open_e_wrt_t_rec_lower_e_fv_u_open_u_wrt_t_rec_lower_e_fv_v_open_v_wrt_t_rec_lower_mutual :
(forall d1 t1 n1,
  e_fv_d d1 [<=] e_fv_d (open_d_wrt_t_rec n1 t1 d1)) /\
(forall e1 t1 n1,
  e_fv_e e1 [<=] e_fv_e (open_e_wrt_t_rec n1 t1 e1)) /\
(forall u1 t1 n1,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_t_rec n1 t1 u1)) /\
(forall v1 t1 n1,
  e_fv_v v1 [<=] e_fv_v (open_v_wrt_t_rec n1 t1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_open_d_wrt_t_rec_lower :
forall d1 t1 n1,
  e_fv_d d1 [<=] e_fv_d (open_d_wrt_t_rec n1 t1 d1).
Proof. Admitted.

Hint Resolve e_fv_d_open_d_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_e_open_e_wrt_t_rec_lower :
forall e1 t1 n1,
  e_fv_e e1 [<=] e_fv_e (open_e_wrt_t_rec n1 t1 e1).
Proof. Admitted.

Hint Resolve e_fv_e_open_e_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_open_u_wrt_t_rec_lower :
forall u1 t1 n1,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_t_rec n1 t1 u1).
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_v_open_v_wrt_t_rec_lower :
forall v1 t1 n1,
  e_fv_v v1 [<=] e_fv_v (open_v_wrt_t_rec n1 t1 v1).
Proof. Admitted.

Hint Resolve e_fv_v_open_v_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_open_d_wrt_u_rec_lower_e_fv_e_open_e_wrt_u_rec_lower_e_fv_u_open_u_wrt_u_rec_lower_e_fv_v_open_v_wrt_u_rec_lower_mutual :
(forall d1 u1 n1,
  e_fv_d d1 [<=] e_fv_d (open_d_wrt_u_rec n1 u1 d1)) /\
(forall e1 u1 n1,
  e_fv_e e1 [<=] e_fv_e (open_e_wrt_u_rec n1 u1 e1)) /\
(forall u1 u2 n1,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_u_rec n1 u2 u1)) /\
(forall v1 u1 n1,
  e_fv_v v1 [<=] e_fv_v (open_v_wrt_u_rec n1 u1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_open_d_wrt_u_rec_lower :
forall d1 u1 n1,
  e_fv_d d1 [<=] e_fv_d (open_d_wrt_u_rec n1 u1 d1).
Proof. Admitted.

Hint Resolve e_fv_d_open_d_wrt_u_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_e_open_e_wrt_u_rec_lower :
forall e1 u1 n1,
  e_fv_e e1 [<=] e_fv_e (open_e_wrt_u_rec n1 u1 e1).
Proof. Admitted.

Hint Resolve e_fv_e_open_e_wrt_u_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_open_u_wrt_u_rec_lower :
forall u1 u2 n1,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_u_rec n1 u2 u1).
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_u_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_v_open_v_wrt_u_rec_lower :
forall v1 u1 n1,
  e_fv_v v1 [<=] e_fv_v (open_v_wrt_u_rec n1 u1 v1).
Proof. Admitted.

Hint Resolve e_fv_v_open_v_wrt_u_rec_lower : lngen.

(* end hide *)

Lemma tt_fv_t_open_t_wrt_t_lower :
forall t1 t2,
  tt_fv_t t1 [<=] tt_fv_t (open_t_wrt_t t1 t2).
Proof. Admitted.

Hint Resolve tt_fv_t_open_t_wrt_t_lower : lngen.

Lemma tt_fv_d_open_d_wrt_t_lower :
forall d1 t1,
  tt_fv_d d1 [<=] tt_fv_d (open_d_wrt_t d1 t1).
Proof. Admitted.

Hint Resolve tt_fv_d_open_d_wrt_t_lower : lngen.

Lemma tt_fv_e_open_e_wrt_t_lower :
forall e1 t1,
  tt_fv_e e1 [<=] tt_fv_e (open_e_wrt_t e1 t1).
Proof. Admitted.

Hint Resolve tt_fv_e_open_e_wrt_t_lower : lngen.

Lemma tt_fv_u_open_u_wrt_t_lower :
forall u1 t1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_t_lower : lngen.

Lemma tt_fv_v_open_v_wrt_t_lower :
forall v1 t1,
  tt_fv_v v1 [<=] tt_fv_v (open_v_wrt_t v1 t1).
Proof. Admitted.

Hint Resolve tt_fv_v_open_v_wrt_t_lower : lngen.

Lemma tt_fv_d_open_d_wrt_u_lower :
forall d1 u1,
  tt_fv_d d1 [<=] tt_fv_d (open_d_wrt_u d1 u1).
Proof. Admitted.

Hint Resolve tt_fv_d_open_d_wrt_u_lower : lngen.

Lemma tt_fv_e_open_e_wrt_u_lower :
forall e1 u1,
  tt_fv_e e1 [<=] tt_fv_e (open_e_wrt_u e1 u1).
Proof. Admitted.

Hint Resolve tt_fv_e_open_e_wrt_u_lower : lngen.

Lemma tt_fv_u_open_u_wrt_u_lower :
forall u1 u2,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_u_lower : lngen.

Lemma tt_fv_v_open_v_wrt_u_lower :
forall v1 u1,
  tt_fv_v v1 [<=] tt_fv_v (open_v_wrt_u v1 u1).
Proof. Admitted.

Hint Resolve tt_fv_v_open_v_wrt_u_lower : lngen.

Lemma e_fv_d_open_d_wrt_t_lower :
forall d1 t1,
  e_fv_d d1 [<=] e_fv_d (open_d_wrt_t d1 t1).
Proof. Admitted.

Hint Resolve e_fv_d_open_d_wrt_t_lower : lngen.

Lemma e_fv_e_open_e_wrt_t_lower :
forall e1 t1,
  e_fv_e e1 [<=] e_fv_e (open_e_wrt_t e1 t1).
Proof. Admitted.

Hint Resolve e_fv_e_open_e_wrt_t_lower : lngen.

Lemma e_fv_u_open_u_wrt_t_lower :
forall u1 t1,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_t_lower : lngen.

Lemma e_fv_v_open_v_wrt_t_lower :
forall v1 t1,
  e_fv_v v1 [<=] e_fv_v (open_v_wrt_t v1 t1).
Proof. Admitted.

Hint Resolve e_fv_v_open_v_wrt_t_lower : lngen.

Lemma e_fv_d_open_d_wrt_u_lower :
forall d1 u1,
  e_fv_d d1 [<=] e_fv_d (open_d_wrt_u d1 u1).
Proof. Admitted.

Hint Resolve e_fv_d_open_d_wrt_u_lower : lngen.

Lemma e_fv_e_open_e_wrt_u_lower :
forall e1 u1,
  e_fv_e e1 [<=] e_fv_e (open_e_wrt_u e1 u1).
Proof. Admitted.

Hint Resolve e_fv_e_open_e_wrt_u_lower : lngen.

Lemma e_fv_u_open_u_wrt_u_lower :
forall u1 u2,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_u_lower : lngen.

Lemma e_fv_v_open_v_wrt_u_lower :
forall v1 u1,
  e_fv_v v1 [<=] e_fv_v (open_v_wrt_u v1 u1).
Proof. Admitted.

Hint Resolve e_fv_v_open_v_wrt_u_lower : lngen.

(* begin hide *)

Lemma tt_fv_t_open_t_wrt_t_rec_upper_mutual :
(forall t1 t2 n1,
  tt_fv_t (open_t_wrt_t_rec n1 t2 t1) [<=] tt_fv_t t2 `union` tt_fv_t t1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_t_open_t_wrt_t_rec_upper :
forall t1 t2 n1,
  tt_fv_t (open_t_wrt_t_rec n1 t2 t1) [<=] tt_fv_t t2 `union` tt_fv_t t1.
Proof. Admitted.

Hint Resolve tt_fv_t_open_t_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_open_d_wrt_t_rec_upper_tt_fv_e_open_e_wrt_t_rec_upper_tt_fv_u_open_u_wrt_t_rec_upper_tt_fv_v_open_v_wrt_t_rec_upper_mutual :
(forall d1 t1 n1,
  tt_fv_d (open_d_wrt_t_rec n1 t1 d1) [<=] tt_fv_t t1 `union` tt_fv_d d1) /\
(forall e1 t1 n1,
  tt_fv_e (open_e_wrt_t_rec n1 t1 e1) [<=] tt_fv_t t1 `union` tt_fv_e e1) /\
(forall u1 t1 n1,
  tt_fv_u (open_u_wrt_t_rec n1 t1 u1) [<=] tt_fv_t t1 `union` tt_fv_u u1) /\
(forall v1 t1 n1,
  tt_fv_v (open_v_wrt_t_rec n1 t1 v1) [<=] tt_fv_t t1 `union` tt_fv_v v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_open_d_wrt_t_rec_upper :
forall d1 t1 n1,
  tt_fv_d (open_d_wrt_t_rec n1 t1 d1) [<=] tt_fv_t t1 `union` tt_fv_d d1.
Proof. Admitted.

Hint Resolve tt_fv_d_open_d_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_e_open_e_wrt_t_rec_upper :
forall e1 t1 n1,
  tt_fv_e (open_e_wrt_t_rec n1 t1 e1) [<=] tt_fv_t t1 `union` tt_fv_e e1.
Proof. Admitted.

Hint Resolve tt_fv_e_open_e_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_t_rec_upper :
forall u1 t1 n1,
  tt_fv_u (open_u_wrt_t_rec n1 t1 u1) [<=] tt_fv_t t1 `union` tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_v_open_v_wrt_t_rec_upper :
forall v1 t1 n1,
  tt_fv_v (open_v_wrt_t_rec n1 t1 v1) [<=] tt_fv_t t1 `union` tt_fv_v v1.
Proof. Admitted.

Hint Resolve tt_fv_v_open_v_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_open_d_wrt_u_rec_upper_tt_fv_e_open_e_wrt_u_rec_upper_tt_fv_u_open_u_wrt_u_rec_upper_tt_fv_v_open_v_wrt_u_rec_upper_mutual :
(forall d1 u1 n1,
  tt_fv_d (open_d_wrt_u_rec n1 u1 d1) [<=] tt_fv_u u1 `union` tt_fv_d d1) /\
(forall e1 u1 n1,
  tt_fv_e (open_e_wrt_u_rec n1 u1 e1) [<=] tt_fv_u u1 `union` tt_fv_e e1) /\
(forall u1 u2 n1,
  tt_fv_u (open_u_wrt_u_rec n1 u2 u1) [<=] tt_fv_u u2 `union` tt_fv_u u1) /\
(forall v1 u1 n1,
  tt_fv_v (open_v_wrt_u_rec n1 u1 v1) [<=] tt_fv_u u1 `union` tt_fv_v v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_d_open_d_wrt_u_rec_upper :
forall d1 u1 n1,
  tt_fv_d (open_d_wrt_u_rec n1 u1 d1) [<=] tt_fv_u u1 `union` tt_fv_d d1.
Proof. Admitted.

Hint Resolve tt_fv_d_open_d_wrt_u_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_e_open_e_wrt_u_rec_upper :
forall e1 u1 n1,
  tt_fv_e (open_e_wrt_u_rec n1 u1 e1) [<=] tt_fv_u u1 `union` tt_fv_e e1.
Proof. Admitted.

Hint Resolve tt_fv_e_open_e_wrt_u_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_u_rec_upper :
forall u1 u2 n1,
  tt_fv_u (open_u_wrt_u_rec n1 u2 u1) [<=] tt_fv_u u2 `union` tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_u_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_v_open_v_wrt_u_rec_upper :
forall v1 u1 n1,
  tt_fv_v (open_v_wrt_u_rec n1 u1 v1) [<=] tt_fv_u u1 `union` tt_fv_v v1.
Proof. Admitted.

Hint Resolve tt_fv_v_open_v_wrt_u_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_open_d_wrt_t_rec_upper_e_fv_e_open_e_wrt_t_rec_upper_e_fv_u_open_u_wrt_t_rec_upper_e_fv_v_open_v_wrt_t_rec_upper_mutual :
(forall d1 t1 n1,
  e_fv_d (open_d_wrt_t_rec n1 t1 d1) [<=] e_fv_d d1) /\
(forall e1 t1 n1,
  e_fv_e (open_e_wrt_t_rec n1 t1 e1) [<=] e_fv_e e1) /\
(forall u1 t1 n1,
  e_fv_u (open_u_wrt_t_rec n1 t1 u1) [<=] e_fv_u u1) /\
(forall v1 t1 n1,
  e_fv_v (open_v_wrt_t_rec n1 t1 v1) [<=] e_fv_v v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_open_d_wrt_t_rec_upper :
forall d1 t1 n1,
  e_fv_d (open_d_wrt_t_rec n1 t1 d1) [<=] e_fv_d d1.
Proof. Admitted.

Hint Resolve e_fv_d_open_d_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_e_open_e_wrt_t_rec_upper :
forall e1 t1 n1,
  e_fv_e (open_e_wrt_t_rec n1 t1 e1) [<=] e_fv_e e1.
Proof. Admitted.

Hint Resolve e_fv_e_open_e_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_open_u_wrt_t_rec_upper :
forall u1 t1 n1,
  e_fv_u (open_u_wrt_t_rec n1 t1 u1) [<=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_v_open_v_wrt_t_rec_upper :
forall v1 t1 n1,
  e_fv_v (open_v_wrt_t_rec n1 t1 v1) [<=] e_fv_v v1.
Proof. Admitted.

Hint Resolve e_fv_v_open_v_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_open_d_wrt_u_rec_upper_e_fv_e_open_e_wrt_u_rec_upper_e_fv_u_open_u_wrt_u_rec_upper_e_fv_v_open_v_wrt_u_rec_upper_mutual :
(forall d1 u1 n1,
  e_fv_d (open_d_wrt_u_rec n1 u1 d1) [<=] e_fv_u u1 `union` e_fv_d d1) /\
(forall e1 u1 n1,
  e_fv_e (open_e_wrt_u_rec n1 u1 e1) [<=] e_fv_u u1 `union` e_fv_e e1) /\
(forall u1 u2 n1,
  e_fv_u (open_u_wrt_u_rec n1 u2 u1) [<=] e_fv_u u2 `union` e_fv_u u1) /\
(forall v1 u1 n1,
  e_fv_v (open_v_wrt_u_rec n1 u1 v1) [<=] e_fv_u u1 `union` e_fv_v v1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_d_open_d_wrt_u_rec_upper :
forall d1 u1 n1,
  e_fv_d (open_d_wrt_u_rec n1 u1 d1) [<=] e_fv_u u1 `union` e_fv_d d1.
Proof. Admitted.

Hint Resolve e_fv_d_open_d_wrt_u_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_e_open_e_wrt_u_rec_upper :
forall e1 u1 n1,
  e_fv_e (open_e_wrt_u_rec n1 u1 e1) [<=] e_fv_u u1 `union` e_fv_e e1.
Proof. Admitted.

Hint Resolve e_fv_e_open_e_wrt_u_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_open_u_wrt_u_rec_upper :
forall u1 u2 n1,
  e_fv_u (open_u_wrt_u_rec n1 u2 u1) [<=] e_fv_u u2 `union` e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_u_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_v_open_v_wrt_u_rec_upper :
forall v1 u1 n1,
  e_fv_v (open_v_wrt_u_rec n1 u1 v1) [<=] e_fv_u u1 `union` e_fv_v v1.
Proof. Admitted.

Hint Resolve e_fv_v_open_v_wrt_u_rec_upper : lngen.

(* end hide *)

Lemma tt_fv_t_open_t_wrt_t_upper :
forall t1 t2,
  tt_fv_t (open_t_wrt_t t1 t2) [<=] tt_fv_t t2 `union` tt_fv_t t1.
Proof. Admitted.

Hint Resolve tt_fv_t_open_t_wrt_t_upper : lngen.

Lemma tt_fv_d_open_d_wrt_t_upper :
forall d1 t1,
  tt_fv_d (open_d_wrt_t d1 t1) [<=] tt_fv_t t1 `union` tt_fv_d d1.
Proof. Admitted.

Hint Resolve tt_fv_d_open_d_wrt_t_upper : lngen.

Lemma tt_fv_e_open_e_wrt_t_upper :
forall e1 t1,
  tt_fv_e (open_e_wrt_t e1 t1) [<=] tt_fv_t t1 `union` tt_fv_e e1.
Proof. Admitted.

Hint Resolve tt_fv_e_open_e_wrt_t_upper : lngen.

Lemma tt_fv_u_open_u_wrt_t_upper :
forall u1 t1,
  tt_fv_u (open_u_wrt_t u1 t1) [<=] tt_fv_t t1 `union` tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_t_upper : lngen.

Lemma tt_fv_v_open_v_wrt_t_upper :
forall v1 t1,
  tt_fv_v (open_v_wrt_t v1 t1) [<=] tt_fv_t t1 `union` tt_fv_v v1.
Proof. Admitted.

Hint Resolve tt_fv_v_open_v_wrt_t_upper : lngen.

Lemma tt_fv_d_open_d_wrt_u_upper :
forall d1 u1,
  tt_fv_d (open_d_wrt_u d1 u1) [<=] tt_fv_u u1 `union` tt_fv_d d1.
Proof. Admitted.

Hint Resolve tt_fv_d_open_d_wrt_u_upper : lngen.

Lemma tt_fv_e_open_e_wrt_u_upper :
forall e1 u1,
  tt_fv_e (open_e_wrt_u e1 u1) [<=] tt_fv_u u1 `union` tt_fv_e e1.
Proof. Admitted.

Hint Resolve tt_fv_e_open_e_wrt_u_upper : lngen.

Lemma tt_fv_u_open_u_wrt_u_upper :
forall u1 u2,
  tt_fv_u (open_u_wrt_u u1 u2) [<=] tt_fv_u u2 `union` tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_u_upper : lngen.

Lemma tt_fv_v_open_v_wrt_u_upper :
forall v1 u1,
  tt_fv_v (open_v_wrt_u v1 u1) [<=] tt_fv_u u1 `union` tt_fv_v v1.
Proof. Admitted.

Hint Resolve tt_fv_v_open_v_wrt_u_upper : lngen.

Lemma e_fv_d_open_d_wrt_t_upper :
forall d1 t1,
  e_fv_d (open_d_wrt_t d1 t1) [<=] e_fv_d d1.
Proof. Admitted.

Hint Resolve e_fv_d_open_d_wrt_t_upper : lngen.

Lemma e_fv_e_open_e_wrt_t_upper :
forall e1 t1,
  e_fv_e (open_e_wrt_t e1 t1) [<=] e_fv_e e1.
Proof. Admitted.

Hint Resolve e_fv_e_open_e_wrt_t_upper : lngen.

Lemma e_fv_u_open_u_wrt_t_upper :
forall u1 t1,
  e_fv_u (open_u_wrt_t u1 t1) [<=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_t_upper : lngen.

Lemma e_fv_v_open_v_wrt_t_upper :
forall v1 t1,
  e_fv_v (open_v_wrt_t v1 t1) [<=] e_fv_v v1.
Proof. Admitted.

Hint Resolve e_fv_v_open_v_wrt_t_upper : lngen.

Lemma e_fv_d_open_d_wrt_u_upper :
forall d1 u1,
  e_fv_d (open_d_wrt_u d1 u1) [<=] e_fv_u u1 `union` e_fv_d d1.
Proof. Admitted.

Hint Resolve e_fv_d_open_d_wrt_u_upper : lngen.

Lemma e_fv_e_open_e_wrt_u_upper :
forall e1 u1,
  e_fv_e (open_e_wrt_u e1 u1) [<=] e_fv_u u1 `union` e_fv_e e1.
Proof. Admitted.

Hint Resolve e_fv_e_open_e_wrt_u_upper : lngen.

Lemma e_fv_u_open_u_wrt_u_upper :
forall u1 u2,
  e_fv_u (open_u_wrt_u u1 u2) [<=] e_fv_u u2 `union` e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_u_upper : lngen.

Lemma e_fv_v_open_v_wrt_u_upper :
forall v1 u1,
  e_fv_v (open_v_wrt_u v1 u1) [<=] e_fv_u u1 `union` e_fv_v v1.
Proof. Admitted.

Hint Resolve e_fv_v_open_v_wrt_u_upper : lngen.

(* begin hide *)

Lemma tt_fv_t_t_subst_t_fresh_mutual :
(forall t1 t2 a1,
  a1 `notin` tt_fv_t t1 ->
  tt_fv_t (t_subst_t t2 a1 t1) [=] tt_fv_t t1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_t_t_subst_t_fresh :
forall t1 t2 a1,
  a1 `notin` tt_fv_t t1 ->
  tt_fv_t (t_subst_t t2 a1 t1) [=] tt_fv_t t1.
Proof. Admitted.

Hint Resolve tt_fv_t_t_subst_t_fresh : lngen.
Hint Rewrite tt_fv_t_t_subst_t_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_d_t_subst_d_fresh_tt_fv_e_t_subst_e_fresh_tt_fv_u_t_subst_u_fresh_tt_fv_v_t_subst_v_fresh_mutual :
(forall d1 t1 a1,
  a1 `notin` tt_fv_d d1 ->
  tt_fv_d (t_subst_d t1 a1 d1) [=] tt_fv_d d1) /\
(forall e1 t1 a1,
  a1 `notin` tt_fv_e e1 ->
  tt_fv_e (t_subst_e t1 a1 e1) [=] tt_fv_e e1) /\
(forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  tt_fv_u (t_subst_u t1 a1 u1) [=] tt_fv_u u1) /\
(forall v1 t1 a1,
  a1 `notin` tt_fv_v v1 ->
  tt_fv_v (t_subst_v t1 a1 v1) [=] tt_fv_v v1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_d_t_subst_d_fresh :
forall d1 t1 a1,
  a1 `notin` tt_fv_d d1 ->
  tt_fv_d (t_subst_d t1 a1 d1) [=] tt_fv_d d1.
Proof. Admitted.

Hint Resolve tt_fv_d_t_subst_d_fresh : lngen.
Hint Rewrite tt_fv_d_t_subst_d_fresh using solve [auto] : lngen.

Lemma tt_fv_e_t_subst_e_fresh :
forall e1 t1 a1,
  a1 `notin` tt_fv_e e1 ->
  tt_fv_e (t_subst_e t1 a1 e1) [=] tt_fv_e e1.
Proof. Admitted.

Hint Resolve tt_fv_e_t_subst_e_fresh : lngen.
Hint Rewrite tt_fv_e_t_subst_e_fresh using solve [auto] : lngen.

Lemma tt_fv_u_t_subst_u_fresh :
forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  tt_fv_u (t_subst_u t1 a1 u1) [=] tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_t_subst_u_fresh : lngen.
Hint Rewrite tt_fv_u_t_subst_u_fresh using solve [auto] : lngen.

Lemma tt_fv_v_t_subst_v_fresh :
forall v1 t1 a1,
  a1 `notin` tt_fv_v v1 ->
  tt_fv_v (t_subst_v t1 a1 v1) [=] tt_fv_v v1.
Proof. Admitted.

Hint Resolve tt_fv_v_t_subst_v_fresh : lngen.
Hint Rewrite tt_fv_v_t_subst_v_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_d_e_subst_d_fresh_tt_fv_e_e_subst_e_fresh_tt_fv_u_e_subst_u_fresh_tt_fv_v_e_subst_v_fresh_mutual :
(forall d1 t1 a1,
  e_fv_d (t_subst_d t1 a1 d1) [=] e_fv_d d1) /\
(forall e1 t1 a1,
  e_fv_e (t_subst_e t1 a1 e1) [=] e_fv_e e1) /\
(forall u1 t1 a1,
  e_fv_u (t_subst_u t1 a1 u1) [=] e_fv_u u1) /\
(forall v1 t1 a1,
  e_fv_v (t_subst_v t1 a1 v1) [=] e_fv_v v1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_d_e_subst_d_fresh :
forall d1 t1 a1,
  e_fv_d (t_subst_d t1 a1 d1) [=] e_fv_d d1.
Proof. Admitted.

Hint Resolve tt_fv_d_e_subst_d_fresh : lngen.
Hint Rewrite tt_fv_d_e_subst_d_fresh using solve [auto] : lngen.

Lemma tt_fv_e_e_subst_e_fresh :
forall e1 t1 a1,
  e_fv_e (t_subst_e t1 a1 e1) [=] e_fv_e e1.
Proof. Admitted.

Hint Resolve tt_fv_e_e_subst_e_fresh : lngen.
Hint Rewrite tt_fv_e_e_subst_e_fresh using solve [auto] : lngen.

Lemma tt_fv_u_e_subst_u_fresh :
forall u1 t1 a1,
  e_fv_u (t_subst_u t1 a1 u1) [=] e_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_e_subst_u_fresh : lngen.
Hint Rewrite tt_fv_u_e_subst_u_fresh using solve [auto] : lngen.

Lemma tt_fv_v_e_subst_v_fresh :
forall v1 t1 a1,
  e_fv_v (t_subst_v t1 a1 v1) [=] e_fv_v v1.
Proof. Admitted.

Hint Resolve tt_fv_v_e_subst_v_fresh : lngen.
Hint Rewrite tt_fv_v_e_subst_v_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma e_fv_d_e_subst_d_fresh_e_fv_e_e_subst_e_fresh_e_fv_u_e_subst_u_fresh_e_fv_v_e_subst_v_fresh_mutual :
(forall d1 u1 x1,
  x1 `notin` e_fv_d d1 ->
  e_fv_d (e_subst_d u1 x1 d1) [=] e_fv_d d1) /\
(forall e1 u1 x1,
  x1 `notin` e_fv_e e1 ->
  e_fv_e (e_subst_e u1 x1 e1) [=] e_fv_e e1) /\
(forall u1 u2 x1,
  x1 `notin` e_fv_u u1 ->
  e_fv_u (e_subst_u u2 x1 u1) [=] e_fv_u u1) /\
(forall v1 u1 x1,
  x1 `notin` e_fv_v v1 ->
  e_fv_v (e_subst_v u1 x1 v1) [=] e_fv_v v1).
Proof. Admitted.

(* end hide *)

Lemma e_fv_d_e_subst_d_fresh :
forall d1 u1 x1,
  x1 `notin` e_fv_d d1 ->
  e_fv_d (e_subst_d u1 x1 d1) [=] e_fv_d d1.
Proof. Admitted.

Hint Resolve e_fv_d_e_subst_d_fresh : lngen.
Hint Rewrite e_fv_d_e_subst_d_fresh using solve [auto] : lngen.

Lemma e_fv_e_e_subst_e_fresh :
forall e1 u1 x1,
  x1 `notin` e_fv_e e1 ->
  e_fv_e (e_subst_e u1 x1 e1) [=] e_fv_e e1.
Proof. Admitted.

Hint Resolve e_fv_e_e_subst_e_fresh : lngen.
Hint Rewrite e_fv_e_e_subst_e_fresh using solve [auto] : lngen.

Lemma e_fv_u_e_subst_u_fresh :
forall u1 u2 x1,
  x1 `notin` e_fv_u u1 ->
  e_fv_u (e_subst_u u2 x1 u1) [=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_e_subst_u_fresh : lngen.
Hint Rewrite e_fv_u_e_subst_u_fresh using solve [auto] : lngen.

Lemma e_fv_v_e_subst_v_fresh :
forall v1 u1 x1,
  x1 `notin` e_fv_v v1 ->
  e_fv_v (e_subst_v u1 x1 v1) [=] e_fv_v v1.
Proof. Admitted.

Hint Resolve e_fv_v_e_subst_v_fresh : lngen.
Hint Rewrite e_fv_v_e_subst_v_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_t_t_subst_t_lower_mutual :
(forall t1 t2 a1,
  remove a1 (tt_fv_t t1) [<=] tt_fv_t (t_subst_t t2 a1 t1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_t_t_subst_t_lower :
forall t1 t2 a1,
  remove a1 (tt_fv_t t1) [<=] tt_fv_t (t_subst_t t2 a1 t1).
Proof. Admitted.

Hint Resolve tt_fv_t_t_subst_t_lower : lngen.

(* begin hide *)

Lemma tt_fv_d_t_subst_d_lower_tt_fv_e_t_subst_e_lower_tt_fv_u_t_subst_u_lower_tt_fv_v_t_subst_v_lower_mutual :
(forall d1 t1 a1,
  remove a1 (tt_fv_d d1) [<=] tt_fv_d (t_subst_d t1 a1 d1)) /\
(forall e1 t1 a1,
  remove a1 (tt_fv_e e1) [<=] tt_fv_e (t_subst_e t1 a1 e1)) /\
(forall u1 t1 a1,
  remove a1 (tt_fv_u u1) [<=] tt_fv_u (t_subst_u t1 a1 u1)) /\
(forall v1 t1 a1,
  remove a1 (tt_fv_v v1) [<=] tt_fv_v (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_d_t_subst_d_lower :
forall d1 t1 a1,
  remove a1 (tt_fv_d d1) [<=] tt_fv_d (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve tt_fv_d_t_subst_d_lower : lngen.

Lemma tt_fv_e_t_subst_e_lower :
forall e1 t1 a1,
  remove a1 (tt_fv_e e1) [<=] tt_fv_e (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve tt_fv_e_t_subst_e_lower : lngen.

Lemma tt_fv_u_t_subst_u_lower :
forall u1 t1 a1,
  remove a1 (tt_fv_u u1) [<=] tt_fv_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_t_subst_u_lower : lngen.

Lemma tt_fv_v_t_subst_v_lower :
forall v1 t1 a1,
  remove a1 (tt_fv_v v1) [<=] tt_fv_v (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve tt_fv_v_t_subst_v_lower : lngen.

(* begin hide *)

Lemma tt_fv_d_e_subst_d_lower_tt_fv_e_e_subst_e_lower_tt_fv_u_e_subst_u_lower_tt_fv_v_e_subst_v_lower_mutual :
(forall d1 u1 x1,
  tt_fv_d d1 [<=] tt_fv_d (e_subst_d u1 x1 d1)) /\
(forall e1 u1 x1,
  tt_fv_e e1 [<=] tt_fv_e (e_subst_e u1 x1 e1)) /\
(forall u1 u2 x1,
  tt_fv_u u1 [<=] tt_fv_u (e_subst_u u2 x1 u1)) /\
(forall v1 u1 x1,
  tt_fv_v v1 [<=] tt_fv_v (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_d_e_subst_d_lower :
forall d1 u1 x1,
  tt_fv_d d1 [<=] tt_fv_d (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve tt_fv_d_e_subst_d_lower : lngen.

Lemma tt_fv_e_e_subst_e_lower :
forall e1 u1 x1,
  tt_fv_e e1 [<=] tt_fv_e (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve tt_fv_e_e_subst_e_lower : lngen.

Lemma tt_fv_u_e_subst_u_lower :
forall u1 u2 x1,
  tt_fv_u u1 [<=] tt_fv_u (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_e_subst_u_lower : lngen.

Lemma tt_fv_v_e_subst_v_lower :
forall v1 u1 x1,
  tt_fv_v v1 [<=] tt_fv_v (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve tt_fv_v_e_subst_v_lower : lngen.

(* begin hide *)

Lemma e_fv_d_t_subst_d_lower_e_fv_e_t_subst_e_lower_e_fv_u_t_subst_u_lower_e_fv_v_t_subst_v_lower_mutual :
(forall d1 t1 a1,
  e_fv_d d1 [<=] e_fv_d (t_subst_d t1 a1 d1)) /\
(forall e1 t1 a1,
  e_fv_e e1 [<=] e_fv_e (t_subst_e t1 a1 e1)) /\
(forall u1 t1 a1,
  e_fv_u u1 [<=] e_fv_u (t_subst_u t1 a1 u1)) /\
(forall v1 t1 a1,
  e_fv_v v1 [<=] e_fv_v (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_d_t_subst_d_lower :
forall d1 t1 a1,
  e_fv_d d1 [<=] e_fv_d (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve e_fv_d_t_subst_d_lower : lngen.

Lemma e_fv_e_t_subst_e_lower :
forall e1 t1 a1,
  e_fv_e e1 [<=] e_fv_e (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve e_fv_e_t_subst_e_lower : lngen.

Lemma e_fv_u_t_subst_u_lower :
forall u1 t1 a1,
  e_fv_u u1 [<=] e_fv_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve e_fv_u_t_subst_u_lower : lngen.

Lemma e_fv_v_t_subst_v_lower :
forall v1 t1 a1,
  e_fv_v v1 [<=] e_fv_v (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve e_fv_v_t_subst_v_lower : lngen.

(* begin hide *)

Lemma e_fv_d_e_subst_d_lower_e_fv_e_e_subst_e_lower_e_fv_u_e_subst_u_lower_e_fv_v_e_subst_v_lower_mutual :
(forall d1 u1 x1,
  remove x1 (e_fv_d d1) [<=] e_fv_d (e_subst_d u1 x1 d1)) /\
(forall e1 u1 x1,
  remove x1 (e_fv_e e1) [<=] e_fv_e (e_subst_e u1 x1 e1)) /\
(forall u1 u2 x1,
  remove x1 (e_fv_u u1) [<=] e_fv_u (e_subst_u u2 x1 u1)) /\
(forall v1 u1 x1,
  remove x1 (e_fv_v v1) [<=] e_fv_v (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_d_e_subst_d_lower :
forall d1 u1 x1,
  remove x1 (e_fv_d d1) [<=] e_fv_d (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_fv_d_e_subst_d_lower : lngen.

Lemma e_fv_e_e_subst_e_lower :
forall e1 u1 x1,
  remove x1 (e_fv_e e1) [<=] e_fv_e (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_fv_e_e_subst_e_lower : lngen.

Lemma e_fv_u_e_subst_u_lower :
forall u1 u2 x1,
  remove x1 (e_fv_u u1) [<=] e_fv_u (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_fv_u_e_subst_u_lower : lngen.

Lemma e_fv_v_e_subst_v_lower :
forall v1 u1 x1,
  remove x1 (e_fv_v v1) [<=] e_fv_v (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_fv_v_e_subst_v_lower : lngen.

(* begin hide *)

Lemma tt_fv_t_t_subst_t_notin_mutual :
(forall t1 t2 a1 a2,
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t (t_subst_t t2 a1 t1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_t_t_subst_t_notin :
forall t1 t2 a1 a2,
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t (t_subst_t t2 a1 t1).
Proof. Admitted.

Hint Resolve tt_fv_t_t_subst_t_notin : lngen.

(* begin hide *)

Lemma tt_fv_d_t_subst_d_notin_tt_fv_e_t_subst_e_notin_tt_fv_u_t_subst_u_notin_tt_fv_v_t_subst_v_notin_mutual :
(forall d1 t1 a1 a2,
  a2 `notin` tt_fv_d d1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_d (t_subst_d t1 a1 d1)) /\
(forall e1 t1 a1 a2,
  a2 `notin` tt_fv_e e1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_e (t_subst_e t1 a1 e1)) /\
(forall u1 t1 a1 a2,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_u (t_subst_u t1 a1 u1)) /\
(forall v1 t1 a1 a2,
  a2 `notin` tt_fv_v v1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_v (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_d_t_subst_d_notin :
forall d1 t1 a1 a2,
  a2 `notin` tt_fv_d d1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_d (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve tt_fv_d_t_subst_d_notin : lngen.

Lemma tt_fv_e_t_subst_e_notin :
forall e1 t1 a1 a2,
  a2 `notin` tt_fv_e e1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_e (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve tt_fv_e_t_subst_e_notin : lngen.

Lemma tt_fv_u_t_subst_u_notin :
forall u1 t1 a1 a2,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_t_subst_u_notin : lngen.

Lemma tt_fv_v_t_subst_v_notin :
forall v1 t1 a1 a2,
  a2 `notin` tt_fv_v v1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_v (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve tt_fv_v_t_subst_v_notin : lngen.

(* begin hide *)

Lemma tt_fv_d_e_subst_d_notin_tt_fv_e_e_subst_e_notin_tt_fv_u_e_subst_u_notin_tt_fv_v_e_subst_v_notin_mutual :
(forall d1 u1 x1 a1,
  a1 `notin` tt_fv_d d1 ->
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_d (e_subst_d u1 x1 d1)) /\
(forall e1 u1 x1 a1,
  a1 `notin` tt_fv_e e1 ->
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_e (e_subst_e u1 x1 e1)) /\
(forall u1 u2 x1 a1,
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u (e_subst_u u2 x1 u1)) /\
(forall v1 u1 x1 a1,
  a1 `notin` tt_fv_v v1 ->
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_v (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_d_e_subst_d_notin :
forall d1 u1 x1 a1,
  a1 `notin` tt_fv_d d1 ->
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_d (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve tt_fv_d_e_subst_d_notin : lngen.

Lemma tt_fv_e_e_subst_e_notin :
forall e1 u1 x1 a1,
  a1 `notin` tt_fv_e e1 ->
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_e (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve tt_fv_e_e_subst_e_notin : lngen.

Lemma tt_fv_u_e_subst_u_notin :
forall u1 u2 x1 a1,
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_e_subst_u_notin : lngen.

Lemma tt_fv_v_e_subst_v_notin :
forall v1 u1 x1 a1,
  a1 `notin` tt_fv_v v1 ->
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_v (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve tt_fv_v_e_subst_v_notin : lngen.

(* begin hide *)

Lemma e_fv_d_t_subst_d_notin_e_fv_e_t_subst_e_notin_e_fv_u_t_subst_u_notin_e_fv_v_t_subst_v_notin_mutual :
(forall d1 t1 a1 x1,
  x1 `notin` e_fv_d d1 ->
  x1 `notin` e_fv_d (t_subst_d t1 a1 d1)) /\
(forall e1 t1 a1 x1,
  x1 `notin` e_fv_e e1 ->
  x1 `notin` e_fv_e (t_subst_e t1 a1 e1)) /\
(forall u1 t1 a1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (t_subst_u t1 a1 u1)) /\
(forall v1 t1 a1 x1,
  x1 `notin` e_fv_v v1 ->
  x1 `notin` e_fv_v (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_d_t_subst_d_notin :
forall d1 t1 a1 x1,
  x1 `notin` e_fv_d d1 ->
  x1 `notin` e_fv_d (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve e_fv_d_t_subst_d_notin : lngen.

Lemma e_fv_e_t_subst_e_notin :
forall e1 t1 a1 x1,
  x1 `notin` e_fv_e e1 ->
  x1 `notin` e_fv_e (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve e_fv_e_t_subst_e_notin : lngen.

Lemma e_fv_u_t_subst_u_notin :
forall u1 t1 a1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve e_fv_u_t_subst_u_notin : lngen.

Lemma e_fv_v_t_subst_v_notin :
forall v1 t1 a1 x1,
  x1 `notin` e_fv_v v1 ->
  x1 `notin` e_fv_v (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve e_fv_v_t_subst_v_notin : lngen.

(* begin hide *)

Lemma e_fv_d_e_subst_d_notin_e_fv_e_e_subst_e_notin_e_fv_u_e_subst_u_notin_e_fv_v_e_subst_v_notin_mutual :
(forall d1 u1 x1 x2,
  x2 `notin` e_fv_d d1 ->
  x2 `notin` e_fv_u u1 ->
  x2 `notin` e_fv_d (e_subst_d u1 x1 d1)) /\
(forall e1 u1 x1 x2,
  x2 `notin` e_fv_e e1 ->
  x2 `notin` e_fv_u u1 ->
  x2 `notin` e_fv_e (e_subst_e u1 x1 e1)) /\
(forall u1 u2 x1 x2,
  x2 `notin` e_fv_u u1 ->
  x2 `notin` e_fv_u u2 ->
  x2 `notin` e_fv_u (e_subst_u u2 x1 u1)) /\
(forall v1 u1 x1 x2,
  x2 `notin` e_fv_v v1 ->
  x2 `notin` e_fv_u u1 ->
  x2 `notin` e_fv_v (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_d_e_subst_d_notin :
forall d1 u1 x1 x2,
  x2 `notin` e_fv_d d1 ->
  x2 `notin` e_fv_u u1 ->
  x2 `notin` e_fv_d (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_fv_d_e_subst_d_notin : lngen.

Lemma e_fv_e_e_subst_e_notin :
forall e1 u1 x1 x2,
  x2 `notin` e_fv_e e1 ->
  x2 `notin` e_fv_u u1 ->
  x2 `notin` e_fv_e (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_fv_e_e_subst_e_notin : lngen.

Lemma e_fv_u_e_subst_u_notin :
forall u1 u2 x1 x2,
  x2 `notin` e_fv_u u1 ->
  x2 `notin` e_fv_u u2 ->
  x2 `notin` e_fv_u (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_fv_u_e_subst_u_notin : lngen.

Lemma e_fv_v_e_subst_v_notin :
forall v1 u1 x1 x2,
  x2 `notin` e_fv_v v1 ->
  x2 `notin` e_fv_u u1 ->
  x2 `notin` e_fv_v (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_fv_v_e_subst_v_notin : lngen.

(* begin hide *)

Lemma tt_fv_t_t_subst_t_upper_mutual :
(forall t1 t2 a1,
  tt_fv_t (t_subst_t t2 a1 t1) [<=] tt_fv_t t2 `union` remove a1 (tt_fv_t t1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_t_t_subst_t_upper :
forall t1 t2 a1,
  tt_fv_t (t_subst_t t2 a1 t1) [<=] tt_fv_t t2 `union` remove a1 (tt_fv_t t1).
Proof. Admitted.

Hint Resolve tt_fv_t_t_subst_t_upper : lngen.

(* begin hide *)

Lemma tt_fv_d_t_subst_d_upper_tt_fv_e_t_subst_e_upper_tt_fv_u_t_subst_u_upper_tt_fv_v_t_subst_v_upper_mutual :
(forall d1 t1 a1,
  tt_fv_d (t_subst_d t1 a1 d1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_d d1)) /\
(forall e1 t1 a1,
  tt_fv_e (t_subst_e t1 a1 e1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_e e1)) /\
(forall u1 t1 a1,
  tt_fv_u (t_subst_u t1 a1 u1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_u u1)) /\
(forall v1 t1 a1,
  tt_fv_v (t_subst_v t1 a1 v1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_v v1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_d_t_subst_d_upper :
forall d1 t1 a1,
  tt_fv_d (t_subst_d t1 a1 d1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_d d1).
Proof. Admitted.

Hint Resolve tt_fv_d_t_subst_d_upper : lngen.

Lemma tt_fv_e_t_subst_e_upper :
forall e1 t1 a1,
  tt_fv_e (t_subst_e t1 a1 e1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_e e1).
Proof. Admitted.

Hint Resolve tt_fv_e_t_subst_e_upper : lngen.

Lemma tt_fv_u_t_subst_u_upper :
forall u1 t1 a1,
  tt_fv_u (t_subst_u t1 a1 u1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_u u1).
Proof. Admitted.

Hint Resolve tt_fv_u_t_subst_u_upper : lngen.

Lemma tt_fv_v_t_subst_v_upper :
forall v1 t1 a1,
  tt_fv_v (t_subst_v t1 a1 v1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_v v1).
Proof. Admitted.

Hint Resolve tt_fv_v_t_subst_v_upper : lngen.

(* begin hide *)

Lemma tt_fv_d_e_subst_d_upper_tt_fv_e_e_subst_e_upper_tt_fv_u_e_subst_u_upper_tt_fv_v_e_subst_v_upper_mutual :
(forall d1 u1 x1,
  tt_fv_d (e_subst_d u1 x1 d1) [<=] tt_fv_u u1 `union` tt_fv_d d1) /\
(forall e1 u1 x1,
  tt_fv_e (e_subst_e u1 x1 e1) [<=] tt_fv_u u1 `union` tt_fv_e e1) /\
(forall u1 u2 x1,
  tt_fv_u (e_subst_u u2 x1 u1) [<=] tt_fv_u u2 `union` tt_fv_u u1) /\
(forall v1 u1 x1,
  tt_fv_v (e_subst_v u1 x1 v1) [<=] tt_fv_u u1 `union` tt_fv_v v1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_d_e_subst_d_upper :
forall d1 u1 x1,
  tt_fv_d (e_subst_d u1 x1 d1) [<=] tt_fv_u u1 `union` tt_fv_d d1.
Proof. Admitted.

Hint Resolve tt_fv_d_e_subst_d_upper : lngen.

Lemma tt_fv_e_e_subst_e_upper :
forall e1 u1 x1,
  tt_fv_e (e_subst_e u1 x1 e1) [<=] tt_fv_u u1 `union` tt_fv_e e1.
Proof. Admitted.

Hint Resolve tt_fv_e_e_subst_e_upper : lngen.

Lemma tt_fv_u_e_subst_u_upper :
forall u1 u2 x1,
  tt_fv_u (e_subst_u u2 x1 u1) [<=] tt_fv_u u2 `union` tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_e_subst_u_upper : lngen.

Lemma tt_fv_v_e_subst_v_upper :
forall v1 u1 x1,
  tt_fv_v (e_subst_v u1 x1 v1) [<=] tt_fv_u u1 `union` tt_fv_v v1.
Proof. Admitted.

Hint Resolve tt_fv_v_e_subst_v_upper : lngen.

(* begin hide *)

Lemma e_fv_d_t_subst_d_upper_e_fv_e_t_subst_e_upper_e_fv_u_t_subst_u_upper_e_fv_v_t_subst_v_upper_mutual :
(forall d1 t1 a1,
  e_fv_d (t_subst_d t1 a1 d1) [<=] e_fv_d d1) /\
(forall e1 t1 a1,
  e_fv_e (t_subst_e t1 a1 e1) [<=] e_fv_e e1) /\
(forall u1 t1 a1,
  e_fv_u (t_subst_u t1 a1 u1) [<=] e_fv_u u1) /\
(forall v1 t1 a1,
  e_fv_v (t_subst_v t1 a1 v1) [<=] e_fv_v v1).
Proof. Admitted.

(* end hide *)

Lemma e_fv_d_t_subst_d_upper :
forall d1 t1 a1,
  e_fv_d (t_subst_d t1 a1 d1) [<=] e_fv_d d1.
Proof. Admitted.

Hint Resolve e_fv_d_t_subst_d_upper : lngen.

Lemma e_fv_e_t_subst_e_upper :
forall e1 t1 a1,
  e_fv_e (t_subst_e t1 a1 e1) [<=] e_fv_e e1.
Proof. Admitted.

Hint Resolve e_fv_e_t_subst_e_upper : lngen.

Lemma e_fv_u_t_subst_u_upper :
forall u1 t1 a1,
  e_fv_u (t_subst_u t1 a1 u1) [<=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_t_subst_u_upper : lngen.

Lemma e_fv_v_t_subst_v_upper :
forall v1 t1 a1,
  e_fv_v (t_subst_v t1 a1 v1) [<=] e_fv_v v1.
Proof. Admitted.

Hint Resolve e_fv_v_t_subst_v_upper : lngen.

(* begin hide *)

Lemma e_fv_d_e_subst_d_upper_e_fv_e_e_subst_e_upper_e_fv_u_e_subst_u_upper_e_fv_v_e_subst_v_upper_mutual :
(forall d1 u1 x1,
  e_fv_d (e_subst_d u1 x1 d1) [<=] e_fv_u u1 `union` remove x1 (e_fv_d d1)) /\
(forall e1 u1 x1,
  e_fv_e (e_subst_e u1 x1 e1) [<=] e_fv_u u1 `union` remove x1 (e_fv_e e1)) /\
(forall u1 u2 x1,
  e_fv_u (e_subst_u u2 x1 u1) [<=] e_fv_u u2 `union` remove x1 (e_fv_u u1)) /\
(forall v1 u1 x1,
  e_fv_v (e_subst_v u1 x1 v1) [<=] e_fv_u u1 `union` remove x1 (e_fv_v v1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_d_e_subst_d_upper :
forall d1 u1 x1,
  e_fv_d (e_subst_d u1 x1 d1) [<=] e_fv_u u1 `union` remove x1 (e_fv_d d1).
Proof. Admitted.

Hint Resolve e_fv_d_e_subst_d_upper : lngen.

Lemma e_fv_e_e_subst_e_upper :
forall e1 u1 x1,
  e_fv_e (e_subst_e u1 x1 e1) [<=] e_fv_u u1 `union` remove x1 (e_fv_e e1).
Proof. Admitted.

Hint Resolve e_fv_e_e_subst_e_upper : lngen.

Lemma e_fv_u_e_subst_u_upper :
forall u1 u2 x1,
  e_fv_u (e_subst_u u2 x1 u1) [<=] e_fv_u u2 `union` remove x1 (e_fv_u u1).
Proof. Admitted.

Hint Resolve e_fv_u_e_subst_u_upper : lngen.

Lemma e_fv_v_e_subst_v_upper :
forall v1 u1 x1,
  e_fv_v (e_subst_v u1 x1 v1) [<=] e_fv_u u1 `union` remove x1 (e_fv_v v1).
Proof. Admitted.

Hint Resolve e_fv_v_e_subst_v_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma t_subst_t_close_t_wrt_t_rec_mutual :
(forall t2 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_t t1 a1 (close_t_wrt_t_rec n1 a2 t2) = close_t_wrt_t_rec n1 a2 (t_subst_t t1 a1 t2)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_t_close_t_wrt_t_rec :
forall t2 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_t t1 a1 (close_t_wrt_t_rec n1 a2 t2) = close_t_wrt_t_rec n1 a2 (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_t_close_t_wrt_t_rec : lngen.

(* begin hide *)

Lemma t_subst_d_close_d_wrt_t_rec_t_subst_e_close_e_wrt_t_rec_t_subst_u_close_u_wrt_t_rec_t_subst_v_close_v_wrt_t_rec_mutual :
(forall d1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_d t1 a1 (close_d_wrt_t_rec n1 a2 d1) = close_d_wrt_t_rec n1 a2 (t_subst_d t1 a1 d1)) /\
(forall e1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_e t1 a1 (close_e_wrt_t_rec n1 a2 e1) = close_e_wrt_t_rec n1 a2 (t_subst_e t1 a1 e1)) /\
(forall u1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_u t1 a1 (close_u_wrt_t_rec n1 a2 u1) = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 u1)) /\
(forall v1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_v t1 a1 (close_v_wrt_t_rec n1 a2 v1) = close_v_wrt_t_rec n1 a2 (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_d_close_d_wrt_t_rec :
forall d1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_d t1 a1 (close_d_wrt_t_rec n1 a2 d1) = close_d_wrt_t_rec n1 a2 (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_close_d_wrt_t_rec : lngen.

Lemma t_subst_e_close_e_wrt_t_rec :
forall e1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_e t1 a1 (close_e_wrt_t_rec n1 a2 e1) = close_e_wrt_t_rec n1 a2 (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_close_e_wrt_t_rec : lngen.

Lemma t_subst_u_close_u_wrt_t_rec :
forall u1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_u t1 a1 (close_u_wrt_t_rec n1 a2 u1) = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_t_rec : lngen.

Lemma t_subst_v_close_v_wrt_t_rec :
forall v1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_v t1 a1 (close_v_wrt_t_rec n1 a2 v1) = close_v_wrt_t_rec n1 a2 (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_close_v_wrt_t_rec : lngen.

(* begin hide *)

Lemma t_subst_d_close_d_wrt_u_rec_t_subst_e_close_e_wrt_u_rec_t_subst_u_close_u_wrt_u_rec_t_subst_v_close_v_wrt_u_rec_mutual :
(forall d1 t1 x1 a1 n1,
  t_subst_d t1 x1 (close_d_wrt_u_rec n1 a1 d1) = close_d_wrt_u_rec n1 a1 (t_subst_d t1 x1 d1)) /\
(forall e1 t1 x1 a1 n1,
  t_subst_e t1 x1 (close_e_wrt_u_rec n1 a1 e1) = close_e_wrt_u_rec n1 a1 (t_subst_e t1 x1 e1)) /\
(forall u1 t1 x1 a1 n1,
  t_subst_u t1 x1 (close_u_wrt_u_rec n1 a1 u1) = close_u_wrt_u_rec n1 a1 (t_subst_u t1 x1 u1)) /\
(forall v1 t1 x1 a1 n1,
  t_subst_v t1 x1 (close_v_wrt_u_rec n1 a1 v1) = close_v_wrt_u_rec n1 a1 (t_subst_v t1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_d_close_d_wrt_u_rec :
forall d1 t1 x1 a1 n1,
  t_subst_d t1 x1 (close_d_wrt_u_rec n1 a1 d1) = close_d_wrt_u_rec n1 a1 (t_subst_d t1 x1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_close_d_wrt_u_rec : lngen.

Lemma t_subst_e_close_e_wrt_u_rec :
forall e1 t1 x1 a1 n1,
  t_subst_e t1 x1 (close_e_wrt_u_rec n1 a1 e1) = close_e_wrt_u_rec n1 a1 (t_subst_e t1 x1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_close_e_wrt_u_rec : lngen.

Lemma t_subst_u_close_u_wrt_u_rec :
forall u1 t1 x1 a1 n1,
  t_subst_u t1 x1 (close_u_wrt_u_rec n1 a1 u1) = close_u_wrt_u_rec n1 a1 (t_subst_u t1 x1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_u_rec : lngen.

Lemma t_subst_v_close_v_wrt_u_rec :
forall v1 t1 x1 a1 n1,
  t_subst_v t1 x1 (close_v_wrt_u_rec n1 a1 v1) = close_v_wrt_u_rec n1 a1 (t_subst_v t1 x1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_close_v_wrt_u_rec : lngen.

(* begin hide *)

Lemma e_subst_d_close_d_wrt_t_rec_e_subst_e_close_e_wrt_t_rec_e_subst_u_close_u_wrt_t_rec_e_subst_v_close_v_wrt_t_rec_mutual :
(forall d1 u1 a1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  x1 `notin` tt_fv_u u1 ->
  e_subst_d u1 a1 (close_d_wrt_t_rec n1 x1 d1) = close_d_wrt_t_rec n1 x1 (e_subst_d u1 a1 d1)) /\
(forall e1 u1 a1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  x1 `notin` tt_fv_u u1 ->
  e_subst_e u1 a1 (close_e_wrt_t_rec n1 x1 e1) = close_e_wrt_t_rec n1 x1 (e_subst_e u1 a1 e1)) /\
(forall u2 u1 a1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  x1 `notin` tt_fv_u u1 ->
  e_subst_u u1 a1 (close_u_wrt_t_rec n1 x1 u2) = close_u_wrt_t_rec n1 x1 (e_subst_u u1 a1 u2)) /\
(forall v1 u1 a1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  x1 `notin` tt_fv_u u1 ->
  e_subst_v u1 a1 (close_v_wrt_t_rec n1 x1 v1) = close_v_wrt_t_rec n1 x1 (e_subst_v u1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_d_close_d_wrt_t_rec :
forall d1 u1 a1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  x1 `notin` tt_fv_u u1 ->
  e_subst_d u1 a1 (close_d_wrt_t_rec n1 x1 d1) = close_d_wrt_t_rec n1 x1 (e_subst_d u1 a1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_close_d_wrt_t_rec : lngen.

Lemma e_subst_e_close_e_wrt_t_rec :
forall e1 u1 a1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  x1 `notin` tt_fv_u u1 ->
  e_subst_e u1 a1 (close_e_wrt_t_rec n1 x1 e1) = close_e_wrt_t_rec n1 x1 (e_subst_e u1 a1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_close_e_wrt_t_rec : lngen.

Lemma e_subst_u_close_u_wrt_t_rec :
forall u2 u1 a1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  x1 `notin` tt_fv_u u1 ->
  e_subst_u u1 a1 (close_u_wrt_t_rec n1 x1 u2) = close_u_wrt_t_rec n1 x1 (e_subst_u u1 a1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_t_rec : lngen.

Lemma e_subst_v_close_v_wrt_t_rec :
forall v1 u1 a1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  x1 `notin` tt_fv_u u1 ->
  e_subst_v u1 a1 (close_v_wrt_t_rec n1 x1 v1) = close_v_wrt_t_rec n1 x1 (e_subst_v u1 a1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_close_v_wrt_t_rec : lngen.

(* begin hide *)

Lemma e_subst_d_close_d_wrt_u_rec_e_subst_e_close_e_wrt_u_rec_e_subst_u_close_u_wrt_u_rec_e_subst_v_close_v_wrt_u_rec_mutual :
(forall d1 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_d u1 x1 (close_d_wrt_u_rec n1 x2 d1) = close_d_wrt_u_rec n1 x2 (e_subst_d u1 x1 d1)) /\
(forall e1 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_e u1 x1 (close_e_wrt_u_rec n1 x2 e1) = close_e_wrt_u_rec n1 x2 (e_subst_e u1 x1 e1)) /\
(forall u2 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_u u1 x1 (close_u_wrt_u_rec n1 x2 u2) = close_u_wrt_u_rec n1 x2 (e_subst_u u1 x1 u2)) /\
(forall v1 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_v u1 x1 (close_v_wrt_u_rec n1 x2 v1) = close_v_wrt_u_rec n1 x2 (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_d_close_d_wrt_u_rec :
forall d1 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_d u1 x1 (close_d_wrt_u_rec n1 x2 d1) = close_d_wrt_u_rec n1 x2 (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_close_d_wrt_u_rec : lngen.

Lemma e_subst_e_close_e_wrt_u_rec :
forall e1 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_e u1 x1 (close_e_wrt_u_rec n1 x2 e1) = close_e_wrt_u_rec n1 x2 (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_close_e_wrt_u_rec : lngen.

Lemma e_subst_u_close_u_wrt_u_rec :
forall u2 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_u u1 x1 (close_u_wrt_u_rec n1 x2 u2) = close_u_wrt_u_rec n1 x2 (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_u_rec : lngen.

Lemma e_subst_v_close_v_wrt_u_rec :
forall v1 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_v u1 x1 (close_v_wrt_u_rec n1 x2 v1) = close_v_wrt_u_rec n1 x2 (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_close_v_wrt_u_rec : lngen.

Lemma t_subst_t_close_t_wrt_t :
forall t2 t1 a1 a2,
  lc_t t1 ->  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_t t1 a1 (close_t_wrt_t a2 t2) = close_t_wrt_t a2 (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_t_close_t_wrt_t : lngen.

Lemma t_subst_d_close_d_wrt_t :
forall d1 t1 a1 a2,
  lc_t t1 ->  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_d t1 a1 (close_d_wrt_t a2 d1) = close_d_wrt_t a2 (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_close_d_wrt_t : lngen.

Lemma t_subst_e_close_e_wrt_t :
forall e1 t1 a1 a2,
  lc_t t1 ->  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_e t1 a1 (close_e_wrt_t a2 e1) = close_e_wrt_t a2 (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_close_e_wrt_t : lngen.

Lemma t_subst_u_close_u_wrt_t :
forall u1 t1 a1 a2,
  lc_t t1 ->  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_u t1 a1 (close_u_wrt_t a2 u1) = close_u_wrt_t a2 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_t : lngen.

Lemma t_subst_v_close_v_wrt_t :
forall v1 t1 a1 a2,
  lc_t t1 ->  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_v t1 a1 (close_v_wrt_t a2 v1) = close_v_wrt_t a2 (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_close_v_wrt_t : lngen.

Lemma t_subst_d_close_d_wrt_u :
forall d1 t1 x1 a1,
  lc_t t1 ->  t_subst_d t1 x1 (close_d_wrt_u a1 d1) = close_d_wrt_u a1 (t_subst_d t1 x1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_close_d_wrt_u : lngen.

Lemma t_subst_e_close_e_wrt_u :
forall e1 t1 x1 a1,
  lc_t t1 ->  t_subst_e t1 x1 (close_e_wrt_u a1 e1) = close_e_wrt_u a1 (t_subst_e t1 x1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_close_e_wrt_u : lngen.

Lemma t_subst_u_close_u_wrt_u :
forall u1 t1 x1 a1,
  lc_t t1 ->  t_subst_u t1 x1 (close_u_wrt_u a1 u1) = close_u_wrt_u a1 (t_subst_u t1 x1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_u : lngen.

Lemma t_subst_v_close_v_wrt_u :
forall v1 t1 x1 a1,
  lc_t t1 ->  t_subst_v t1 x1 (close_v_wrt_u a1 v1) = close_v_wrt_u a1 (t_subst_v t1 x1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_close_v_wrt_u : lngen.

Lemma e_subst_d_close_d_wrt_t :
forall d1 u1 a1 x1,
  lc_u u1 ->  x1 `notin` tt_fv_u u1 ->
  e_subst_d u1 a1 (close_d_wrt_t x1 d1) = close_d_wrt_t x1 (e_subst_d u1 a1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_close_d_wrt_t : lngen.

Lemma e_subst_e_close_e_wrt_t :
forall e1 u1 a1 x1,
  lc_u u1 ->  x1 `notin` tt_fv_u u1 ->
  e_subst_e u1 a1 (close_e_wrt_t x1 e1) = close_e_wrt_t x1 (e_subst_e u1 a1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_close_e_wrt_t : lngen.

Lemma e_subst_u_close_u_wrt_t :
forall u2 u1 a1 x1,
  lc_u u1 ->  x1 `notin` tt_fv_u u1 ->
  e_subst_u u1 a1 (close_u_wrt_t x1 u2) = close_u_wrt_t x1 (e_subst_u u1 a1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_t : lngen.

Lemma e_subst_v_close_v_wrt_t :
forall v1 u1 a1 x1,
  lc_u u1 ->  x1 `notin` tt_fv_u u1 ->
  e_subst_v u1 a1 (close_v_wrt_t x1 v1) = close_v_wrt_t x1 (e_subst_v u1 a1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_close_v_wrt_t : lngen.

Lemma e_subst_d_close_d_wrt_u :
forall d1 u1 x1 x2,
  lc_u u1 ->  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_d u1 x1 (close_d_wrt_u x2 d1) = close_d_wrt_u x2 (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_close_d_wrt_u : lngen.

Lemma e_subst_e_close_e_wrt_u :
forall e1 u1 x1 x2,
  lc_u u1 ->  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_e u1 x1 (close_e_wrt_u x2 e1) = close_e_wrt_u x2 (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_close_e_wrt_u : lngen.

Lemma e_subst_u_close_u_wrt_u :
forall u2 u1 x1 x2,
  lc_u u1 ->  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_u u1 x1 (close_u_wrt_u x2 u2) = close_u_wrt_u x2 (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_u : lngen.

Lemma e_subst_v_close_v_wrt_u :
forall v1 u1 x1 x2,
  lc_u u1 ->  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_v u1 x1 (close_v_wrt_u x2 v1) = close_v_wrt_u x2 (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_close_v_wrt_u : lngen.

(* begin hide *)

Lemma t_subst_t_degree_t_wrt_t_mutual :
(forall t1 t2 a1 n1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t n1 t2 ->
  degree_t_wrt_t n1 (t_subst_t t2 a1 t1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_t_degree_t_wrt_t :
forall t1 t2 a1 n1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t n1 t2 ->
  degree_t_wrt_t n1 (t_subst_t t2 a1 t1).
Proof. Admitted.

Hint Resolve t_subst_t_degree_t_wrt_t : lngen.

(* begin hide *)

Lemma t_subst_d_degree_d_wrt_t_t_subst_e_degree_e_wrt_t_t_subst_u_degree_u_wrt_t_t_subst_v_degree_v_wrt_t_mutual :
(forall d1 t1 a1 n1,
  degree_d_wrt_t n1 d1 ->
  degree_t_wrt_t n1 t1 ->
  degree_d_wrt_t n1 (t_subst_d t1 a1 d1)) /\
(forall e1 t1 a1 n1,
  degree_e_wrt_t n1 e1 ->
  degree_t_wrt_t n1 t1 ->
  degree_e_wrt_t n1 (t_subst_e t1 a1 e1)) /\
(forall u1 t1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (t_subst_u t1 a1 u1)) /\
(forall v1 t1 a1 n1,
  degree_v_wrt_t n1 v1 ->
  degree_t_wrt_t n1 t1 ->
  degree_v_wrt_t n1 (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_d_degree_d_wrt_t :
forall d1 t1 a1 n1,
  degree_d_wrt_t n1 d1 ->
  degree_t_wrt_t n1 t1 ->
  degree_d_wrt_t n1 (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_degree_d_wrt_t : lngen.

Lemma t_subst_e_degree_e_wrt_t :
forall e1 t1 a1 n1,
  degree_e_wrt_t n1 e1 ->
  degree_t_wrt_t n1 t1 ->
  degree_e_wrt_t n1 (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_degree_e_wrt_t : lngen.

Lemma t_subst_u_degree_u_wrt_t :
forall u1 t1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_degree_u_wrt_t : lngen.

Lemma t_subst_v_degree_v_wrt_t :
forall v1 t1 a1 n1,
  degree_v_wrt_t n1 v1 ->
  degree_t_wrt_t n1 t1 ->
  degree_v_wrt_t n1 (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_degree_v_wrt_t : lngen.

(* begin hide *)

Lemma t_subst_d_degree_d_wrt_u_t_subst_e_degree_e_wrt_u_t_subst_u_degree_u_wrt_u_t_subst_v_degree_v_wrt_u_mutual :
(forall d1 t1 a1 n1,
  degree_d_wrt_u n1 d1 ->
  degree_d_wrt_u n1 (t_subst_d t1 a1 d1)) /\
(forall e1 t1 a1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u n1 (t_subst_e t1 a1 e1)) /\
(forall u1 t1 a1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (t_subst_u t1 a1 u1)) /\
(forall v1 t1 a1 n1,
  degree_v_wrt_u n1 v1 ->
  degree_v_wrt_u n1 (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_d_degree_d_wrt_u :
forall d1 t1 a1 n1,
  degree_d_wrt_u n1 d1 ->
  degree_d_wrt_u n1 (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_degree_d_wrt_u : lngen.

Lemma t_subst_e_degree_e_wrt_u :
forall e1 t1 a1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u n1 (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_degree_e_wrt_u : lngen.

Lemma t_subst_u_degree_u_wrt_u :
forall u1 t1 a1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_degree_u_wrt_u : lngen.

Lemma t_subst_v_degree_v_wrt_u :
forall v1 t1 a1 n1,
  degree_v_wrt_u n1 v1 ->
  degree_v_wrt_u n1 (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_degree_v_wrt_u : lngen.

(* begin hide *)

Lemma e_subst_d_degree_d_wrt_t_e_subst_e_degree_e_wrt_t_e_subst_u_degree_u_wrt_t_e_subst_v_degree_v_wrt_t_mutual :
(forall d1 u1 x1 n1,
  degree_d_wrt_t n1 d1 ->
  degree_u_wrt_t n1 u1 ->
  degree_d_wrt_t n1 (e_subst_d u1 x1 d1)) /\
(forall e1 u1 x1 n1,
  degree_e_wrt_t n1 e1 ->
  degree_u_wrt_t n1 u1 ->
  degree_e_wrt_t n1 (e_subst_e u1 x1 e1)) /\
(forall u1 u2 x1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 u2 ->
  degree_u_wrt_t n1 (e_subst_u u2 x1 u1)) /\
(forall v1 u1 x1 n1,
  degree_v_wrt_t n1 v1 ->
  degree_u_wrt_t n1 u1 ->
  degree_v_wrt_t n1 (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_d_degree_d_wrt_t :
forall d1 u1 x1 n1,
  degree_d_wrt_t n1 d1 ->
  degree_u_wrt_t n1 u1 ->
  degree_d_wrt_t n1 (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_degree_d_wrt_t : lngen.

Lemma e_subst_e_degree_e_wrt_t :
forall e1 u1 x1 n1,
  degree_e_wrt_t n1 e1 ->
  degree_u_wrt_t n1 u1 ->
  degree_e_wrt_t n1 (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_degree_e_wrt_t : lngen.

Lemma e_subst_u_degree_u_wrt_t :
forall u1 u2 x1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 u2 ->
  degree_u_wrt_t n1 (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_degree_u_wrt_t : lngen.

Lemma e_subst_v_degree_v_wrt_t :
forall v1 u1 x1 n1,
  degree_v_wrt_t n1 v1 ->
  degree_u_wrt_t n1 u1 ->
  degree_v_wrt_t n1 (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_degree_v_wrt_t : lngen.

(* begin hide *)

Lemma e_subst_d_degree_d_wrt_u_e_subst_e_degree_e_wrt_u_e_subst_u_degree_u_wrt_u_e_subst_v_degree_v_wrt_u_mutual :
(forall d1 u1 x1 n1,
  degree_d_wrt_u n1 d1 ->
  degree_u_wrt_u n1 u1 ->
  degree_d_wrt_u n1 (e_subst_d u1 x1 d1)) /\
(forall e1 u1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_u_wrt_u n1 u1 ->
  degree_e_wrt_u n1 (e_subst_e u1 x1 e1)) /\
(forall u1 u2 x1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 u2 ->
  degree_u_wrt_u n1 (e_subst_u u2 x1 u1)) /\
(forall v1 u1 x1 n1,
  degree_v_wrt_u n1 v1 ->
  degree_u_wrt_u n1 u1 ->
  degree_v_wrt_u n1 (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_d_degree_d_wrt_u :
forall d1 u1 x1 n1,
  degree_d_wrt_u n1 d1 ->
  degree_u_wrt_u n1 u1 ->
  degree_d_wrt_u n1 (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_degree_d_wrt_u : lngen.

Lemma e_subst_e_degree_e_wrt_u :
forall e1 u1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_u_wrt_u n1 u1 ->
  degree_e_wrt_u n1 (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_degree_e_wrt_u : lngen.

Lemma e_subst_u_degree_u_wrt_u :
forall u1 u2 x1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 u2 ->
  degree_u_wrt_u n1 (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_degree_u_wrt_u : lngen.

Lemma e_subst_v_degree_v_wrt_u :
forall v1 u1 x1 n1,
  degree_v_wrt_u n1 v1 ->
  degree_u_wrt_u n1 u1 ->
  degree_v_wrt_u n1 (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_degree_v_wrt_u : lngen.

(* begin hide *)

Lemma t_subst_t_fresh_eq_mutual :
(forall t2 t1 a1,
  a1 `notin` tt_fv_t t2 ->
  t_subst_t t1 a1 t2 = t2).
Proof. Admitted.

(* end hide *)

Lemma t_subst_t_fresh_eq :
forall t2 t1 a1,
  a1 `notin` tt_fv_t t2 ->
  t_subst_t t1 a1 t2 = t2.
Proof. Admitted.

Hint Resolve t_subst_t_fresh_eq : lngen.
Hint Rewrite t_subst_t_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_d_fresh_eq_t_subst_e_fresh_eq_t_subst_u_fresh_eq_t_subst_v_fresh_eq_mutual :
(forall d1 t1 a1,
  a1 `notin` tt_fv_d d1 ->
  t_subst_d t1 a1 d1 = d1) /\
(forall e1 t1 a1,
  a1 `notin` tt_fv_e e1 ->
  t_subst_e t1 a1 e1 = e1) /\
(forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  t_subst_u t1 a1 u1 = u1) /\
(forall v1 t1 a1,
  a1 `notin` tt_fv_v v1 ->
  t_subst_v t1 a1 v1 = v1).
Proof. Admitted.

(* end hide *)

Lemma t_subst_d_fresh_eq :
forall d1 t1 a1,
  a1 `notin` tt_fv_d d1 ->
  t_subst_d t1 a1 d1 = d1.
Proof. Admitted.

Hint Resolve t_subst_d_fresh_eq : lngen.
Hint Rewrite t_subst_d_fresh_eq using solve [auto] : lngen.

Lemma t_subst_e_fresh_eq :
forall e1 t1 a1,
  a1 `notin` tt_fv_e e1 ->
  t_subst_e t1 a1 e1 = e1.
Proof. Admitted.

Hint Resolve t_subst_e_fresh_eq : lngen.
Hint Rewrite t_subst_e_fresh_eq using solve [auto] : lngen.

Lemma t_subst_u_fresh_eq :
forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  t_subst_u t1 a1 u1 = u1.
Proof. Admitted.

Hint Resolve t_subst_u_fresh_eq : lngen.
Hint Rewrite t_subst_u_fresh_eq using solve [auto] : lngen.

Lemma t_subst_v_fresh_eq :
forall v1 t1 a1,
  a1 `notin` tt_fv_v v1 ->
  t_subst_v t1 a1 v1 = v1.
Proof. Admitted.

Hint Resolve t_subst_v_fresh_eq : lngen.
Hint Rewrite t_subst_v_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma e_subst_d_fresh_eq_e_subst_e_fresh_eq_e_subst_u_fresh_eq_e_subst_v_fresh_eq_mutual :
(forall d1 u1 x1,
  x1 `notin` e_fv_d d1 ->
  e_subst_d u1 x1 d1 = d1) /\
(forall e1 u1 x1,
  x1 `notin` e_fv_e e1 ->
  e_subst_e u1 x1 e1 = e1) /\
(forall u2 u1 x1,
  x1 `notin` e_fv_u u2 ->
  e_subst_u u1 x1 u2 = u2) /\
(forall v1 u1 x1,
  x1 `notin` e_fv_v v1 ->
  e_subst_v u1 x1 v1 = v1).
Proof. Admitted.

(* end hide *)

Lemma e_subst_d_fresh_eq :
forall d1 u1 x1,
  x1 `notin` e_fv_d d1 ->
  e_subst_d u1 x1 d1 = d1.
Proof. Admitted.

Hint Resolve e_subst_d_fresh_eq : lngen.
Hint Rewrite e_subst_d_fresh_eq using solve [auto] : lngen.

Lemma e_subst_e_fresh_eq :
forall e1 u1 x1,
  x1 `notin` e_fv_e e1 ->
  e_subst_e u1 x1 e1 = e1.
Proof. Admitted.

Hint Resolve e_subst_e_fresh_eq : lngen.
Hint Rewrite e_subst_e_fresh_eq using solve [auto] : lngen.

Lemma e_subst_u_fresh_eq :
forall u2 u1 x1,
  x1 `notin` e_fv_u u2 ->
  e_subst_u u1 x1 u2 = u2.
Proof. Admitted.

Hint Resolve e_subst_u_fresh_eq : lngen.
Hint Rewrite e_subst_u_fresh_eq using solve [auto] : lngen.

Lemma e_subst_v_fresh_eq :
forall v1 u1 x1,
  x1 `notin` e_fv_v v1 ->
  e_subst_v u1 x1 v1 = v1.
Proof. Admitted.

Hint Resolve e_subst_v_fresh_eq : lngen.
Hint Rewrite e_subst_v_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_t_fresh_same_mutual :
(forall t2 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_t (t_subst_t t1 a1 t2)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_t_fresh_same :
forall t2 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_t (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_t_fresh_same : lngen.

(* begin hide *)

Lemma t_subst_d_fresh_same_t_subst_e_fresh_same_t_subst_u_fresh_same_t_subst_v_fresh_same_mutual :
(forall d1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_d (t_subst_d t1 a1 d1)) /\
(forall e1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_e (t_subst_e t1 a1 e1)) /\
(forall u1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a1 u1)) /\
(forall v1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_v (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_d_fresh_same :
forall d1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_d (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_fresh_same : lngen.

Lemma t_subst_e_fresh_same :
forall e1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_e (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_fresh_same : lngen.

Lemma t_subst_u_fresh_same :
forall u1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_fresh_same : lngen.

Lemma t_subst_v_fresh_same :
forall v1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_v (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_fresh_same : lngen.

(* begin hide *)

Lemma e_subst_d_fresh_same_e_subst_e_fresh_same_e_subst_u_fresh_same_e_subst_v_fresh_same_mutual :
(forall d1 u1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_d (e_subst_d u1 x1 d1)) /\
(forall e1 u1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_e (e_subst_e u1 x1 e1)) /\
(forall u2 u1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (e_subst_u u1 x1 u2)) /\
(forall v1 u1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_v (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_d_fresh_same :
forall d1 u1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_d (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_fresh_same : lngen.

Lemma e_subst_e_fresh_same :
forall e1 u1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_e (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_fresh_same : lngen.

Lemma e_subst_u_fresh_same :
forall u2 u1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_fresh_same : lngen.

Lemma e_subst_v_fresh_same :
forall v1 u1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_v (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_fresh_same : lngen.

(* begin hide *)

Lemma t_subst_t_fresh_mutual :
(forall t2 t1 a1 a2,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_t (t_subst_t t1 a2 t2)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_t_fresh :
forall t2 t1 a1 a2,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_t (t_subst_t t1 a2 t2).
Proof. Admitted.

Hint Resolve t_subst_t_fresh : lngen.

(* begin hide *)

Lemma t_subst_d_fresh_t_subst_e_fresh_t_subst_u_fresh_t_subst_v_fresh_mutual :
(forall d1 t1 a1 a2,
  a1 `notin` tt_fv_d d1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_d (t_subst_d t1 a2 d1)) /\
(forall e1 t1 a1 a2,
  a1 `notin` tt_fv_e e1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_e (t_subst_e t1 a2 e1)) /\
(forall u1 t1 a1 a2,
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a2 u1)) /\
(forall v1 t1 a1 a2,
  a1 `notin` tt_fv_v v1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_v (t_subst_v t1 a2 v1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_d_fresh :
forall d1 t1 a1 a2,
  a1 `notin` tt_fv_d d1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_d (t_subst_d t1 a2 d1).
Proof. Admitted.

Hint Resolve t_subst_d_fresh : lngen.

Lemma t_subst_e_fresh :
forall e1 t1 a1 a2,
  a1 `notin` tt_fv_e e1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_e (t_subst_e t1 a2 e1).
Proof. Admitted.

Hint Resolve t_subst_e_fresh : lngen.

Lemma t_subst_u_fresh :
forall u1 t1 a1 a2,
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a2 u1).
Proof. Admitted.

Hint Resolve t_subst_u_fresh : lngen.

Lemma t_subst_v_fresh :
forall v1 t1 a1 a2,
  a1 `notin` tt_fv_v v1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_v (t_subst_v t1 a2 v1).
Proof. Admitted.

Hint Resolve t_subst_v_fresh : lngen.

(* begin hide *)

Lemma e_subst_d_fresh_e_subst_e_fresh_e_subst_u_fresh_e_subst_v_fresh_mutual :
(forall d1 u1 x1 x2,
  x1 `notin` e_fv_d d1 ->
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_d (e_subst_d u1 x2 d1)) /\
(forall e1 u1 x1 x2,
  x1 `notin` e_fv_e e1 ->
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_e (e_subst_e u1 x2 e1)) /\
(forall u2 u1 x1 x2,
  x1 `notin` e_fv_u u2 ->
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (e_subst_u u1 x2 u2)) /\
(forall v1 u1 x1 x2,
  x1 `notin` e_fv_v v1 ->
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_v (e_subst_v u1 x2 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_d_fresh :
forall d1 u1 x1 x2,
  x1 `notin` e_fv_d d1 ->
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_d (e_subst_d u1 x2 d1).
Proof. Admitted.

Hint Resolve e_subst_d_fresh : lngen.

Lemma e_subst_e_fresh :
forall e1 u1 x1 x2,
  x1 `notin` e_fv_e e1 ->
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_e (e_subst_e u1 x2 e1).
Proof. Admitted.

Hint Resolve e_subst_e_fresh : lngen.

Lemma e_subst_u_fresh :
forall u2 u1 x1 x2,
  x1 `notin` e_fv_u u2 ->
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (e_subst_u u1 x2 u2).
Proof. Admitted.

Hint Resolve e_subst_u_fresh : lngen.

Lemma e_subst_v_fresh :
forall v1 u1 x1 x2,
  x1 `notin` e_fv_v v1 ->
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_v (e_subst_v u1 x2 v1).
Proof. Admitted.

Hint Resolve e_subst_v_fresh : lngen.

Lemma t_subst_t_lc_t :
forall t1 t2 a1,
  lc_t t1 ->
  lc_t t2 ->
  lc_t (t_subst_t t2 a1 t1).
Proof. Admitted.

Hint Resolve t_subst_t_lc_t : lngen.

Lemma t_subst_d_lc_d :
forall d1 t1 a1,
  lc_d d1 ->
  lc_t t1 ->
  lc_d (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_lc_d : lngen.

Lemma t_subst_e_lc_e :
forall e1 t1 a1,
  lc_e e1 ->
  lc_t t1 ->
  lc_e (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_lc_e : lngen.

Lemma t_subst_u_lc_u :
forall u1 t1 a1,
  lc_u u1 ->
  lc_t t1 ->
  lc_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_lc_u : lngen.

Lemma t_subst_v_lc_v :
forall v1 t1 a1,
  lc_v v1 ->
  lc_t t1 ->
  lc_v (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_lc_v : lngen.

Lemma e_subst_d_lc_d :
forall d1 u1 x1,
  lc_d d1 ->
  lc_u u1 ->
  lc_d (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_lc_d : lngen.

Lemma e_subst_e_lc_e :
forall e1 u1 x1,
  lc_e e1 ->
  lc_u u1 ->
  lc_e (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_lc_e : lngen.

Lemma e_subst_u_lc_u :
forall u1 u2 x1,
  lc_u u1 ->
  lc_u u2 ->
  lc_u (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_lc_u : lngen.

Lemma e_subst_v_lc_v :
forall v1 u1 x1,
  lc_v v1 ->
  lc_u u1 ->
  lc_v (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_lc_v : lngen.

(* begin hide *)

Lemma t_subst_t_open_t_wrt_t_rec_mutual :
(forall t3 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_t t1 a1 (open_t_wrt_t_rec n1 t2 t3) = open_t_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_t t1 a1 t3)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_t_open_t_wrt_t_rec :
forall t3 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_t t1 a1 (open_t_wrt_t_rec n1 t2 t3) = open_t_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_t t1 a1 t3).
Proof. Admitted.

Hint Resolve t_subst_t_open_t_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_d_open_d_wrt_t_rec_t_subst_e_open_e_wrt_t_rec_t_subst_u_open_u_wrt_t_rec_t_subst_v_open_v_wrt_t_rec_mutual :
(forall d1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_d t1 a1 (open_d_wrt_t_rec n1 t2 d1) = open_d_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_d t1 a1 d1)) /\
(forall e1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_e t1 a1 (open_e_wrt_t_rec n1 t2 e1) = open_e_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_e t1 a1 e1)) /\
(forall u1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_u t1 a1 (open_u_wrt_t_rec n1 t2 u1) = open_u_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_u t1 a1 u1)) /\
(forall v1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_v t1 a1 (open_v_wrt_t_rec n1 t2 v1) = open_v_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_d_open_d_wrt_t_rec :
forall d1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_d t1 a1 (open_d_wrt_t_rec n1 t2 d1) = open_d_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_open_d_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_e_open_e_wrt_t_rec :
forall e1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_e t1 a1 (open_e_wrt_t_rec n1 t2 e1) = open_e_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_open_e_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_open_u_wrt_t_rec :
forall u1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_u t1 a1 (open_u_wrt_t_rec n1 t2 u1) = open_u_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_v_open_v_wrt_t_rec :
forall v1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_v t1 a1 (open_v_wrt_t_rec n1 t2 v1) = open_v_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_open_v_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_d_open_d_wrt_u_rec_t_subst_e_open_e_wrt_u_rec_t_subst_u_open_u_wrt_u_rec_t_subst_v_open_v_wrt_u_rec_mutual :
(forall d1 t1 u1 a1 n1,
  t_subst_d t1 a1 (open_d_wrt_u_rec n1 u1 d1) = open_d_wrt_u_rec n1 (t_subst_u t1 a1 u1) (t_subst_d t1 a1 d1)) /\
(forall e1 t1 u1 a1 n1,
  t_subst_e t1 a1 (open_e_wrt_u_rec n1 u1 e1) = open_e_wrt_u_rec n1 (t_subst_u t1 a1 u1) (t_subst_e t1 a1 e1)) /\
(forall u2 t1 u1 a1 n1,
  t_subst_u t1 a1 (open_u_wrt_u_rec n1 u1 u2) = open_u_wrt_u_rec n1 (t_subst_u t1 a1 u1) (t_subst_u t1 a1 u2)) /\
(forall v1 t1 u1 a1 n1,
  t_subst_v t1 a1 (open_v_wrt_u_rec n1 u1 v1) = open_v_wrt_u_rec n1 (t_subst_u t1 a1 u1) (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_d_open_d_wrt_u_rec :
forall d1 t1 u1 a1 n1,
  t_subst_d t1 a1 (open_d_wrt_u_rec n1 u1 d1) = open_d_wrt_u_rec n1 (t_subst_u t1 a1 u1) (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_open_d_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_e_open_e_wrt_u_rec :
forall e1 t1 u1 a1 n1,
  t_subst_e t1 a1 (open_e_wrt_u_rec n1 u1 e1) = open_e_wrt_u_rec n1 (t_subst_u t1 a1 u1) (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_open_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_open_u_wrt_u_rec :
forall u2 t1 u1 a1 n1,
  t_subst_u t1 a1 (open_u_wrt_u_rec n1 u1 u2) = open_u_wrt_u_rec n1 (t_subst_u t1 a1 u1) (t_subst_u t1 a1 u2).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_v_open_v_wrt_u_rec :
forall v1 t1 u1 a1 n1,
  t_subst_v t1 a1 (open_v_wrt_u_rec n1 u1 v1) = open_v_wrt_u_rec n1 (t_subst_u t1 a1 u1) (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_open_v_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_d_open_d_wrt_t_rec_e_subst_e_open_e_wrt_t_rec_e_subst_u_open_u_wrt_t_rec_e_subst_v_open_v_wrt_t_rec_mutual :
(forall d1 u1 t1 x1 n1,
  lc_u u1 ->
  e_subst_d u1 x1 (open_d_wrt_t_rec n1 t1 d1) = open_d_wrt_t_rec n1 t1 (e_subst_d u1 x1 d1)) /\
(forall e1 u1 t1 x1 n1,
  lc_u u1 ->
  e_subst_e u1 x1 (open_e_wrt_t_rec n1 t1 e1) = open_e_wrt_t_rec n1 t1 (e_subst_e u1 x1 e1)) /\
(forall u2 u1 t1 x1 n1,
  lc_u u1 ->
  e_subst_u u1 x1 (open_u_wrt_t_rec n1 t1 u2) = open_u_wrt_t_rec n1 t1 (e_subst_u u1 x1 u2)) /\
(forall v1 u1 t1 x1 n1,
  lc_u u1 ->
  e_subst_v u1 x1 (open_v_wrt_t_rec n1 t1 v1) = open_v_wrt_t_rec n1 t1 (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_d_open_d_wrt_t_rec :
forall d1 u1 t1 x1 n1,
  lc_u u1 ->
  e_subst_d u1 x1 (open_d_wrt_t_rec n1 t1 d1) = open_d_wrt_t_rec n1 t1 (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_open_d_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_e_open_e_wrt_t_rec :
forall e1 u1 t1 x1 n1,
  lc_u u1 ->
  e_subst_e u1 x1 (open_e_wrt_t_rec n1 t1 e1) = open_e_wrt_t_rec n1 t1 (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_open_e_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_u_open_u_wrt_t_rec :
forall u2 u1 t1 x1 n1,
  lc_u u1 ->
  e_subst_u u1 x1 (open_u_wrt_t_rec n1 t1 u2) = open_u_wrt_t_rec n1 t1 (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_open_u_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_v_open_v_wrt_t_rec :
forall v1 u1 t1 x1 n1,
  lc_u u1 ->
  e_subst_v u1 x1 (open_v_wrt_t_rec n1 t1 v1) = open_v_wrt_t_rec n1 t1 (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_open_v_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_d_open_d_wrt_u_rec_e_subst_e_open_e_wrt_u_rec_e_subst_u_open_u_wrt_u_rec_e_subst_v_open_v_wrt_u_rec_mutual :
(forall d1 u1 u2 x1 n1,
  lc_u u1 ->
  e_subst_d u1 x1 (open_d_wrt_u_rec n1 u2 d1) = open_d_wrt_u_rec n1 (e_subst_u u1 x1 u2) (e_subst_d u1 x1 d1)) /\
(forall e1 u1 u2 x1 n1,
  lc_u u1 ->
  e_subst_e u1 x1 (open_e_wrt_u_rec n1 u2 e1) = open_e_wrt_u_rec n1 (e_subst_u u1 x1 u2) (e_subst_e u1 x1 e1)) /\
(forall u3 u1 u2 x1 n1,
  lc_u u1 ->
  e_subst_u u1 x1 (open_u_wrt_u_rec n1 u2 u3) = open_u_wrt_u_rec n1 (e_subst_u u1 x1 u2) (e_subst_u u1 x1 u3)) /\
(forall v1 u1 u2 x1 n1,
  lc_u u1 ->
  e_subst_v u1 x1 (open_v_wrt_u_rec n1 u2 v1) = open_v_wrt_u_rec n1 (e_subst_u u1 x1 u2) (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_d_open_d_wrt_u_rec :
forall d1 u1 u2 x1 n1,
  lc_u u1 ->
  e_subst_d u1 x1 (open_d_wrt_u_rec n1 u2 d1) = open_d_wrt_u_rec n1 (e_subst_u u1 x1 u2) (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_open_d_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_e_open_e_wrt_u_rec :
forall e1 u1 u2 x1 n1,
  lc_u u1 ->
  e_subst_e u1 x1 (open_e_wrt_u_rec n1 u2 e1) = open_e_wrt_u_rec n1 (e_subst_u u1 x1 u2) (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_open_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_u_open_u_wrt_u_rec :
forall u3 u1 u2 x1 n1,
  lc_u u1 ->
  e_subst_u u1 x1 (open_u_wrt_u_rec n1 u2 u3) = open_u_wrt_u_rec n1 (e_subst_u u1 x1 u2) (e_subst_u u1 x1 u3).
Proof. Admitted.

Hint Resolve e_subst_u_open_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_v_open_v_wrt_u_rec :
forall v1 u1 u2 x1 n1,
  lc_u u1 ->
  e_subst_v u1 x1 (open_v_wrt_u_rec n1 u2 v1) = open_v_wrt_u_rec n1 (e_subst_u u1 x1 u2) (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_open_v_wrt_u_rec : lngen.

(* end hide *)

Lemma t_subst_t_open_t_wrt_t :
forall t3 t1 t2 a1,
  lc_t t1 ->
  t_subst_t t1 a1 (open_t_wrt_t t3 t2) = open_t_wrt_t (t_subst_t t1 a1 t3) (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_t_open_t_wrt_t : lngen.

Lemma t_subst_d_open_d_wrt_t :
forall d1 t1 t2 a1,
  lc_t t1 ->
  t_subst_d t1 a1 (open_d_wrt_t d1 t2) = open_d_wrt_t (t_subst_d t1 a1 d1) (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_d_open_d_wrt_t : lngen.

Lemma t_subst_e_open_e_wrt_t :
forall e1 t1 t2 a1,
  lc_t t1 ->
  t_subst_e t1 a1 (open_e_wrt_t e1 t2) = open_e_wrt_t (t_subst_e t1 a1 e1) (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_e_open_e_wrt_t : lngen.

Lemma t_subst_u_open_u_wrt_t :
forall u1 t1 t2 a1,
  lc_t t1 ->
  t_subst_u t1 a1 (open_u_wrt_t u1 t2) = open_u_wrt_t (t_subst_u t1 a1 u1) (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_t : lngen.

Lemma t_subst_v_open_v_wrt_t :
forall v1 t1 t2 a1,
  lc_t t1 ->
  t_subst_v t1 a1 (open_v_wrt_t v1 t2) = open_v_wrt_t (t_subst_v t1 a1 v1) (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_v_open_v_wrt_t : lngen.

Lemma t_subst_d_open_d_wrt_u :
forall d1 t1 u1 a1,
  t_subst_d t1 a1 (open_d_wrt_u d1 u1) = open_d_wrt_u (t_subst_d t1 a1 d1) (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_d_open_d_wrt_u : lngen.

Lemma t_subst_e_open_e_wrt_u :
forall e1 t1 u1 a1,
  t_subst_e t1 a1 (open_e_wrt_u e1 u1) = open_e_wrt_u (t_subst_e t1 a1 e1) (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_e_open_e_wrt_u : lngen.

Lemma t_subst_u_open_u_wrt_u :
forall u2 t1 u1 a1,
  t_subst_u t1 a1 (open_u_wrt_u u2 u1) = open_u_wrt_u (t_subst_u t1 a1 u2) (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_u : lngen.

Lemma t_subst_v_open_v_wrt_u :
forall v1 t1 u1 a1,
  t_subst_v t1 a1 (open_v_wrt_u v1 u1) = open_v_wrt_u (t_subst_v t1 a1 v1) (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_v_open_v_wrt_u : lngen.

Lemma e_subst_d_open_d_wrt_t :
forall d1 u1 t1 x1,
  lc_u u1 ->
  e_subst_d u1 x1 (open_d_wrt_t d1 t1) = open_d_wrt_t (e_subst_d u1 x1 d1) t1.
Proof. Admitted.

Hint Resolve e_subst_d_open_d_wrt_t : lngen.

Lemma e_subst_e_open_e_wrt_t :
forall e1 u1 t1 x1,
  lc_u u1 ->
  e_subst_e u1 x1 (open_e_wrt_t e1 t1) = open_e_wrt_t (e_subst_e u1 x1 e1) t1.
Proof. Admitted.

Hint Resolve e_subst_e_open_e_wrt_t : lngen.

Lemma e_subst_u_open_u_wrt_t :
forall u2 u1 t1 x1,
  lc_u u1 ->
  e_subst_u u1 x1 (open_u_wrt_t u2 t1) = open_u_wrt_t (e_subst_u u1 x1 u2) t1.
Proof. Admitted.

Hint Resolve e_subst_u_open_u_wrt_t : lngen.

Lemma e_subst_v_open_v_wrt_t :
forall v1 u1 t1 x1,
  lc_u u1 ->
  e_subst_v u1 x1 (open_v_wrt_t v1 t1) = open_v_wrt_t (e_subst_v u1 x1 v1) t1.
Proof. Admitted.

Hint Resolve e_subst_v_open_v_wrt_t : lngen.

Lemma e_subst_d_open_d_wrt_u :
forall d1 u1 u2 x1,
  lc_u u1 ->
  e_subst_d u1 x1 (open_d_wrt_u d1 u2) = open_d_wrt_u (e_subst_d u1 x1 d1) (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_d_open_d_wrt_u : lngen.

Lemma e_subst_e_open_e_wrt_u :
forall e1 u1 u2 x1,
  lc_u u1 ->
  e_subst_e u1 x1 (open_e_wrt_u e1 u2) = open_e_wrt_u (e_subst_e u1 x1 e1) (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_e_open_e_wrt_u : lngen.

Lemma e_subst_u_open_u_wrt_u :
forall u3 u1 u2 x1,
  lc_u u1 ->
  e_subst_u u1 x1 (open_u_wrt_u u3 u2) = open_u_wrt_u (e_subst_u u1 x1 u3) (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_open_u_wrt_u : lngen.

Lemma e_subst_v_open_v_wrt_u :
forall v1 u1 u2 x1,
  lc_u u1 ->
  e_subst_v u1 x1 (open_v_wrt_u v1 u2) = open_v_wrt_u (e_subst_v u1 x1 v1) (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_v_open_v_wrt_u : lngen.

Lemma t_subst_t_open_t_wrt_t_var :
forall t2 t1 a1 a2,
  a1 <> a2 ->
  lc_t t1 ->
  open_t_wrt_t (t_subst_t t1 a1 t2) (t_var_f a2) = t_subst_t t1 a1 (open_t_wrt_t t2 (t_var_f a2)).
Proof. Admitted.

Hint Resolve t_subst_t_open_t_wrt_t_var : lngen.

Lemma t_subst_d_open_d_wrt_t_var :
forall d1 t1 a1 a2,
  a1 <> a2 ->
  lc_t t1 ->
  open_d_wrt_t (t_subst_d t1 a1 d1) (t_var_f a2) = t_subst_d t1 a1 (open_d_wrt_t d1 (t_var_f a2)).
Proof. Admitted.

Hint Resolve t_subst_d_open_d_wrt_t_var : lngen.

Lemma t_subst_e_open_e_wrt_t_var :
forall e1 t1 a1 a2,
  a1 <> a2 ->
  lc_t t1 ->
  open_e_wrt_t (t_subst_e t1 a1 e1) (t_var_f a2) = t_subst_e t1 a1 (open_e_wrt_t e1 (t_var_f a2)).
Proof. Admitted.

Hint Resolve t_subst_e_open_e_wrt_t_var : lngen.

Lemma t_subst_u_open_u_wrt_t_var :
forall u1 t1 a1 a2,
  a1 <> a2 ->
  lc_t t1 ->
  open_u_wrt_t (t_subst_u t1 a1 u1) (t_var_f a2) = t_subst_u t1 a1 (open_u_wrt_t u1 (t_var_f a2)).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_t_var : lngen.

Lemma t_subst_v_open_v_wrt_t_var :
forall v1 t1 a1 a2,
  a1 <> a2 ->
  lc_t t1 ->
  open_v_wrt_t (t_subst_v t1 a1 v1) (t_var_f a2) = t_subst_v t1 a1 (open_v_wrt_t v1 (t_var_f a2)).
Proof. Admitted.

Hint Resolve t_subst_v_open_v_wrt_t_var : lngen.

Lemma t_subst_d_open_d_wrt_u_var :
forall d1 t1 a1 x1,
  open_d_wrt_u (t_subst_d t1 a1 d1) (u_var_f x1) = t_subst_d t1 a1 (open_d_wrt_u d1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve t_subst_d_open_d_wrt_u_var : lngen.

Lemma t_subst_e_open_e_wrt_u_var :
forall e1 t1 a1 x1,
  open_e_wrt_u (t_subst_e t1 a1 e1) (u_var_f x1) = t_subst_e t1 a1 (open_e_wrt_u e1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve t_subst_e_open_e_wrt_u_var : lngen.

Lemma t_subst_u_open_u_wrt_u_var :
forall u1 t1 a1 x1,
  open_u_wrt_u (t_subst_u t1 a1 u1) (u_var_f x1) = t_subst_u t1 a1 (open_u_wrt_u u1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_u_var : lngen.

Lemma t_subst_v_open_v_wrt_u_var :
forall v1 t1 a1 x1,
  open_v_wrt_u (t_subst_v t1 a1 v1) (u_var_f x1) = t_subst_v t1 a1 (open_v_wrt_u v1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve t_subst_v_open_v_wrt_u_var : lngen.

Lemma e_subst_d_open_d_wrt_t_var :
forall d1 u1 x1 a1,
  lc_u u1 ->
  open_d_wrt_t (e_subst_d u1 x1 d1) (t_var_f a1) = e_subst_d u1 x1 (open_d_wrt_t d1 (t_var_f a1)).
Proof. Admitted.

Hint Resolve e_subst_d_open_d_wrt_t_var : lngen.

Lemma e_subst_e_open_e_wrt_t_var :
forall e1 u1 x1 a1,
  lc_u u1 ->
  open_e_wrt_t (e_subst_e u1 x1 e1) (t_var_f a1) = e_subst_e u1 x1 (open_e_wrt_t e1 (t_var_f a1)).
Proof. Admitted.

Hint Resolve e_subst_e_open_e_wrt_t_var : lngen.

Lemma e_subst_u_open_u_wrt_t_var :
forall u2 u1 x1 a1,
  lc_u u1 ->
  open_u_wrt_t (e_subst_u u1 x1 u2) (t_var_f a1) = e_subst_u u1 x1 (open_u_wrt_t u2 (t_var_f a1)).
Proof. Admitted.

Hint Resolve e_subst_u_open_u_wrt_t_var : lngen.

Lemma e_subst_v_open_v_wrt_t_var :
forall v1 u1 x1 a1,
  lc_u u1 ->
  open_v_wrt_t (e_subst_v u1 x1 v1) (t_var_f a1) = e_subst_v u1 x1 (open_v_wrt_t v1 (t_var_f a1)).
Proof. Admitted.

Hint Resolve e_subst_v_open_v_wrt_t_var : lngen.

Lemma e_subst_d_open_d_wrt_u_var :
forall d1 u1 x1 x2,
  x1 <> x2 ->
  lc_u u1 ->
  open_d_wrt_u (e_subst_d u1 x1 d1) (u_var_f x2) = e_subst_d u1 x1 (open_d_wrt_u d1 (u_var_f x2)).
Proof. Admitted.

Hint Resolve e_subst_d_open_d_wrt_u_var : lngen.

Lemma e_subst_e_open_e_wrt_u_var :
forall e1 u1 x1 x2,
  x1 <> x2 ->
  lc_u u1 ->
  open_e_wrt_u (e_subst_e u1 x1 e1) (u_var_f x2) = e_subst_e u1 x1 (open_e_wrt_u e1 (u_var_f x2)).
Proof. Admitted.

Hint Resolve e_subst_e_open_e_wrt_u_var : lngen.

Lemma e_subst_u_open_u_wrt_u_var :
forall u2 u1 x1 x2,
  x1 <> x2 ->
  lc_u u1 ->
  open_u_wrt_u (e_subst_u u1 x1 u2) (u_var_f x2) = e_subst_u u1 x1 (open_u_wrt_u u2 (u_var_f x2)).
Proof. Admitted.

Hint Resolve e_subst_u_open_u_wrt_u_var : lngen.

Lemma e_subst_v_open_v_wrt_u_var :
forall v1 u1 x1 x2,
  x1 <> x2 ->
  lc_u u1 ->
  open_v_wrt_u (e_subst_v u1 x1 v1) (u_var_f x2) = e_subst_v u1 x1 (open_v_wrt_u v1 (u_var_f x2)).
Proof. Admitted.

Hint Resolve e_subst_v_open_v_wrt_u_var : lngen.

(* begin hide *)

Lemma t_subst_t_spec_rec_mutual :
(forall t1 t2 a1 n1,
  t_subst_t t2 a1 t1 = open_t_wrt_t_rec n1 t2 (close_t_wrt_t_rec n1 a1 t1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_t_spec_rec :
forall t1 t2 a1 n1,
  t_subst_t t2 a1 t1 = open_t_wrt_t_rec n1 t2 (close_t_wrt_t_rec n1 a1 t1).
Proof. Admitted.

Hint Resolve t_subst_t_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_d_spec_rec_t_subst_e_spec_rec_t_subst_u_spec_rec_t_subst_v_spec_rec_mutual :
(forall d1 t1 a1 n1,
  t_subst_d t1 a1 d1 = open_d_wrt_t_rec n1 t1 (close_d_wrt_t_rec n1 a1 d1)) /\
(forall e1 t1 a1 n1,
  t_subst_e t1 a1 e1 = open_e_wrt_t_rec n1 t1 (close_e_wrt_t_rec n1 a1 e1)) /\
(forall u1 t1 a1 n1,
  t_subst_u t1 a1 u1 = open_u_wrt_t_rec n1 t1 (close_u_wrt_t_rec n1 a1 u1)) /\
(forall v1 t1 a1 n1,
  t_subst_v t1 a1 v1 = open_v_wrt_t_rec n1 t1 (close_v_wrt_t_rec n1 a1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_d_spec_rec :
forall d1 t1 a1 n1,
  t_subst_d t1 a1 d1 = open_d_wrt_t_rec n1 t1 (close_d_wrt_t_rec n1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_e_spec_rec :
forall e1 t1 a1 n1,
  t_subst_e t1 a1 e1 = open_e_wrt_t_rec n1 t1 (close_e_wrt_t_rec n1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_spec_rec :
forall u1 t1 a1 n1,
  t_subst_u t1 a1 u1 = open_u_wrt_t_rec n1 t1 (close_u_wrt_t_rec n1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_v_spec_rec :
forall v1 t1 a1 n1,
  t_subst_v t1 a1 v1 = open_v_wrt_t_rec n1 t1 (close_v_wrt_t_rec n1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_d_spec_rec_e_subst_e_spec_rec_e_subst_u_spec_rec_e_subst_v_spec_rec_mutual :
(forall d1 u1 x1 n1,
  e_subst_d u1 x1 d1 = open_d_wrt_u_rec n1 u1 (close_d_wrt_u_rec n1 x1 d1)) /\
(forall e1 u1 x1 n1,
  e_subst_e u1 x1 e1 = open_e_wrt_u_rec n1 u1 (close_e_wrt_u_rec n1 x1 e1)) /\
(forall u1 u2 x1 n1,
  e_subst_u u2 x1 u1 = open_u_wrt_u_rec n1 u2 (close_u_wrt_u_rec n1 x1 u1)) /\
(forall v1 u1 x1 n1,
  e_subst_v u1 x1 v1 = open_v_wrt_u_rec n1 u1 (close_v_wrt_u_rec n1 x1 v1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_d_spec_rec :
forall d1 u1 x1 n1,
  e_subst_d u1 x1 d1 = open_d_wrt_u_rec n1 u1 (close_d_wrt_u_rec n1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_e_spec_rec :
forall e1 u1 x1 n1,
  e_subst_e u1 x1 e1 = open_e_wrt_u_rec n1 u1 (close_e_wrt_u_rec n1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_u_spec_rec :
forall u1 u2 x1 n1,
  e_subst_u u2 x1 u1 = open_u_wrt_u_rec n1 u2 (close_u_wrt_u_rec n1 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_v_spec_rec :
forall v1 u1 x1 n1,
  e_subst_v u1 x1 v1 = open_v_wrt_u_rec n1 u1 (close_v_wrt_u_rec n1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_spec_rec : lngen.

(* end hide *)

Lemma t_subst_t_spec :
forall t1 t2 a1,
  t_subst_t t2 a1 t1 = open_t_wrt_t (close_t_wrt_t a1 t1) t2.
Proof. Admitted.

Hint Resolve t_subst_t_spec : lngen.

Lemma t_subst_d_spec :
forall d1 t1 a1,
  t_subst_d t1 a1 d1 = open_d_wrt_t (close_d_wrt_t a1 d1) t1.
Proof. Admitted.

Hint Resolve t_subst_d_spec : lngen.

Lemma t_subst_e_spec :
forall e1 t1 a1,
  t_subst_e t1 a1 e1 = open_e_wrt_t (close_e_wrt_t a1 e1) t1.
Proof. Admitted.

Hint Resolve t_subst_e_spec : lngen.

Lemma t_subst_u_spec :
forall u1 t1 a1,
  t_subst_u t1 a1 u1 = open_u_wrt_t (close_u_wrt_t a1 u1) t1.
Proof. Admitted.

Hint Resolve t_subst_u_spec : lngen.

Lemma t_subst_v_spec :
forall v1 t1 a1,
  t_subst_v t1 a1 v1 = open_v_wrt_t (close_v_wrt_t a1 v1) t1.
Proof. Admitted.

Hint Resolve t_subst_v_spec : lngen.

Lemma e_subst_d_spec :
forall d1 u1 x1,
  e_subst_d u1 x1 d1 = open_d_wrt_u (close_d_wrt_u x1 d1) u1.
Proof. Admitted.

Hint Resolve e_subst_d_spec : lngen.

Lemma e_subst_e_spec :
forall e1 u1 x1,
  e_subst_e u1 x1 e1 = open_e_wrt_u (close_e_wrt_u x1 e1) u1.
Proof. Admitted.

Hint Resolve e_subst_e_spec : lngen.

Lemma e_subst_u_spec :
forall u1 u2 x1,
  e_subst_u u2 x1 u1 = open_u_wrt_u (close_u_wrt_u x1 u1) u2.
Proof. Admitted.

Hint Resolve e_subst_u_spec : lngen.

Lemma e_subst_v_spec :
forall v1 u1 x1,
  e_subst_v u1 x1 v1 = open_v_wrt_u (close_v_wrt_u x1 v1) u1.
Proof. Admitted.

Hint Resolve e_subst_v_spec : lngen.

(* begin hide *)

Lemma t_subst_t_t_subst_t_mutual :
(forall t1 t2 t3 a2 a1,
  a2 `notin` tt_fv_t t2 ->
  a2 <> a1 ->
  t_subst_t t2 a1 (t_subst_t t3 a2 t1) = t_subst_t (t_subst_t t2 a1 t3) a2 (t_subst_t t2 a1 t1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_t_t_subst_t :
forall t1 t2 t3 a2 a1,
  a2 `notin` tt_fv_t t2 ->
  a2 <> a1 ->
  t_subst_t t2 a1 (t_subst_t t3 a2 t1) = t_subst_t (t_subst_t t2 a1 t3) a2 (t_subst_t t2 a1 t1).
Proof. Admitted.

Hint Resolve t_subst_t_t_subst_t : lngen.

(* begin hide *)

Lemma t_subst_d_t_subst_d_t_subst_e_t_subst_e_t_subst_u_t_subst_u_t_subst_v_t_subst_v_mutual :
(forall d1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_d t1 a1 (t_subst_d t2 a2 d1) = t_subst_d (t_subst_t t1 a1 t2) a2 (t_subst_d t1 a1 d1)) /\
(forall e1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_e t1 a1 (t_subst_e t2 a2 e1) = t_subst_e (t_subst_t t1 a1 t2) a2 (t_subst_e t1 a1 e1)) /\
(forall u1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_u t1 a1 (t_subst_u t2 a2 u1) = t_subst_u (t_subst_t t1 a1 t2) a2 (t_subst_u t1 a1 u1)) /\
(forall v1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_v t1 a1 (t_subst_v t2 a2 v1) = t_subst_v (t_subst_t t1 a1 t2) a2 (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_d_t_subst_d :
forall d1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_d t1 a1 (t_subst_d t2 a2 d1) = t_subst_d (t_subst_t t1 a1 t2) a2 (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_t_subst_d : lngen.

Lemma t_subst_e_t_subst_e :
forall e1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_e t1 a1 (t_subst_e t2 a2 e1) = t_subst_e (t_subst_t t1 a1 t2) a2 (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_t_subst_e : lngen.

Lemma t_subst_u_t_subst_u :
forall u1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_u t1 a1 (t_subst_u t2 a2 u1) = t_subst_u (t_subst_t t1 a1 t2) a2 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_t_subst_u : lngen.

Lemma t_subst_v_t_subst_v :
forall v1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_v t1 a1 (t_subst_v t2 a2 v1) = t_subst_v (t_subst_t t1 a1 t2) a2 (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_t_subst_v : lngen.

(* begin hide *)

Lemma t_subst_d_e_subst_d_t_subst_e_e_subst_e_t_subst_u_e_subst_u_t_subst_v_e_subst_v_mutual :
(forall d1 t1 u1 x1 a1,
  t_subst_d t1 a1 (e_subst_d u1 x1 d1) = e_subst_d (t_subst_u t1 a1 u1) x1 (t_subst_d t1 a1 d1)) /\
(forall e1 t1 u1 x1 a1,
  t_subst_e t1 a1 (e_subst_e u1 x1 e1) = e_subst_e (t_subst_u t1 a1 u1) x1 (t_subst_e t1 a1 e1)) /\
(forall u1 t1 u2 x1 a1,
  t_subst_u t1 a1 (e_subst_u u2 x1 u1) = e_subst_u (t_subst_u t1 a1 u2) x1 (t_subst_u t1 a1 u1)) /\
(forall v1 t1 u1 x1 a1,
  t_subst_v t1 a1 (e_subst_v u1 x1 v1) = e_subst_v (t_subst_u t1 a1 u1) x1 (t_subst_v t1 a1 v1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_d_e_subst_d :
forall d1 t1 u1 x1 a1,
  t_subst_d t1 a1 (e_subst_d u1 x1 d1) = e_subst_d (t_subst_u t1 a1 u1) x1 (t_subst_d t1 a1 d1).
Proof. Admitted.

Hint Resolve t_subst_d_e_subst_d : lngen.

Lemma t_subst_e_e_subst_e :
forall e1 t1 u1 x1 a1,
  t_subst_e t1 a1 (e_subst_e u1 x1 e1) = e_subst_e (t_subst_u t1 a1 u1) x1 (t_subst_e t1 a1 e1).
Proof. Admitted.

Hint Resolve t_subst_e_e_subst_e : lngen.

Lemma t_subst_u_e_subst_u :
forall u1 t1 u2 x1 a1,
  t_subst_u t1 a1 (e_subst_u u2 x1 u1) = e_subst_u (t_subst_u t1 a1 u2) x1 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_e_subst_u : lngen.

Lemma t_subst_v_e_subst_v :
forall v1 t1 u1 x1 a1,
  t_subst_v t1 a1 (e_subst_v u1 x1 v1) = e_subst_v (t_subst_u t1 a1 u1) x1 (t_subst_v t1 a1 v1).
Proof. Admitted.

Hint Resolve t_subst_v_e_subst_v : lngen.

(* begin hide *)

Lemma e_subst_d_t_subst_d_e_subst_e_t_subst_e_e_subst_u_t_subst_u_e_subst_v_t_subst_v_mutual :
(forall d1 u1 t1 a1 x1,
  a1 `notin` tt_fv_u u1 ->
  e_subst_d u1 x1 (t_subst_d t1 a1 d1) = t_subst_d t1 a1 (e_subst_d u1 x1 d1)) /\
(forall e1 u1 t1 a1 x1,
  a1 `notin` tt_fv_u u1 ->
  e_subst_e u1 x1 (t_subst_e t1 a1 e1) = t_subst_e t1 a1 (e_subst_e u1 x1 e1)) /\
(forall u1 u2 t1 a1 x1,
  a1 `notin` tt_fv_u u2 ->
  e_subst_u u2 x1 (t_subst_u t1 a1 u1) = t_subst_u t1 a1 (e_subst_u u2 x1 u1)) /\
(forall v1 u1 t1 a1 x1,
  a1 `notin` tt_fv_u u1 ->
  e_subst_v u1 x1 (t_subst_v t1 a1 v1) = t_subst_v t1 a1 (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_d_t_subst_d :
forall d1 u1 t1 a1 x1,
  a1 `notin` tt_fv_u u1 ->
  e_subst_d u1 x1 (t_subst_d t1 a1 d1) = t_subst_d t1 a1 (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_t_subst_d : lngen.

Lemma e_subst_e_t_subst_e :
forall e1 u1 t1 a1 x1,
  a1 `notin` tt_fv_u u1 ->
  e_subst_e u1 x1 (t_subst_e t1 a1 e1) = t_subst_e t1 a1 (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_t_subst_e : lngen.

Lemma e_subst_u_t_subst_u :
forall u1 u2 t1 a1 x1,
  a1 `notin` tt_fv_u u2 ->
  e_subst_u u2 x1 (t_subst_u t1 a1 u1) = t_subst_u t1 a1 (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_t_subst_u : lngen.

Lemma e_subst_v_t_subst_v :
forall v1 u1 t1 a1 x1,
  a1 `notin` tt_fv_u u1 ->
  e_subst_v u1 x1 (t_subst_v t1 a1 v1) = t_subst_v t1 a1 (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_t_subst_v : lngen.

(* begin hide *)

Lemma e_subst_d_e_subst_d_e_subst_e_e_subst_e_e_subst_u_e_subst_u_e_subst_v_e_subst_v_mutual :
(forall d1 u1 u2 x2 x1,
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  e_subst_d u1 x1 (e_subst_d u2 x2 d1) = e_subst_d (e_subst_u u1 x1 u2) x2 (e_subst_d u1 x1 d1)) /\
(forall e1 u1 u2 x2 x1,
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  e_subst_e u1 x1 (e_subst_e u2 x2 e1) = e_subst_e (e_subst_u u1 x1 u2) x2 (e_subst_e u1 x1 e1)) /\
(forall u1 u2 u3 x2 x1,
  x2 `notin` e_fv_u u2 ->
  x2 <> x1 ->
  e_subst_u u2 x1 (e_subst_u u3 x2 u1) = e_subst_u (e_subst_u u2 x1 u3) x2 (e_subst_u u2 x1 u1)) /\
(forall v1 u1 u2 x2 x1,
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  e_subst_v u1 x1 (e_subst_v u2 x2 v1) = e_subst_v (e_subst_u u1 x1 u2) x2 (e_subst_v u1 x1 v1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_d_e_subst_d :
forall d1 u1 u2 x2 x1,
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  e_subst_d u1 x1 (e_subst_d u2 x2 d1) = e_subst_d (e_subst_u u1 x1 u2) x2 (e_subst_d u1 x1 d1).
Proof. Admitted.

Hint Resolve e_subst_d_e_subst_d : lngen.

Lemma e_subst_e_e_subst_e :
forall e1 u1 u2 x2 x1,
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  e_subst_e u1 x1 (e_subst_e u2 x2 e1) = e_subst_e (e_subst_u u1 x1 u2) x2 (e_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve e_subst_e_e_subst_e : lngen.

Lemma e_subst_u_e_subst_u :
forall u1 u2 u3 x2 x1,
  x2 `notin` e_fv_u u2 ->
  x2 <> x1 ->
  e_subst_u u2 x1 (e_subst_u u3 x2 u1) = e_subst_u (e_subst_u u2 x1 u3) x2 (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_e_subst_u : lngen.

Lemma e_subst_v_e_subst_v :
forall v1 u1 u2 x2 x1,
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  e_subst_v u1 x1 (e_subst_v u2 x2 v1) = e_subst_v (e_subst_u u1 x1 u2) x2 (e_subst_v u1 x1 v1).
Proof. Admitted.

Hint Resolve e_subst_v_e_subst_v : lngen.

(* begin hide *)

Lemma t_subst_t_close_t_wrt_t_rec_open_t_wrt_t_rec_mutual :
(forall t2 t1 a1 a2 n1,
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_t t1 a1 t2 = close_t_wrt_t_rec n1 a2 (t_subst_t t1 a1 (open_t_wrt_t_rec n1 (t_var_f a2) t2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_t_close_t_wrt_t_rec_open_t_wrt_t_rec :
forall t2 t1 a1 a2 n1,
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_t t1 a1 t2 = close_t_wrt_t_rec n1 a2 (t_subst_t t1 a1 (open_t_wrt_t_rec n1 (t_var_f a2) t2)).
Proof. Admitted.

Hint Resolve t_subst_t_close_t_wrt_t_rec_open_t_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_d_close_d_wrt_t_rec_open_d_wrt_t_rec_t_subst_e_close_e_wrt_t_rec_open_e_wrt_t_rec_t_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec_t_subst_v_close_v_wrt_t_rec_open_v_wrt_t_rec_mutual :
(forall d1 t1 a1 a2 n1,
  a2 `notin` tt_fv_d d1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_d t1 a1 d1 = close_d_wrt_t_rec n1 a2 (t_subst_d t1 a1 (open_d_wrt_t_rec n1 (t_var_f a2) d1))) *
(forall e1 t1 a1 a2 n1,
  a2 `notin` tt_fv_e e1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_e t1 a1 e1 = close_e_wrt_t_rec n1 a2 (t_subst_e t1 a1 (open_e_wrt_t_rec n1 (t_var_f a2) e1))) *
(forall u1 t1 a1 a2 n1,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a2) u1))) *
(forall v1 t1 a1 a2 n1,
  a2 `notin` tt_fv_v v1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_v t1 a1 v1 = close_v_wrt_t_rec n1 a2 (t_subst_v t1 a1 (open_v_wrt_t_rec n1 (t_var_f a2) v1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_d_close_d_wrt_t_rec_open_d_wrt_t_rec :
forall d1 t1 a1 a2 n1,
  a2 `notin` tt_fv_d d1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_d t1 a1 d1 = close_d_wrt_t_rec n1 a2 (t_subst_d t1 a1 (open_d_wrt_t_rec n1 (t_var_f a2) d1)).
Proof. Admitted.

Hint Resolve t_subst_d_close_d_wrt_t_rec_open_d_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_e_close_e_wrt_t_rec_open_e_wrt_t_rec :
forall e1 t1 a1 a2 n1,
  a2 `notin` tt_fv_e e1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_e t1 a1 e1 = close_e_wrt_t_rec n1 a2 (t_subst_e t1 a1 (open_e_wrt_t_rec n1 (t_var_f a2) e1)).
Proof. Admitted.

Hint Resolve t_subst_e_close_e_wrt_t_rec_open_e_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec :
forall u1 t1 a1 a2 n1,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a2) u1)).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_v_close_v_wrt_t_rec_open_v_wrt_t_rec :
forall v1 t1 a1 a2 n1,
  a2 `notin` tt_fv_v v1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_v t1 a1 v1 = close_v_wrt_t_rec n1 a2 (t_subst_v t1 a1 (open_v_wrt_t_rec n1 (t_var_f a2) v1)).
Proof. Admitted.

Hint Resolve t_subst_v_close_v_wrt_t_rec_open_v_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_d_close_d_wrt_u_rec_open_d_wrt_u_rec_t_subst_e_close_e_wrt_u_rec_open_e_wrt_u_rec_t_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec_t_subst_v_close_v_wrt_u_rec_open_v_wrt_u_rec_mutual :
(forall d1 t1 a1 x1 n1,
  x1 `notin` e_fv_d d1 ->
  t_subst_d t1 a1 d1 = close_d_wrt_u_rec n1 x1 (t_subst_d t1 a1 (open_d_wrt_u_rec n1 (u_var_f x1) d1))) *
(forall e1 t1 a1 x1 n1,
  x1 `notin` e_fv_e e1 ->
  t_subst_e t1 a1 e1 = close_e_wrt_u_rec n1 x1 (t_subst_e t1 a1 (open_e_wrt_u_rec n1 (u_var_f x1) e1))) *
(forall u1 t1 a1 x1 n1,
  x1 `notin` e_fv_u u1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_u_rec n1 x1 (t_subst_u t1 a1 (open_u_wrt_u_rec n1 (u_var_f x1) u1))) *
(forall v1 t1 a1 x1 n1,
  x1 `notin` e_fv_v v1 ->
  t_subst_v t1 a1 v1 = close_v_wrt_u_rec n1 x1 (t_subst_v t1 a1 (open_v_wrt_u_rec n1 (u_var_f x1) v1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_d_close_d_wrt_u_rec_open_d_wrt_u_rec :
forall d1 t1 a1 x1 n1,
  x1 `notin` e_fv_d d1 ->
  t_subst_d t1 a1 d1 = close_d_wrt_u_rec n1 x1 (t_subst_d t1 a1 (open_d_wrt_u_rec n1 (u_var_f x1) d1)).
Proof. Admitted.

Hint Resolve t_subst_d_close_d_wrt_u_rec_open_d_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_e_close_e_wrt_u_rec_open_e_wrt_u_rec :
forall e1 t1 a1 x1 n1,
  x1 `notin` e_fv_e e1 ->
  t_subst_e t1 a1 e1 = close_e_wrt_u_rec n1 x1 (t_subst_e t1 a1 (open_e_wrt_u_rec n1 (u_var_f x1) e1)).
Proof. Admitted.

Hint Resolve t_subst_e_close_e_wrt_u_rec_open_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec :
forall u1 t1 a1 x1 n1,
  x1 `notin` e_fv_u u1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_u_rec n1 x1 (t_subst_u t1 a1 (open_u_wrt_u_rec n1 (u_var_f x1) u1)).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_v_close_v_wrt_u_rec_open_v_wrt_u_rec :
forall v1 t1 a1 x1 n1,
  x1 `notin` e_fv_v v1 ->
  t_subst_v t1 a1 v1 = close_v_wrt_u_rec n1 x1 (t_subst_v t1 a1 (open_v_wrt_u_rec n1 (u_var_f x1) v1)).
Proof. Admitted.

Hint Resolve t_subst_v_close_v_wrt_u_rec_open_v_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_d_close_d_wrt_t_rec_open_d_wrt_t_rec_e_subst_e_close_e_wrt_t_rec_open_e_wrt_t_rec_e_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec_e_subst_v_close_v_wrt_t_rec_open_v_wrt_t_rec_mutual :
(forall d1 u1 x1 a1 n1,
  a1 `notin` tt_fv_d d1 ->
  a1 `notin` tt_fv_u u1 ->
  degree_u_wrt_t n1 u1 ->
  e_subst_d u1 x1 d1 = close_d_wrt_t_rec n1 a1 (e_subst_d u1 x1 (open_d_wrt_t_rec n1 (t_var_f a1) d1))) *
(forall e1 u1 x1 a1 n1,
  a1 `notin` tt_fv_e e1 ->
  a1 `notin` tt_fv_u u1 ->
  degree_u_wrt_t n1 u1 ->
  e_subst_e u1 x1 e1 = close_e_wrt_t_rec n1 a1 (e_subst_e u1 x1 (open_e_wrt_t_rec n1 (t_var_f a1) e1))) *
(forall u2 u1 x1 a1 n1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  degree_u_wrt_t n1 u1 ->
  e_subst_u u1 x1 u2 = close_u_wrt_t_rec n1 a1 (e_subst_u u1 x1 (open_u_wrt_t_rec n1 (t_var_f a1) u2))) *
(forall v1 u1 x1 a1 n1,
  a1 `notin` tt_fv_v v1 ->
  a1 `notin` tt_fv_u u1 ->
  degree_u_wrt_t n1 u1 ->
  e_subst_v u1 x1 v1 = close_v_wrt_t_rec n1 a1 (e_subst_v u1 x1 (open_v_wrt_t_rec n1 (t_var_f a1) v1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_d_close_d_wrt_t_rec_open_d_wrt_t_rec :
forall d1 u1 x1 a1 n1,
  a1 `notin` tt_fv_d d1 ->
  a1 `notin` tt_fv_u u1 ->
  degree_u_wrt_t n1 u1 ->
  e_subst_d u1 x1 d1 = close_d_wrt_t_rec n1 a1 (e_subst_d u1 x1 (open_d_wrt_t_rec n1 (t_var_f a1) d1)).
Proof. Admitted.

Hint Resolve e_subst_d_close_d_wrt_t_rec_open_d_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_e_close_e_wrt_t_rec_open_e_wrt_t_rec :
forall e1 u1 x1 a1 n1,
  a1 `notin` tt_fv_e e1 ->
  a1 `notin` tt_fv_u u1 ->
  degree_u_wrt_t n1 u1 ->
  e_subst_e u1 x1 e1 = close_e_wrt_t_rec n1 a1 (e_subst_e u1 x1 (open_e_wrt_t_rec n1 (t_var_f a1) e1)).
Proof. Admitted.

Hint Resolve e_subst_e_close_e_wrt_t_rec_open_e_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec :
forall u2 u1 x1 a1 n1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  degree_u_wrt_t n1 u1 ->
  e_subst_u u1 x1 u2 = close_u_wrt_t_rec n1 a1 (e_subst_u u1 x1 (open_u_wrt_t_rec n1 (t_var_f a1) u2)).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_v_close_v_wrt_t_rec_open_v_wrt_t_rec :
forall v1 u1 x1 a1 n1,
  a1 `notin` tt_fv_v v1 ->
  a1 `notin` tt_fv_u u1 ->
  degree_u_wrt_t n1 u1 ->
  e_subst_v u1 x1 v1 = close_v_wrt_t_rec n1 a1 (e_subst_v u1 x1 (open_v_wrt_t_rec n1 (t_var_f a1) v1)).
Proof. Admitted.

Hint Resolve e_subst_v_close_v_wrt_t_rec_open_v_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_d_close_d_wrt_u_rec_open_d_wrt_u_rec_e_subst_e_close_e_wrt_u_rec_open_e_wrt_u_rec_e_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec_e_subst_v_close_v_wrt_u_rec_open_v_wrt_u_rec_mutual :
(forall d1 u1 x1 x2 n1,
  x2 `notin` e_fv_d d1 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  e_subst_d u1 x1 d1 = close_d_wrt_u_rec n1 x2 (e_subst_d u1 x1 (open_d_wrt_u_rec n1 (u_var_f x2) d1))) *
(forall e1 u1 x1 x2 n1,
  x2 `notin` e_fv_e e1 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  e_subst_e u1 x1 e1 = close_e_wrt_u_rec n1 x2 (e_subst_e u1 x1 (open_e_wrt_u_rec n1 (u_var_f x2) e1))) *
(forall u2 u1 x1 x2 n1,
  x2 `notin` e_fv_u u2 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  e_subst_u u1 x1 u2 = close_u_wrt_u_rec n1 x2 (e_subst_u u1 x1 (open_u_wrt_u_rec n1 (u_var_f x2) u2))) *
(forall v1 u1 x1 x2 n1,
  x2 `notin` e_fv_v v1 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  e_subst_v u1 x1 v1 = close_v_wrt_u_rec n1 x2 (e_subst_v u1 x1 (open_v_wrt_u_rec n1 (u_var_f x2) v1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_d_close_d_wrt_u_rec_open_d_wrt_u_rec :
forall d1 u1 x1 x2 n1,
  x2 `notin` e_fv_d d1 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  e_subst_d u1 x1 d1 = close_d_wrt_u_rec n1 x2 (e_subst_d u1 x1 (open_d_wrt_u_rec n1 (u_var_f x2) d1)).
Proof. Admitted.

Hint Resolve e_subst_d_close_d_wrt_u_rec_open_d_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_e_close_e_wrt_u_rec_open_e_wrt_u_rec :
forall e1 u1 x1 x2 n1,
  x2 `notin` e_fv_e e1 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  e_subst_e u1 x1 e1 = close_e_wrt_u_rec n1 x2 (e_subst_e u1 x1 (open_e_wrt_u_rec n1 (u_var_f x2) e1)).
Proof. Admitted.

Hint Resolve e_subst_e_close_e_wrt_u_rec_open_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec :
forall u2 u1 x1 x2 n1,
  x2 `notin` e_fv_u u2 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  e_subst_u u1 x1 u2 = close_u_wrt_u_rec n1 x2 (e_subst_u u1 x1 (open_u_wrt_u_rec n1 (u_var_f x2) u2)).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma e_subst_v_close_v_wrt_u_rec_open_v_wrt_u_rec :
forall v1 u1 x1 x2 n1,
  x2 `notin` e_fv_v v1 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  e_subst_v u1 x1 v1 = close_v_wrt_u_rec n1 x2 (e_subst_v u1 x1 (open_v_wrt_u_rec n1 (u_var_f x2) v1)).
Proof. Admitted.

Hint Resolve e_subst_v_close_v_wrt_u_rec_open_v_wrt_u_rec : lngen.

(* end hide *)

Lemma t_subst_t_close_t_wrt_t_open_t_wrt_t :
forall t2 t1 a1 a2,
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  lc_t t1 ->
  t_subst_t t1 a1 t2 = close_t_wrt_t a2 (t_subst_t t1 a1 (open_t_wrt_t t2 (t_var_f a2))).
Proof. Admitted.

Hint Resolve t_subst_t_close_t_wrt_t_open_t_wrt_t : lngen.

Lemma t_subst_d_close_d_wrt_t_open_d_wrt_t :
forall d1 t1 a1 a2,
  a2 `notin` tt_fv_d d1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  lc_t t1 ->
  t_subst_d t1 a1 d1 = close_d_wrt_t a2 (t_subst_d t1 a1 (open_d_wrt_t d1 (t_var_f a2))).
Proof. Admitted.

Hint Resolve t_subst_d_close_d_wrt_t_open_d_wrt_t : lngen.

Lemma t_subst_e_close_e_wrt_t_open_e_wrt_t :
forall e1 t1 a1 a2,
  a2 `notin` tt_fv_e e1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  lc_t t1 ->
  t_subst_e t1 a1 e1 = close_e_wrt_t a2 (t_subst_e t1 a1 (open_e_wrt_t e1 (t_var_f a2))).
Proof. Admitted.

Hint Resolve t_subst_e_close_e_wrt_t_open_e_wrt_t : lngen.

Lemma t_subst_u_close_u_wrt_t_open_u_wrt_t :
forall u1 t1 a1 a2,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  lc_t t1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_t a2 (t_subst_u t1 a1 (open_u_wrt_t u1 (t_var_f a2))).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_t_open_u_wrt_t : lngen.

Lemma t_subst_v_close_v_wrt_t_open_v_wrt_t :
forall v1 t1 a1 a2,
  a2 `notin` tt_fv_v v1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  lc_t t1 ->
  t_subst_v t1 a1 v1 = close_v_wrt_t a2 (t_subst_v t1 a1 (open_v_wrt_t v1 (t_var_f a2))).
Proof. Admitted.

Hint Resolve t_subst_v_close_v_wrt_t_open_v_wrt_t : lngen.

Lemma t_subst_d_close_d_wrt_u_open_d_wrt_u :
forall d1 t1 a1 x1,
  x1 `notin` e_fv_d d1 ->
  lc_t t1 ->
  t_subst_d t1 a1 d1 = close_d_wrt_u x1 (t_subst_d t1 a1 (open_d_wrt_u d1 (u_var_f x1))).
Proof. Admitted.

Hint Resolve t_subst_d_close_d_wrt_u_open_d_wrt_u : lngen.

Lemma t_subst_e_close_e_wrt_u_open_e_wrt_u :
forall e1 t1 a1 x1,
  x1 `notin` e_fv_e e1 ->
  lc_t t1 ->
  t_subst_e t1 a1 e1 = close_e_wrt_u x1 (t_subst_e t1 a1 (open_e_wrt_u e1 (u_var_f x1))).
Proof. Admitted.

Hint Resolve t_subst_e_close_e_wrt_u_open_e_wrt_u : lngen.

Lemma t_subst_u_close_u_wrt_u_open_u_wrt_u :
forall u1 t1 a1 x1,
  x1 `notin` e_fv_u u1 ->
  lc_t t1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_u x1 (t_subst_u t1 a1 (open_u_wrt_u u1 (u_var_f x1))).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_u_open_u_wrt_u : lngen.

Lemma t_subst_v_close_v_wrt_u_open_v_wrt_u :
forall v1 t1 a1 x1,
  x1 `notin` e_fv_v v1 ->
  lc_t t1 ->
  t_subst_v t1 a1 v1 = close_v_wrt_u x1 (t_subst_v t1 a1 (open_v_wrt_u v1 (u_var_f x1))).
Proof. Admitted.

Hint Resolve t_subst_v_close_v_wrt_u_open_v_wrt_u : lngen.

Lemma e_subst_d_close_d_wrt_t_open_d_wrt_t :
forall d1 u1 x1 a1,
  a1 `notin` tt_fv_d d1 ->
  a1 `notin` tt_fv_u u1 ->
  lc_u u1 ->
  e_subst_d u1 x1 d1 = close_d_wrt_t a1 (e_subst_d u1 x1 (open_d_wrt_t d1 (t_var_f a1))).
Proof. Admitted.

Hint Resolve e_subst_d_close_d_wrt_t_open_d_wrt_t : lngen.

Lemma e_subst_e_close_e_wrt_t_open_e_wrt_t :
forall e1 u1 x1 a1,
  a1 `notin` tt_fv_e e1 ->
  a1 `notin` tt_fv_u u1 ->
  lc_u u1 ->
  e_subst_e u1 x1 e1 = close_e_wrt_t a1 (e_subst_e u1 x1 (open_e_wrt_t e1 (t_var_f a1))).
Proof. Admitted.

Hint Resolve e_subst_e_close_e_wrt_t_open_e_wrt_t : lngen.

Lemma e_subst_u_close_u_wrt_t_open_u_wrt_t :
forall u2 u1 x1 a1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  lc_u u1 ->
  e_subst_u u1 x1 u2 = close_u_wrt_t a1 (e_subst_u u1 x1 (open_u_wrt_t u2 (t_var_f a1))).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_t_open_u_wrt_t : lngen.

Lemma e_subst_v_close_v_wrt_t_open_v_wrt_t :
forall v1 u1 x1 a1,
  a1 `notin` tt_fv_v v1 ->
  a1 `notin` tt_fv_u u1 ->
  lc_u u1 ->
  e_subst_v u1 x1 v1 = close_v_wrt_t a1 (e_subst_v u1 x1 (open_v_wrt_t v1 (t_var_f a1))).
Proof. Admitted.

Hint Resolve e_subst_v_close_v_wrt_t_open_v_wrt_t : lngen.

Lemma e_subst_d_close_d_wrt_u_open_d_wrt_u :
forall d1 u1 x1 x2,
  x2 `notin` e_fv_d d1 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  lc_u u1 ->
  e_subst_d u1 x1 d1 = close_d_wrt_u x2 (e_subst_d u1 x1 (open_d_wrt_u d1 (u_var_f x2))).
Proof. Admitted.

Hint Resolve e_subst_d_close_d_wrt_u_open_d_wrt_u : lngen.

Lemma e_subst_e_close_e_wrt_u_open_e_wrt_u :
forall e1 u1 x1 x2,
  x2 `notin` e_fv_e e1 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  lc_u u1 ->
  e_subst_e u1 x1 e1 = close_e_wrt_u x2 (e_subst_e u1 x1 (open_e_wrt_u e1 (u_var_f x2))).
Proof. Admitted.

Hint Resolve e_subst_e_close_e_wrt_u_open_e_wrt_u : lngen.

Lemma e_subst_u_close_u_wrt_u_open_u_wrt_u :
forall u2 u1 x1 x2,
  x2 `notin` e_fv_u u2 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  lc_u u1 ->
  e_subst_u u1 x1 u2 = close_u_wrt_u x2 (e_subst_u u1 x1 (open_u_wrt_u u2 (u_var_f x2))).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_u_open_u_wrt_u : lngen.

Lemma e_subst_v_close_v_wrt_u_open_v_wrt_u :
forall v1 u1 x1 x2,
  x2 `notin` e_fv_v v1 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  lc_u u1 ->
  e_subst_v u1 x1 v1 = close_v_wrt_u x2 (e_subst_v u1 x1 (open_v_wrt_u v1 (u_var_f x2))).
Proof. Admitted.

Hint Resolve e_subst_v_close_v_wrt_u_open_v_wrt_u : lngen.

Lemma t_subst_t_t_all :
forall a2 t2 t1 a1,
  lc_t t1 ->
  a2 `notin` tt_fv_t t1 `union` tt_fv_t t2 `union` singleton a1 ->
  t_subst_t t1 a1 (t_all t2) = t_all (close_t_wrt_t a2 (t_subst_t t1 a1 (open_t_wrt_t t2 (t_var_f a2)))).
Proof. Admitted.

Hint Resolve t_subst_t_t_all : lngen.

Lemma t_subst_e_e_let :
forall x1 d1 e1 t1 a1,
  lc_t t1 ->
  x1 `notin` e_fv_e e1 ->
  t_subst_e t1 a1 (e_let d1 e1) = e_let (t_subst_d t1 a1 d1) (close_e_wrt_u x1 (t_subst_e t1 a1 (open_e_wrt_u e1 (u_var_f x1)))).
Proof. Admitted.

Hint Resolve t_subst_e_e_let : lngen.

Lemma e_subst_e_e_let :
forall x2 d1 e1 u1 x1,
  lc_u u1 ->
  x2 `notin` e_fv_u u1 `union` e_fv_e e1 `union` singleton x1 ->
  e_subst_e u1 x1 (e_let d1 e1) = e_let (e_subst_d u1 x1 d1) (close_e_wrt_u x2 (e_subst_e u1 x1 (open_e_wrt_u e1 (u_var_f x2)))).
Proof. Admitted.

Hint Resolve e_subst_e_e_let : lngen.

Lemma t_subst_u_u_lam :
forall x1 t2 v1 t1 a1,
  lc_t t1 ->
  x1 `notin` e_fv_v v1 ->
  t_subst_u t1 a1 (u_lam t2 v1) = u_lam (t_subst_t t1 a1 t2) (close_v_wrt_u x1 (t_subst_v t1 a1 (open_v_wrt_u v1 (u_var_f x1)))).
Proof. Admitted.

Hint Resolve t_subst_u_u_lam : lngen.

Lemma t_subst_u_u_Lam :
forall x1 t2 e1 t1 a1,
  lc_t t1 ->
  x1 `notin` e_fv_e e1 ->
  t_subst_u t1 a1 (u_Lam t2 e1) = u_Lam (t_subst_t t1 a1 t2) (close_e_wrt_u x1 (t_subst_e t1 a1 (open_e_wrt_u e1 (u_var_f x1)))).
Proof. Admitted.

Hint Resolve t_subst_u_u_Lam : lngen.

Lemma e_subst_u_u_lam :
forall x2 t1 v1 u1 x1,
  lc_u u1 ->
  x2 `notin` e_fv_u u1 `union` e_fv_v v1 `union` singleton x1 ->
  e_subst_u u1 x1 (u_lam t1 v1) = u_lam (t1) (close_v_wrt_u x2 (e_subst_v u1 x1 (open_v_wrt_u v1 (u_var_f x2)))).
Proof. Admitted.

Hint Resolve e_subst_u_u_lam : lngen.

Lemma e_subst_u_u_Lam :
forall x2 t1 e1 u1 x1,
  lc_u u1 ->
  x2 `notin` e_fv_u u1 `union` e_fv_e e1 `union` singleton x1 ->
  e_subst_u u1 x1 (u_Lam t1 e1) = u_Lam (t1) (close_e_wrt_u x2 (e_subst_e u1 x1 (open_e_wrt_u e1 (u_var_f x2)))).
Proof. Admitted.

Hint Resolve e_subst_u_u_Lam : lngen.

(* begin hide *)

Lemma t_subst_t_intro_rec_mutual :
(forall t1 a1 t2 n1,
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t_rec n1 t2 t1 = t_subst_t t2 a1 (open_t_wrt_t_rec n1 (t_var_f a1) t1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_t_intro_rec :
forall t1 a1 t2 n1,
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t_rec n1 t2 t1 = t_subst_t t2 a1 (open_t_wrt_t_rec n1 (t_var_f a1) t1).
Proof. Admitted.

Hint Resolve t_subst_t_intro_rec : lngen.
Hint Rewrite t_subst_t_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_d_intro_rec_t_subst_e_intro_rec_t_subst_u_intro_rec_t_subst_v_intro_rec_mutual :
(forall d1 a1 t1 n1,
  a1 `notin` tt_fv_d d1 ->
  open_d_wrt_t_rec n1 t1 d1 = t_subst_d t1 a1 (open_d_wrt_t_rec n1 (t_var_f a1) d1)) /\
(forall e1 a1 t1 n1,
  a1 `notin` tt_fv_e e1 ->
  open_e_wrt_t_rec n1 t1 e1 = t_subst_e t1 a1 (open_e_wrt_t_rec n1 (t_var_f a1) e1)) /\
(forall u1 a1 t1 n1,
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 t1 u1 = t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1)) /\
(forall v1 a1 t1 n1,
  a1 `notin` tt_fv_v v1 ->
  open_v_wrt_t_rec n1 t1 v1 = t_subst_v t1 a1 (open_v_wrt_t_rec n1 (t_var_f a1) v1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_d_intro_rec :
forall d1 a1 t1 n1,
  a1 `notin` tt_fv_d d1 ->
  open_d_wrt_t_rec n1 t1 d1 = t_subst_d t1 a1 (open_d_wrt_t_rec n1 (t_var_f a1) d1).
Proof. Admitted.

Hint Resolve t_subst_d_intro_rec : lngen.
Hint Rewrite t_subst_d_intro_rec using solve [auto] : lngen.

Lemma t_subst_e_intro_rec :
forall e1 a1 t1 n1,
  a1 `notin` tt_fv_e e1 ->
  open_e_wrt_t_rec n1 t1 e1 = t_subst_e t1 a1 (open_e_wrt_t_rec n1 (t_var_f a1) e1).
Proof. Admitted.

Hint Resolve t_subst_e_intro_rec : lngen.
Hint Rewrite t_subst_e_intro_rec using solve [auto] : lngen.

Lemma t_subst_u_intro_rec :
forall u1 a1 t1 n1,
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 t1 u1 = t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1).
Proof. Admitted.

Hint Resolve t_subst_u_intro_rec : lngen.
Hint Rewrite t_subst_u_intro_rec using solve [auto] : lngen.

Lemma t_subst_v_intro_rec :
forall v1 a1 t1 n1,
  a1 `notin` tt_fv_v v1 ->
  open_v_wrt_t_rec n1 t1 v1 = t_subst_v t1 a1 (open_v_wrt_t_rec n1 (t_var_f a1) v1).
Proof. Admitted.

Hint Resolve t_subst_v_intro_rec : lngen.
Hint Rewrite t_subst_v_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma e_subst_d_intro_rec_e_subst_e_intro_rec_e_subst_u_intro_rec_e_subst_v_intro_rec_mutual :
(forall d1 x1 u1 n1,
  x1 `notin` e_fv_d d1 ->
  open_d_wrt_u_rec n1 u1 d1 = e_subst_d u1 x1 (open_d_wrt_u_rec n1 (u_var_f x1) d1)) /\
(forall e1 x1 u1 n1,
  x1 `notin` e_fv_e e1 ->
  open_e_wrt_u_rec n1 u1 e1 = e_subst_e u1 x1 (open_e_wrt_u_rec n1 (u_var_f x1) e1)) /\
(forall u1 x1 u2 n1,
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u_rec n1 u2 u1 = e_subst_u u2 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1)) /\
(forall v1 x1 u1 n1,
  x1 `notin` e_fv_v v1 ->
  open_v_wrt_u_rec n1 u1 v1 = e_subst_v u1 x1 (open_v_wrt_u_rec n1 (u_var_f x1) v1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_d_intro_rec :
forall d1 x1 u1 n1,
  x1 `notin` e_fv_d d1 ->
  open_d_wrt_u_rec n1 u1 d1 = e_subst_d u1 x1 (open_d_wrt_u_rec n1 (u_var_f x1) d1).
Proof. Admitted.

Hint Resolve e_subst_d_intro_rec : lngen.
Hint Rewrite e_subst_d_intro_rec using solve [auto] : lngen.

Lemma e_subst_e_intro_rec :
forall e1 x1 u1 n1,
  x1 `notin` e_fv_e e1 ->
  open_e_wrt_u_rec n1 u1 e1 = e_subst_e u1 x1 (open_e_wrt_u_rec n1 (u_var_f x1) e1).
Proof. Admitted.

Hint Resolve e_subst_e_intro_rec : lngen.
Hint Rewrite e_subst_e_intro_rec using solve [auto] : lngen.

Lemma e_subst_u_intro_rec :
forall u1 x1 u2 n1,
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u_rec n1 u2 u1 = e_subst_u u2 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1).
Proof. Admitted.

Hint Resolve e_subst_u_intro_rec : lngen.
Hint Rewrite e_subst_u_intro_rec using solve [auto] : lngen.

Lemma e_subst_v_intro_rec :
forall v1 x1 u1 n1,
  x1 `notin` e_fv_v v1 ->
  open_v_wrt_u_rec n1 u1 v1 = e_subst_v u1 x1 (open_v_wrt_u_rec n1 (u_var_f x1) v1).
Proof. Admitted.

Hint Resolve e_subst_v_intro_rec : lngen.
Hint Rewrite e_subst_v_intro_rec using solve [auto] : lngen.

Lemma t_subst_t_intro :
forall a1 t1 t2,
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t t1 t2 = t_subst_t t2 a1 (open_t_wrt_t t1 (t_var_f a1)).
Proof. Admitted.

Hint Resolve t_subst_t_intro : lngen.

Lemma t_subst_d_intro :
forall a1 d1 t1,
  a1 `notin` tt_fv_d d1 ->
  open_d_wrt_t d1 t1 = t_subst_d t1 a1 (open_d_wrt_t d1 (t_var_f a1)).
Proof. Admitted.

Hint Resolve t_subst_d_intro : lngen.

Lemma t_subst_e_intro :
forall a1 e1 t1,
  a1 `notin` tt_fv_e e1 ->
  open_e_wrt_t e1 t1 = t_subst_e t1 a1 (open_e_wrt_t e1 (t_var_f a1)).
Proof. Admitted.

Hint Resolve t_subst_e_intro : lngen.

Lemma t_subst_u_intro :
forall a1 u1 t1,
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t u1 t1 = t_subst_u t1 a1 (open_u_wrt_t u1 (t_var_f a1)).
Proof. Admitted.

Hint Resolve t_subst_u_intro : lngen.

Lemma t_subst_v_intro :
forall a1 v1 t1,
  a1 `notin` tt_fv_v v1 ->
  open_v_wrt_t v1 t1 = t_subst_v t1 a1 (open_v_wrt_t v1 (t_var_f a1)).
Proof. Admitted.

Hint Resolve t_subst_v_intro : lngen.

Lemma e_subst_d_intro :
forall x1 d1 u1,
  x1 `notin` e_fv_d d1 ->
  open_d_wrt_u d1 u1 = e_subst_d u1 x1 (open_d_wrt_u d1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve e_subst_d_intro : lngen.

Lemma e_subst_e_intro :
forall x1 e1 u1,
  x1 `notin` e_fv_e e1 ->
  open_e_wrt_u e1 u1 = e_subst_e u1 x1 (open_e_wrt_u e1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve e_subst_e_intro : lngen.

Lemma e_subst_u_intro :
forall x1 u1 u2,
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u u1 u2 = e_subst_u u2 x1 (open_u_wrt_u u1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve e_subst_u_intro : lngen.

Lemma e_subst_v_intro :
forall x1 v1 u1,
  x1 `notin` e_fv_v v1 ->
  open_v_wrt_u v1 u1 = e_subst_v u1 x1 (open_v_wrt_u v1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve e_subst_v_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
