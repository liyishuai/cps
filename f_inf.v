Add LoadPath ".".
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export LibLNgen.

Require Export f_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme t_ind' := Induction for t Sort Prop.

Definition t_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  t_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme t_rec' := Induction for t Sort Set.

Definition t_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  t_rec' H1 H2 H3 H4 H5 H6 H7.

Scheme p_ind' := Induction for p Sort Prop.

Definition p_mutind :=
  fun H1 H2 H3 =>
  p_ind' H1 H2 H3.

Scheme p_rec' := Induction for p Sort Set.

Definition p_mutrec :=
  fun H1 H2 H3 =>
  p_rec' H1 H2 H3.

Scheme u_ind' := Induction for u Sort Prop.

Definition u_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.

Scheme u_rec' := Induction for u Sort Set.

Definition u_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  u_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_t_wrt_t_rec (n1 : nat) (a1 : a) (t1 : t) {struct t1} : t :=
  match t1 with
    | t_var_f a2 => if (a1 == a2) then (t_var_b n1) else (t_var_f a2)
    | t_var_b n2 => if (lt_ge_dec n2 n1) then (t_var_b n2) else (t_var_b (S n2))
    | t_int => t_int
    | t_arr t2 t3 => t_arr (close_t_wrt_t_rec n1 a1 t2) (close_t_wrt_t_rec n1 a1 t3)
    | t_all t2 => t_all (close_t_wrt_t_rec (S n1) a1 t2)
    | t_prod t2 t3 => t_prod (close_t_wrt_t_rec n1 a1 t2) (close_t_wrt_t_rec n1 a1 t3)
  end.

Definition close_t_wrt_t a1 t1 := close_t_wrt_t_rec 0 a1 t1.

Fixpoint close_u_wrt_u_rec (n1 : nat) (x1 : x) (u1 : u) {struct u1} : u :=
  match u1 with
    | u_var_f x2 => if (x1 == x2) then (u_var_b n1) else (u_var_f x2)
    | u_var_b n2 => if (lt_ge_dec n2 n1) then (u_var_b n2) else (u_var_b (S n2))
    | u_int i1 => u_int i1
    | u_fix t1 t2 e1 => u_fix t1 t2 (close_u_wrt_u_rec (S n1) x1 e1)
    | u_lam t1 e1 => u_lam t1 (close_u_wrt_u_rec (S n1) x1 e1)
    | u_app e1 e2 => u_app (close_u_wrt_u_rec n1 x1 e1) (close_u_wrt_u_rec n1 x1 e2)
    | u_tlam e1 => u_tlam (close_u_wrt_u_rec n1 x1 e1)
    | u_tapp e1 t1 => u_tapp (close_u_wrt_u_rec n1 x1 e1) t1
    | u_pair e1 e2 => u_pair (close_u_wrt_u_rec n1 x1 e1) (close_u_wrt_u_rec n1 x1 e2)
    | u_prl e1 => u_prl (close_u_wrt_u_rec n1 x1 e1)
    | u_prr e1 => u_prr (close_u_wrt_u_rec n1 x1 e1)
    | u_prim e1 p1 e2 => u_prim (close_u_wrt_u_rec n1 x1 e1) p1 (close_u_wrt_u_rec n1 x1 e2)
    | u_if0 e1 e2 e3 => u_if0 (close_u_wrt_u_rec n1 x1 e1) (close_u_wrt_u_rec n1 x1 e2) (close_u_wrt_u_rec n1 x1 e3)
    | u_ann u2 t1 => u_ann (close_u_wrt_u_rec n1 x1 u2) t1
  end.

Fixpoint close_u_wrt_t_rec (n1 : nat) (a1 : a) (u1 : u) {struct u1} : u :=
  match u1 with
    | u_var_f x1 => u_var_f x1
    | u_var_b n2 => u_var_b n2
    | u_int i1 => u_int i1
    | u_fix t1 t2 e1 => u_fix (close_t_wrt_t_rec n1 a1 t1) (close_t_wrt_t_rec n1 a1 t2) (close_u_wrt_t_rec n1 a1 e1)
    | u_lam t1 e1 => u_lam (close_t_wrt_t_rec n1 a1 t1) (close_u_wrt_t_rec n1 a1 e1)
    | u_app e1 e2 => u_app (close_u_wrt_t_rec n1 a1 e1) (close_u_wrt_t_rec n1 a1 e2)
    | u_tlam e1 => u_tlam (close_u_wrt_t_rec (S n1) a1 e1)
    | u_tapp e1 t1 => u_tapp (close_u_wrt_t_rec n1 a1 e1) (close_t_wrt_t_rec n1 a1 t1)
    | u_pair e1 e2 => u_pair (close_u_wrt_t_rec n1 a1 e1) (close_u_wrt_t_rec n1 a1 e2)
    | u_prl e1 => u_prl (close_u_wrt_t_rec n1 a1 e1)
    | u_prr e1 => u_prr (close_u_wrt_t_rec n1 a1 e1)
    | u_prim e1 p1 e2 => u_prim (close_u_wrt_t_rec n1 a1 e1) p1 (close_u_wrt_t_rec n1 a1 e2)
    | u_if0 e1 e2 e3 => u_if0 (close_u_wrt_t_rec n1 a1 e1) (close_u_wrt_t_rec n1 a1 e2) (close_u_wrt_t_rec n1 a1 e3)
    | u_ann u2 t1 => u_ann (close_u_wrt_t_rec n1 a1 u2) (close_t_wrt_t_rec n1 a1 t1)
  end.

Definition close_u_wrt_u x1 u1 := close_u_wrt_u_rec 0 x1 u1.

Definition close_u_wrt_t a1 u1 := close_u_wrt_t_rec 0 a1 u1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_t (t1 : t) {struct t1} : nat :=
  match t1 with
    | t_var_f a1 => 1
    | t_var_b n1 => 1
    | t_int => 1
    | t_arr t2 t3 => 1 + (size_t t2) + (size_t t3)
    | t_all t2 => 1 + (size_t t2)
    | t_prod t2 t3 => 1 + (size_t t2) + (size_t t3)
  end.

Fixpoint size_p (p1 : p) {struct p1} : nat :=
  match p1 with
    | p_plus => 1
    | p_minus => 1
  end.

Fixpoint size_u (u1 : u) {struct u1} : nat :=
  match u1 with
    | u_var_f x1 => 1
    | u_var_b n1 => 1
    | u_int i1 => 1
    | u_fix t1 t2 e1 => 1 + (size_t t1) + (size_t t2) + (size_u e1)
    | u_lam t1 e1 => 1 + (size_t t1) + (size_u e1)
    | u_app e1 e2 => 1 + (size_u e1) + (size_u e2)
    | u_tlam e1 => 1 + (size_u e1)
    | u_tapp e1 t1 => 1 + (size_u e1) + (size_t t1)
    | u_pair e1 e2 => 1 + (size_u e1) + (size_u e2)
    | u_prl e1 => 1 + (size_u e1)
    | u_prr e1 => 1 + (size_u e1)
    | u_prim e1 p1 e2 => 1 + (size_u e1) + (size_p p1) + (size_u e2)
    | u_if0 e1 e2 e3 => 1 + (size_u e1) + (size_u e2) + (size_u e3)
    | u_ann u2 t1 => 1 + (size_u u2) + (size_t t1)
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
  fun H1 H2 H3 H4 H5 H6 H7 =>
  degree_t_wrt_t_ind' H1 H2 H3 H4 H5 H6 H7.

Hint Constructors degree_t_wrt_t : core lngen.

Inductive degree_u_wrt_u : nat -> u -> Prop :=
  | degree_wrt_u_u_var_f : forall n1 x1,
    degree_u_wrt_u n1 (u_var_f x1)
  | degree_wrt_u_u_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_u_wrt_u n1 (u_var_b n2)
  | degree_wrt_u_u_int : forall n1 i1,
    degree_u_wrt_u n1 (u_int i1)
  | degree_wrt_u_u_fix : forall n1 t1 t2 e1,
    degree_u_wrt_u (S n1) e1 ->
    degree_u_wrt_u n1 (u_fix t1 t2 e1)
  | degree_wrt_u_u_lam : forall n1 t1 e1,
    degree_u_wrt_u (S n1) e1 ->
    degree_u_wrt_u n1 (u_lam t1 e1)
  | degree_wrt_u_u_app : forall n1 e1 e2,
    degree_u_wrt_u n1 e1 ->
    degree_u_wrt_u n1 e2 ->
    degree_u_wrt_u n1 (u_app e1 e2)
  | degree_wrt_u_u_tlam : forall n1 e1,
    degree_u_wrt_u n1 e1 ->
    degree_u_wrt_u n1 (u_tlam e1)
  | degree_wrt_u_u_tapp : forall n1 e1 t1,
    degree_u_wrt_u n1 e1 ->
    degree_u_wrt_u n1 (u_tapp e1 t1)
  | degree_wrt_u_u_pair : forall n1 e1 e2,
    degree_u_wrt_u n1 e1 ->
    degree_u_wrt_u n1 e2 ->
    degree_u_wrt_u n1 (u_pair e1 e2)
  | degree_wrt_u_u_prl : forall n1 e1,
    degree_u_wrt_u n1 e1 ->
    degree_u_wrt_u n1 (u_prl e1)
  | degree_wrt_u_u_prr : forall n1 e1,
    degree_u_wrt_u n1 e1 ->
    degree_u_wrt_u n1 (u_prr e1)
  | degree_wrt_u_u_prim : forall n1 e1 p1 e2,
    degree_u_wrt_u n1 e1 ->
    degree_u_wrt_u n1 e2 ->
    degree_u_wrt_u n1 (u_prim e1 p1 e2)
  | degree_wrt_u_u_if0 : forall n1 e1 e2 e3,
    degree_u_wrt_u n1 e1 ->
    degree_u_wrt_u n1 e2 ->
    degree_u_wrt_u n1 e3 ->
    degree_u_wrt_u n1 (u_if0 e1 e2 e3)
  | degree_wrt_u_u_ann : forall n1 u1 t1,
    degree_u_wrt_u n1 u1 ->
    degree_u_wrt_u n1 (u_ann u1 t1).

Inductive degree_u_wrt_t : nat -> u -> Prop :=
  | degree_wrt_t_u_var_f : forall n1 x1,
    degree_u_wrt_t n1 (u_var_f x1)
  | degree_wrt_t_u_var_b : forall n1 n2,
    degree_u_wrt_t n1 (u_var_b n2)
  | degree_wrt_t_u_int : forall n1 i1,
    degree_u_wrt_t n1 (u_int i1)
  | degree_wrt_t_u_fix : forall n1 t1 t2 e1,
    degree_t_wrt_t n1 t1 ->
    degree_t_wrt_t n1 t2 ->
    degree_u_wrt_t n1 e1 ->
    degree_u_wrt_t n1 (u_fix t1 t2 e1)
  | degree_wrt_t_u_lam : forall n1 t1 e1,
    degree_t_wrt_t n1 t1 ->
    degree_u_wrt_t n1 e1 ->
    degree_u_wrt_t n1 (u_lam t1 e1)
  | degree_wrt_t_u_app : forall n1 e1 e2,
    degree_u_wrt_t n1 e1 ->
    degree_u_wrt_t n1 e2 ->
    degree_u_wrt_t n1 (u_app e1 e2)
  | degree_wrt_t_u_tlam : forall n1 e1,
    degree_u_wrt_t (S n1) e1 ->
    degree_u_wrt_t n1 (u_tlam e1)
  | degree_wrt_t_u_tapp : forall n1 e1 t1,
    degree_u_wrt_t n1 e1 ->
    degree_t_wrt_t n1 t1 ->
    degree_u_wrt_t n1 (u_tapp e1 t1)
  | degree_wrt_t_u_pair : forall n1 e1 e2,
    degree_u_wrt_t n1 e1 ->
    degree_u_wrt_t n1 e2 ->
    degree_u_wrt_t n1 (u_pair e1 e2)
  | degree_wrt_t_u_prl : forall n1 e1,
    degree_u_wrt_t n1 e1 ->
    degree_u_wrt_t n1 (u_prl e1)
  | degree_wrt_t_u_prr : forall n1 e1,
    degree_u_wrt_t n1 e1 ->
    degree_u_wrt_t n1 (u_prr e1)
  | degree_wrt_t_u_prim : forall n1 e1 p1 e2,
    degree_u_wrt_t n1 e1 ->
    degree_u_wrt_t n1 e2 ->
    degree_u_wrt_t n1 (u_prim e1 p1 e2)
  | degree_wrt_t_u_if0 : forall n1 e1 e2 e3,
    degree_u_wrt_t n1 e1 ->
    degree_u_wrt_t n1 e2 ->
    degree_u_wrt_t n1 e3 ->
    degree_u_wrt_t n1 (u_if0 e1 e2 e3)
  | degree_wrt_t_u_ann : forall n1 u1 t1,
    degree_u_wrt_t n1 u1 ->
    degree_t_wrt_t n1 t1 ->
    degree_u_wrt_t n1 (u_ann u1 t1).

Scheme degree_u_wrt_u_ind' := Induction for degree_u_wrt_u Sort Prop.

Definition degree_u_wrt_u_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  degree_u_wrt_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.

Scheme degree_u_wrt_t_ind' := Induction for degree_u_wrt_t Sort Prop.

Definition degree_u_wrt_t_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  degree_u_wrt_t_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.

Hint Constructors degree_u_wrt_u : core lngen.

Hint Constructors degree_u_wrt_t : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_t : t -> Set :=
  | lc_set_t_var_f : forall a1,
    lc_set_t (t_var_f a1)
  | lc_set_t_int :
    lc_set_t (t_int)
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
  fun H1 H2 H3 H4 H5 H6 =>
  lc_t_ind' H1 H2 H3 H4 H5 H6.

Scheme lc_set_t_ind' := Induction for lc_set_t Sort Prop.

Definition lc_set_t_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_set_t_ind' H1 H2 H3 H4 H5 H6.

Scheme lc_set_t_rec' := Induction for lc_set_t Sort Set.

Definition lc_set_t_mutrec :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_set_t_rec' H1 H2 H3 H4 H5 H6.

Hint Constructors lc_t : core lngen.

Hint Constructors lc_set_t : core lngen.

Inductive lc_set_u : u -> Set :=
  | lc_set_u_var_f : forall x1,
    lc_set_u (u_var_f x1)
  | lc_set_u_int : forall i1,
    lc_set_u (u_int i1)
  | lc_set_u_fix : forall t1 t2 e1,
    lc_set_t t1 ->
    lc_set_t t2 ->
    (forall x1 : x, lc_set_u (open_u_wrt_u e1 (u_var_f x1))) ->
    lc_set_u (u_fix t1 t2 e1)
  | lc_set_u_lam : forall t1 e1,
    lc_set_t t1 ->
    (forall x1 : x, lc_set_u (open_u_wrt_u e1 (u_var_f x1))) ->
    lc_set_u (u_lam t1 e1)
  | lc_set_u_app : forall e1 e2,
    lc_set_u e1 ->
    lc_set_u e2 ->
    lc_set_u (u_app e1 e2)
  | lc_set_u_tlam : forall e1,
    (forall a1 : a, lc_set_u (open_u_wrt_t e1 (t_var_f a1))) ->
    lc_set_u (u_tlam e1)
  | lc_set_u_tapp : forall e1 t1,
    lc_set_u e1 ->
    lc_set_t t1 ->
    lc_set_u (u_tapp e1 t1)
  | lc_set_u_pair : forall e1 e2,
    lc_set_u e1 ->
    lc_set_u e2 ->
    lc_set_u (u_pair e1 e2)
  | lc_set_u_prl : forall e1,
    lc_set_u e1 ->
    lc_set_u (u_prl e1)
  | lc_set_u_prr : forall e1,
    lc_set_u e1 ->
    lc_set_u (u_prr e1)
  | lc_set_u_prim : forall e1 p1 e2,
    lc_set_u e1 ->
    lc_set_u e2 ->
    lc_set_u (u_prim e1 p1 e2)
  | lc_set_u_if0 : forall e1 e2 e3,
    lc_set_u e1 ->
    lc_set_u e2 ->
    lc_set_u e3 ->
    lc_set_u (u_if0 e1 e2 e3)
  | lc_set_u_ann : forall u1 t1,
    lc_set_u u1 ->
    lc_set_t t1 ->
    lc_set_u (u_ann u1 t1).

Scheme lc_u_ind' := Induction for lc_u Sort Prop.

Definition lc_u_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  lc_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Scheme lc_set_u_ind' := Induction for lc_set_u Sort Prop.

Definition lc_set_u_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  lc_set_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Scheme lc_set_u_rec' := Induction for lc_set_u Sort Set.

Definition lc_set_u_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  lc_set_u_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Hint Constructors lc_u : core lngen.

Hint Constructors lc_set_u : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_t_wrt_t t1 := forall a1, lc_t (open_t_wrt_t t1 (t_var_f a1)).

Hint Unfold body_t_wrt_t.

Definition body_u_wrt_u u1 := forall x1, lc_u (open_u_wrt_u u1 (u_var_f x1)).

Definition body_u_wrt_t u1 := forall a1, lc_u (open_u_wrt_t u1 (t_var_f a1)).

Hint Unfold body_u_wrt_u.

Hint Unfold body_u_wrt_t.


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

Lemma size_u_min_mutual :
(forall u1, 1 <= size_u u1).
Proof. Admitted.

(* end hide *)

Lemma size_u_min :
forall u1, 1 <= size_u u1.
Proof. Admitted.

Hint Resolve size_u_min : lngen.

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

Lemma size_u_close_u_wrt_u_rec_mutual :
(forall u1 x1 n1,
  size_u (close_u_wrt_u_rec n1 x1 u1) = size_u u1).
Proof. Admitted.

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

Lemma size_u_close_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  size_u (close_u_wrt_t_rec n1 a1 u1) = size_u u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_u_close_u_wrt_t_rec :
forall u1 a1 n1,
  size_u (close_u_wrt_t_rec n1 a1 u1) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_close_u_wrt_t_rec : lngen.
Hint Rewrite size_u_close_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_t_close_t_wrt_t :
forall t1 a1,
  size_t (close_t_wrt_t a1 t1) = size_t t1.
Proof. Admitted.

Hint Resolve size_t_close_t_wrt_t : lngen.
Hint Rewrite size_t_close_t_wrt_t using solve [auto] : lngen.

Lemma size_u_close_u_wrt_u :
forall u1 x1,
  size_u (close_u_wrt_u x1 u1) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_close_u_wrt_u : lngen.
Hint Rewrite size_u_close_u_wrt_u using solve [auto] : lngen.

Lemma size_u_close_u_wrt_t :
forall u1 a1,
  size_u (close_u_wrt_t a1 u1) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_close_u_wrt_t : lngen.
Hint Rewrite size_u_close_u_wrt_t using solve [auto] : lngen.

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

Lemma size_u_open_u_wrt_u_rec_mutual :
(forall u1 u2 n1,
  size_u u1 <= size_u (open_u_wrt_u_rec n1 u2 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_u_rec :
forall u1 u2 n1,
  size_u u1 <= size_u (open_u_wrt_u_rec n1 u2 u1).
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_t_rec_mutual :
(forall u1 t1 n1,
  size_u u1 <= size_u (open_u_wrt_t_rec n1 t1 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_t_rec :
forall u1 t1 n1,
  size_u u1 <= size_u (open_u_wrt_t_rec n1 t1 u1).
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_t_rec : lngen.

(* end hide *)

Lemma size_t_open_t_wrt_t :
forall t1 t2,
  size_t t1 <= size_t (open_t_wrt_t t1 t2).
Proof. Admitted.

Hint Resolve size_t_open_t_wrt_t : lngen.

Lemma size_u_open_u_wrt_u :
forall u1 u2,
  size_u u1 <= size_u (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_u : lngen.

Lemma size_u_open_u_wrt_t :
forall u1 t1,
  size_u u1 <= size_u (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_t : lngen.

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

Lemma size_u_open_u_wrt_u_rec_var_mutual :
(forall u1 x1 n1,
  size_u (open_u_wrt_u_rec n1 (u_var_f x1) u1) = size_u u1).
Proof. Admitted.

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

Lemma size_u_open_u_wrt_t_rec_var_mutual :
(forall u1 a1 n1,
  size_u (open_u_wrt_t_rec n1 (t_var_f a1) u1) = size_u u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_t_rec_var :
forall u1 a1 n1,
  size_u (open_u_wrt_t_rec n1 (t_var_f a1) u1) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_t_rec_var : lngen.
Hint Rewrite size_u_open_u_wrt_t_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_t_open_t_wrt_t_var :
forall t1 a1,
  size_t (open_t_wrt_t t1 (t_var_f a1)) = size_t t1.
Proof. Admitted.

Hint Resolve size_t_open_t_wrt_t_var : lngen.
Hint Rewrite size_t_open_t_wrt_t_var using solve [auto] : lngen.

Lemma size_u_open_u_wrt_u_var :
forall u1 x1,
  size_u (open_u_wrt_u u1 (u_var_f x1)) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_u_var : lngen.
Hint Rewrite size_u_open_u_wrt_u_var using solve [auto] : lngen.

Lemma size_u_open_u_wrt_t_var :
forall u1 a1,
  size_u (open_u_wrt_t u1 (t_var_f a1)) = size_u u1.
Proof. Admitted.

Hint Resolve size_u_open_u_wrt_t_var : lngen.
Hint Rewrite size_u_open_u_wrt_t_var using solve [auto] : lngen.


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

Lemma degree_u_wrt_u_S_mutual :
(forall n1 u1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u (S n1) u1).
Proof. Admitted.

(* end hide *)

Lemma degree_u_wrt_u_S :
forall n1 u1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u (S n1) u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_u_S : lngen.

(* begin hide *)

Lemma degree_u_wrt_t_S_mutual :
(forall n1 u1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) u1).
Proof. Admitted.

(* end hide *)

Lemma degree_u_wrt_t_S :
forall n1 u1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_t_S : lngen.

Lemma degree_t_wrt_t_O :
forall n1 t1,
  degree_t_wrt_t O t1 ->
  degree_t_wrt_t n1 t1.
Proof. Admitted.

Hint Resolve degree_t_wrt_t_O : lngen.

Lemma degree_u_wrt_u_O :
forall n1 u1,
  degree_u_wrt_u O u1 ->
  degree_u_wrt_u n1 u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_u_O : lngen.

Lemma degree_u_wrt_t_O :
forall n1 u1,
  degree_u_wrt_t O u1 ->
  degree_u_wrt_t n1 u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_t_O : lngen.

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

Lemma degree_u_wrt_u_close_u_wrt_u_rec_mutual :
(forall u1 x1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u (S n1) (close_u_wrt_u_rec n1 x1 u1)).
Proof. Admitted.

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

Lemma degree_u_wrt_u_close_u_wrt_t_rec_mutual :
(forall u1 a1 n1 n2,
  degree_u_wrt_u n2 u1 ->
  degree_u_wrt_u n2 (close_u_wrt_t_rec n1 a1 u1)).
Proof. Admitted.

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

Lemma degree_u_wrt_t_close_u_wrt_u_rec_mutual :
(forall u1 x1 n1 n2,
  degree_u_wrt_t n2 u1 ->
  degree_u_wrt_t n2 (close_u_wrt_u_rec n1 x1 u1)).
Proof. Admitted.

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

Lemma degree_u_wrt_t_close_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_close_u_wrt_t_rec :
forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_close_u_wrt_t_rec : lngen.

(* end hide *)

Lemma degree_t_wrt_t_close_t_wrt_t :
forall t1 a1,
  degree_t_wrt_t 0 t1 ->
  degree_t_wrt_t 1 (close_t_wrt_t a1 t1).
Proof. Admitted.

Hint Resolve degree_t_wrt_t_close_t_wrt_t : lngen.

Lemma degree_u_wrt_u_close_u_wrt_u :
forall u1 x1,
  degree_u_wrt_u 0 u1 ->
  degree_u_wrt_u 1 (close_u_wrt_u x1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_close_u_wrt_u : lngen.

Lemma degree_u_wrt_u_close_u_wrt_t :
forall u1 a1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (close_u_wrt_t a1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_close_u_wrt_t : lngen.

Lemma degree_u_wrt_t_close_u_wrt_u :
forall u1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 (close_u_wrt_u x1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_close_u_wrt_u : lngen.

Lemma degree_u_wrt_t_close_u_wrt_t :
forall u1 a1,
  degree_u_wrt_t 0 u1 ->
  degree_u_wrt_t 1 (close_u_wrt_t a1 u1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_close_u_wrt_t : lngen.

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

Lemma degree_u_wrt_u_close_u_wrt_u_rec_inv_mutual :
(forall u1 x1 n1,
  degree_u_wrt_u (S n1) (close_u_wrt_u_rec n1 x1 u1) ->
  degree_u_wrt_u n1 u1).
Proof. Admitted.

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

Lemma degree_u_wrt_u_close_u_wrt_t_rec_inv_mutual :
(forall u1 a1 n1 n2,
  degree_u_wrt_u n2 (close_u_wrt_t_rec n1 a1 u1) ->
  degree_u_wrt_u n2 u1).
Proof. Admitted.

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

Lemma degree_u_wrt_t_close_u_wrt_u_rec_inv_mutual :
(forall u1 x1 n1 n2,
  degree_u_wrt_t n2 (close_u_wrt_u_rec n1 x1 u1) ->
  degree_u_wrt_t n2 u1).
Proof. Admitted.

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

Lemma degree_u_wrt_t_close_u_wrt_t_rec_inv_mutual :
(forall u1 a1 n1,
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1) ->
  degree_u_wrt_t n1 u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_close_u_wrt_t_rec_inv :
forall u1 a1 n1,
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1) ->
  degree_u_wrt_t n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_close_u_wrt_t_rec_inv : lngen.

(* end hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_inv :
forall t1 a1,
  degree_t_wrt_t 1 (close_t_wrt_t a1 t1) ->
  degree_t_wrt_t 0 t1.
Proof. Admitted.

Hint Immediate degree_t_wrt_t_close_t_wrt_t_inv : lngen.

Lemma degree_u_wrt_u_close_u_wrt_u_inv :
forall u1 x1,
  degree_u_wrt_u 1 (close_u_wrt_u x1 u1) ->
  degree_u_wrt_u 0 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_close_u_wrt_u_inv : lngen.

Lemma degree_u_wrt_u_close_u_wrt_t_inv :
forall u1 a1 n1,
  degree_u_wrt_u n1 (close_u_wrt_t a1 u1) ->
  degree_u_wrt_u n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_close_u_wrt_t_inv : lngen.

Lemma degree_u_wrt_t_close_u_wrt_u_inv :
forall u1 x1 n1,
  degree_u_wrt_t n1 (close_u_wrt_u x1 u1) ->
  degree_u_wrt_t n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_close_u_wrt_u_inv : lngen.

Lemma degree_u_wrt_t_close_u_wrt_t_inv :
forall u1 a1,
  degree_u_wrt_t 1 (close_u_wrt_t a1 u1) ->
  degree_u_wrt_t 0 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_close_u_wrt_t_inv : lngen.

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

Lemma degree_u_wrt_u_open_u_wrt_u_rec_mutual :
(forall u1 u2 n1,
  degree_u_wrt_u (S n1) u1 ->
  degree_u_wrt_u n1 u2 ->
  degree_u_wrt_u n1 (open_u_wrt_u_rec n1 u2 u1)).
Proof. Admitted.

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

Lemma degree_u_wrt_u_open_u_wrt_t_rec_mutual :
(forall u1 t1 n1 n2,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (open_u_wrt_t_rec n2 t1 u1)).
Proof. Admitted.

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

Lemma degree_u_wrt_t_open_u_wrt_u_rec_mutual :
(forall u1 u2 n1 n2,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 u2 ->
  degree_u_wrt_t n1 (open_u_wrt_u_rec n2 u2 u1)).
Proof. Admitted.

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

Lemma degree_u_wrt_t_open_u_wrt_t_rec_mutual :
(forall u1 t1 n1,
  degree_u_wrt_t (S n1) u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1)).
Proof. Admitted.

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

Lemma degree_t_wrt_t_open_t_wrt_t :
forall t1 t2,
  degree_t_wrt_t 1 t1 ->
  degree_t_wrt_t 0 t2 ->
  degree_t_wrt_t 0 (open_t_wrt_t t1 t2).
Proof. Admitted.

Hint Resolve degree_t_wrt_t_open_t_wrt_t : lngen.

Lemma degree_u_wrt_u_open_u_wrt_u :
forall u1 u2,
  degree_u_wrt_u 1 u1 ->
  degree_u_wrt_u 0 u2 ->
  degree_u_wrt_u 0 (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_open_u_wrt_u : lngen.

Lemma degree_u_wrt_u_open_u_wrt_t :
forall u1 t1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve degree_u_wrt_u_open_u_wrt_t : lngen.

Lemma degree_u_wrt_t_open_u_wrt_u :
forall u1 u2 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 u2 ->
  degree_u_wrt_t n1 (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_open_u_wrt_u : lngen.

Lemma degree_u_wrt_t_open_u_wrt_t :
forall u1 t1,
  degree_u_wrt_t 1 u1 ->
  degree_t_wrt_t 0 t1 ->
  degree_u_wrt_t 0 (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve degree_u_wrt_t_open_u_wrt_t : lngen.

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

Lemma degree_u_wrt_u_open_u_wrt_u_rec_inv_mutual :
(forall u1 u2 n1,
  degree_u_wrt_u n1 (open_u_wrt_u_rec n1 u2 u1) ->
  degree_u_wrt_u (S n1) u1).
Proof. Admitted.

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

Lemma degree_u_wrt_u_open_u_wrt_t_rec_inv_mutual :
(forall u1 t1 n1 n2,
  degree_u_wrt_u n1 (open_u_wrt_t_rec n2 t1 u1) ->
  degree_u_wrt_u n1 u1).
Proof. Admitted.

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

Lemma degree_u_wrt_t_open_u_wrt_u_rec_inv_mutual :
(forall u1 u2 n1 n2,
  degree_u_wrt_t n1 (open_u_wrt_u_rec n2 u2 u1) ->
  degree_u_wrt_t n1 u1).
Proof. Admitted.

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

Lemma degree_u_wrt_t_open_u_wrt_t_rec_inv_mutual :
(forall u1 t1 n1,
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1) ->
  degree_u_wrt_t (S n1) u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_open_u_wrt_t_rec_inv :
forall u1 t1 n1,
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1) ->
  degree_u_wrt_t (S n1) u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_open_u_wrt_t_rec_inv : lngen.

(* end hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_inv :
forall t1 t2,
  degree_t_wrt_t 0 (open_t_wrt_t t1 t2) ->
  degree_t_wrt_t 1 t1.
Proof. Admitted.

Hint Immediate degree_t_wrt_t_open_t_wrt_t_inv : lngen.

Lemma degree_u_wrt_u_open_u_wrt_u_inv :
forall u1 u2,
  degree_u_wrt_u 0 (open_u_wrt_u u1 u2) ->
  degree_u_wrt_u 1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_open_u_wrt_u_inv : lngen.

Lemma degree_u_wrt_u_open_u_wrt_t_inv :
forall u1 t1 n1,
  degree_u_wrt_u n1 (open_u_wrt_t u1 t1) ->
  degree_u_wrt_u n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_u_open_u_wrt_t_inv : lngen.

Lemma degree_u_wrt_t_open_u_wrt_u_inv :
forall u1 u2 n1,
  degree_u_wrt_t n1 (open_u_wrt_u u1 u2) ->
  degree_u_wrt_t n1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_open_u_wrt_u_inv : lngen.

Lemma degree_u_wrt_t_open_u_wrt_t_inv :
forall u1 t1,
  degree_u_wrt_t 0 (open_u_wrt_t u1 t1) ->
  degree_u_wrt_t 1 u1.
Proof. Admitted.

Hint Immediate degree_u_wrt_t_open_u_wrt_t_inv : lngen.


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

Lemma close_u_wrt_u_rec_inj_mutual :
(forall u1 u2 x1 n1,
  close_u_wrt_u_rec n1 x1 u1 = close_u_wrt_u_rec n1 x1 u2 ->
  u1 = u2).
Proof. Admitted.

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

Lemma close_u_wrt_t_rec_inj_mutual :
(forall u1 u2 a1 n1,
  close_u_wrt_t_rec n1 a1 u1 = close_u_wrt_t_rec n1 a1 u2 ->
  u1 = u2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_t_rec_inj :
forall u1 u2 a1 n1,
  close_u_wrt_t_rec n1 a1 u1 = close_u_wrt_t_rec n1 a1 u2 ->
  u1 = u2.
Proof. Admitted.

Hint Immediate close_u_wrt_t_rec_inj : lngen.

(* end hide *)

Lemma close_t_wrt_t_inj :
forall t1 t2 a1,
  close_t_wrt_t a1 t1 = close_t_wrt_t a1 t2 ->
  t1 = t2.
Proof. Admitted.

Hint Immediate close_t_wrt_t_inj : lngen.

Lemma close_u_wrt_u_inj :
forall u1 u2 x1,
  close_u_wrt_u x1 u1 = close_u_wrt_u x1 u2 ->
  u1 = u2.
Proof. Admitted.

Hint Immediate close_u_wrt_u_inj : lngen.

Lemma close_u_wrt_t_inj :
forall u1 u2 a1,
  close_u_wrt_t a1 u1 = close_u_wrt_t a1 u2 ->
  u1 = u2.
Proof. Admitted.

Hint Immediate close_u_wrt_t_inj : lngen.

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

Lemma close_u_wrt_u_rec_open_u_wrt_u_rec_mutual :
(forall u1 x1 n1,
  x1 `notin` e_fv_u u1 ->
  close_u_wrt_u_rec n1 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1) = u1).
Proof. Admitted.

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

Lemma close_u_wrt_t_rec_open_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t_rec n1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1) = u1).
Proof. Admitted.

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

Lemma close_t_wrt_t_open_t_wrt_t :
forall t1 a1,
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t a1 (open_t_wrt_t t1 (t_var_f a1)) = t1.
Proof. Admitted.

Hint Resolve close_t_wrt_t_open_t_wrt_t : lngen.
Hint Rewrite close_t_wrt_t_open_t_wrt_t using solve [auto] : lngen.

Lemma close_u_wrt_u_open_u_wrt_u :
forall u1 x1,
  x1 `notin` e_fv_u u1 ->
  close_u_wrt_u x1 (open_u_wrt_u u1 (u_var_f x1)) = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_u_open_u_wrt_u : lngen.
Hint Rewrite close_u_wrt_u_open_u_wrt_u using solve [auto] : lngen.

Lemma close_u_wrt_t_open_u_wrt_t :
forall u1 a1,
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t a1 (open_u_wrt_t u1 (t_var_f a1)) = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_t_open_u_wrt_t : lngen.
Hint Rewrite close_u_wrt_t_open_u_wrt_t using solve [auto] : lngen.

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

Lemma open_u_wrt_u_rec_close_u_wrt_u_rec_mutual :
(forall u1 x1 n1,
  open_u_wrt_u_rec n1 (u_var_f x1) (close_u_wrt_u_rec n1 x1 u1) = u1).
Proof. Admitted.

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

Lemma open_u_wrt_t_rec_close_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  open_u_wrt_t_rec n1 (t_var_f a1) (close_u_wrt_t_rec n1 a1 u1) = u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_t_rec_close_u_wrt_t_rec :
forall u1 a1 n1,
  open_u_wrt_t_rec n1 (t_var_f a1) (close_u_wrt_t_rec n1 a1 u1) = u1.
Proof. Admitted.

Hint Resolve open_u_wrt_t_rec_close_u_wrt_t_rec : lngen.
Hint Rewrite open_u_wrt_t_rec_close_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_t_wrt_t_close_t_wrt_t :
forall t1 a1,
  open_t_wrt_t (close_t_wrt_t a1 t1) (t_var_f a1) = t1.
Proof. Admitted.

Hint Resolve open_t_wrt_t_close_t_wrt_t : lngen.
Hint Rewrite open_t_wrt_t_close_t_wrt_t using solve [auto] : lngen.

Lemma open_u_wrt_u_close_u_wrt_u :
forall u1 x1,
  open_u_wrt_u (close_u_wrt_u x1 u1) (u_var_f x1) = u1.
Proof. Admitted.

Hint Resolve open_u_wrt_u_close_u_wrt_u : lngen.
Hint Rewrite open_u_wrt_u_close_u_wrt_u using solve [auto] : lngen.

Lemma open_u_wrt_t_close_u_wrt_t :
forall u1 a1,
  open_u_wrt_t (close_u_wrt_t a1 u1) (t_var_f a1) = u1.
Proof. Admitted.

Hint Resolve open_u_wrt_t_close_u_wrt_t : lngen.
Hint Rewrite open_u_wrt_t_close_u_wrt_t using solve [auto] : lngen.

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

Lemma open_u_wrt_u_rec_inj_mutual :
(forall u2 u1 x1 n1,
  x1 `notin` e_fv_u u2 ->
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u_rec n1 (u_var_f x1) u2 = open_u_wrt_u_rec n1 (u_var_f x1) u1 ->
  u2 = u1).
Proof. Admitted.

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

Lemma open_u_wrt_t_rec_inj_mutual :
(forall u2 u1 a1 n1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 (t_var_f a1) u2 = open_u_wrt_t_rec n1 (t_var_f a1) u1 ->
  u2 = u1).
Proof. Admitted.

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

Lemma open_t_wrt_t_inj :
forall t2 t1 a1,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t t2 (t_var_f a1) = open_t_wrt_t t1 (t_var_f a1) ->
  t2 = t1.
Proof. Admitted.

Hint Immediate open_t_wrt_t_inj : lngen.

Lemma open_u_wrt_u_inj :
forall u2 u1 x1,
  x1 `notin` e_fv_u u2 ->
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u u2 (u_var_f x1) = open_u_wrt_u u1 (u_var_f x1) ->
  u2 = u1.
Proof. Admitted.

Hint Immediate open_u_wrt_u_inj : lngen.

Lemma open_u_wrt_t_inj :
forall u2 u1 a1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t u2 (t_var_f a1) = open_u_wrt_t u1 (t_var_f a1) ->
  u2 = u1.
Proof. Admitted.

Hint Immediate open_u_wrt_t_inj : lngen.


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

Lemma degree_u_wrt_u_of_lc_u_mutual :
(forall u1,
  lc_u u1 ->
  degree_u_wrt_u 0 u1).
Proof. Admitted.

(* end hide *)

Lemma degree_u_wrt_u_of_lc_u :
forall u1,
  lc_u u1 ->
  degree_u_wrt_u 0 u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_u_of_lc_u : lngen.

(* begin hide *)

Lemma degree_u_wrt_t_of_lc_u_mutual :
(forall u1,
  lc_u u1 ->
  degree_u_wrt_t 0 u1).
Proof. Admitted.

(* end hide *)

Lemma degree_u_wrt_t_of_lc_u :
forall u1,
  lc_u u1 ->
  degree_u_wrt_t 0 u1.
Proof. Admitted.

Hint Resolve degree_u_wrt_t_of_lc_u : lngen.

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

Lemma lc_u_of_degree_size_mutual :
forall i1,
(forall u1,
  size_u u1 = i1 ->
  degree_u_wrt_u 0 u1 ->
  degree_u_wrt_t 0 u1 ->
  lc_u u1).
Proof. Admitted.

(* end hide *)

Lemma lc_u_of_degree :
forall u1,
  degree_u_wrt_u 0 u1 ->
  degree_u_wrt_t 0 u1 ->
  lc_u u1.
Proof. Admitted.

Hint Resolve lc_u_of_degree : lngen.

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

Ltac u_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_u_wrt_u_of_lc_u in J1;
              let J2 := fresh in pose proof H as J2; apply degree_u_wrt_t_of_lc_u in J2; clear H
          end).

Lemma lc_t_all_exists :
forall a1 t1,
  lc_t (open_t_wrt_t t1 (t_var_f a1)) ->
  lc_t (t_all t1).
Proof. Admitted.

Lemma lc_u_fix_exists :
forall x1 t1 t2 e1,
  lc_t t1 ->
  lc_t t2 ->
  lc_u (open_u_wrt_u e1 (u_var_f x1)) ->
  lc_u (u_fix t1 t2 e1).
Proof. Admitted.

Lemma lc_u_lam_exists :
forall x1 t1 e1,
  lc_t t1 ->
  lc_u (open_u_wrt_u e1 (u_var_f x1)) ->
  lc_u (u_lam t1 e1).
Proof. Admitted.

Lemma lc_u_tlam_exists :
forall a1 e1,
  lc_u (open_u_wrt_t e1 (t_var_f a1)) ->
  lc_u (u_tlam e1).
Proof. Admitted.

Hint Extern 1 (lc_t (t_all _)) =>
  let a1 := fresh in
  pick_fresh a1;
  apply (lc_t_all_exists a1).

Hint Extern 1 (lc_u (u_fix _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_u_fix_exists x1).

Hint Extern 1 (lc_u (u_lam _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_u_lam_exists x1).

Hint Extern 1 (lc_u (u_tlam _)) =>
  let a1 := fresh in
  pick_fresh a1;
  apply (lc_u_tlam_exists a1).

Lemma lc_body_t_wrt_t :
forall t1 t2,
  body_t_wrt_t t1 ->
  lc_t t2 ->
  lc_t (open_t_wrt_t t1 t2).
Proof. Admitted.

Hint Resolve lc_body_t_wrt_t : lngen.

Lemma lc_body_u_wrt_u :
forall u1 u2,
  body_u_wrt_u u1 ->
  lc_u u2 ->
  lc_u (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve lc_body_u_wrt_u : lngen.

Lemma lc_body_u_wrt_t :
forall u1 t1,
  body_u_wrt_t u1 ->
  lc_t t1 ->
  lc_u (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve lc_body_u_wrt_t : lngen.

Lemma lc_body_t_all_1 :
forall t1,
  lc_t (t_all t1) ->
  body_t_wrt_t t1.
Proof. Admitted.

Hint Resolve lc_body_t_all_1 : lngen.

Lemma lc_body_u_fix_3 :
forall t1 t2 e1,
  lc_u (u_fix t1 t2 e1) ->
  body_u_wrt_u e1.
Proof. Admitted.

Hint Resolve lc_body_u_fix_3 : lngen.

Lemma lc_body_u_lam_2 :
forall t1 e1,
  lc_u (u_lam t1 e1) ->
  body_u_wrt_u e1.
Proof. Admitted.

Hint Resolve lc_body_u_lam_2 : lngen.

Lemma lc_body_u_tlam_1 :
forall e1,
  lc_u (u_tlam e1) ->
  body_u_wrt_t e1.
Proof. Admitted.

Hint Resolve lc_body_u_tlam_1 : lngen.

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

Lemma lc_u_unique_mutual :
(forall u1 (proof2 proof3 : lc_u u1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_u_unique :
forall u1 (proof2 proof3 : lc_u u1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_u_unique : lngen.

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

Lemma lc_u_of_lc_set_u_mutual :
(forall u1, lc_set_u u1 -> lc_u u1).
Proof. Admitted.

(* end hide *)

Lemma lc_u_of_lc_set_u :
forall u1, lc_set_u u1 -> lc_u u1.
Proof. Admitted.

Hint Resolve lc_u_of_lc_set_u : lngen.

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

Lemma lc_set_u_of_lc_u_size_mutual :
forall i1,
(forall u1,
  size_u u1 = i1 ->
  lc_u u1 ->
  lc_set_u u1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_u_of_lc_u :
forall u1,
  lc_u u1 ->
  lc_set_u u1.
Proof. Admitted.

Hint Resolve lc_set_u_of_lc_u : lngen.


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

Lemma close_u_wrt_u_rec_degree_u_wrt_u_mutual :
(forall u1 x1 n1,
  degree_u_wrt_u n1 u1 ->
  x1 `notin` e_fv_u u1 ->
  close_u_wrt_u_rec n1 x1 u1 = u1).
Proof. Admitted.

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

Lemma close_u_wrt_t_rec_degree_u_wrt_t_mutual :
(forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t_rec n1 a1 u1 = u1).
Proof. Admitted.

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

Lemma close_t_wrt_t_lc_t :
forall t1 a1,
  lc_t t1 ->
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t a1 t1 = t1.
Proof. Admitted.

Hint Resolve close_t_wrt_t_lc_t : lngen.
Hint Rewrite close_t_wrt_t_lc_t using solve [auto] : lngen.

Lemma close_u_wrt_u_lc_u :
forall u1 x1,
  lc_u u1 ->
  x1 `notin` e_fv_u u1 ->
  close_u_wrt_u x1 u1 = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_u_lc_u : lngen.
Hint Rewrite close_u_wrt_u_lc_u using solve [auto] : lngen.

Lemma close_u_wrt_t_lc_u :
forall u1 a1,
  lc_u u1 ->
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t a1 u1 = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_t_lc_u : lngen.
Hint Rewrite close_u_wrt_t_lc_u using solve [auto] : lngen.

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

Lemma open_u_wrt_u_rec_degree_u_wrt_u_mutual :
(forall u2 u1 n1,
  degree_u_wrt_u n1 u2 ->
  open_u_wrt_u_rec n1 u1 u2 = u2).
Proof. Admitted.

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

Lemma open_u_wrt_t_rec_degree_u_wrt_t_mutual :
(forall u1 t1 n1,
  degree_u_wrt_t n1 u1 ->
  open_u_wrt_t_rec n1 t1 u1 = u1).
Proof. Admitted.

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

Lemma open_t_wrt_t_lc_t :
forall t2 t1,
  lc_t t2 ->
  open_t_wrt_t t2 t1 = t2.
Proof. Admitted.

Hint Resolve open_t_wrt_t_lc_t : lngen.
Hint Rewrite open_t_wrt_t_lc_t using solve [auto] : lngen.

Lemma open_u_wrt_u_lc_u :
forall u2 u1,
  lc_u u2 ->
  open_u_wrt_u u2 u1 = u2.
Proof. Admitted.

Hint Resolve open_u_wrt_u_lc_u : lngen.
Hint Rewrite open_u_wrt_u_lc_u using solve [auto] : lngen.

Lemma open_u_wrt_t_lc_u :
forall u1 t1,
  lc_u u1 ->
  open_u_wrt_t u1 t1 = u1.
Proof. Admitted.

Hint Resolve open_u_wrt_t_lc_u : lngen.
Hint Rewrite open_u_wrt_t_lc_u using solve [auto] : lngen.


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

Lemma e_fv_u_close_u_wrt_u_rec_mutual :
(forall u1 x1 n1,
  e_fv_u (close_u_wrt_u_rec n1 x1 u1) [=] remove x1 (e_fv_u u1)).
Proof. Admitted.

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

Lemma e_fv_u_close_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  e_fv_u (close_u_wrt_t_rec n1 a1 u1) [=] e_fv_u u1).
Proof. Admitted.

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

Lemma tt_fv_u_close_u_wrt_u_rec_mutual :
(forall u1 x1 n1,
  tt_fv_u (close_u_wrt_u_rec n1 x1 u1) [=] tt_fv_u u1).
Proof. Admitted.

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

Lemma tt_fv_u_close_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  tt_fv_u (close_u_wrt_t_rec n1 a1 u1) [=] remove a1 (tt_fv_u u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_close_u_wrt_t_rec :
forall u1 a1 n1,
  tt_fv_u (close_u_wrt_t_rec n1 a1 u1) [=] remove a1 (tt_fv_u u1).
Proof. Admitted.

Hint Resolve tt_fv_u_close_u_wrt_t_rec : lngen.
Hint Rewrite tt_fv_u_close_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

Lemma tt_fv_t_close_t_wrt_t :
forall t1 a1,
  tt_fv_t (close_t_wrt_t a1 t1) [=] remove a1 (tt_fv_t t1).
Proof. Admitted.

Hint Resolve tt_fv_t_close_t_wrt_t : lngen.
Hint Rewrite tt_fv_t_close_t_wrt_t using solve [auto] : lngen.

Lemma e_fv_u_close_u_wrt_u :
forall u1 x1,
  e_fv_u (close_u_wrt_u x1 u1) [=] remove x1 (e_fv_u u1).
Proof. Admitted.

Hint Resolve e_fv_u_close_u_wrt_u : lngen.
Hint Rewrite e_fv_u_close_u_wrt_u using solve [auto] : lngen.

Lemma e_fv_u_close_u_wrt_t :
forall u1 a1,
  e_fv_u (close_u_wrt_t a1 u1) [=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_close_u_wrt_t : lngen.
Hint Rewrite e_fv_u_close_u_wrt_t using solve [auto] : lngen.

Lemma tt_fv_u_close_u_wrt_u :
forall u1 x1,
  tt_fv_u (close_u_wrt_u x1 u1) [=] tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_close_u_wrt_u : lngen.
Hint Rewrite tt_fv_u_close_u_wrt_u using solve [auto] : lngen.

Lemma tt_fv_u_close_u_wrt_t :
forall u1 a1,
  tt_fv_u (close_u_wrt_t a1 u1) [=] remove a1 (tt_fv_u u1).
Proof. Admitted.

Hint Resolve tt_fv_u_close_u_wrt_t : lngen.
Hint Rewrite tt_fv_u_close_u_wrt_t using solve [auto] : lngen.

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

Lemma e_fv_u_open_u_wrt_u_rec_lower_mutual :
(forall u1 u2 n1,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_u_rec n1 u2 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_open_u_wrt_u_rec_lower :
forall u1 u2 n1,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_u_rec n1 u2 u1).
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_u_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_open_u_wrt_t_rec_lower_mutual :
(forall u1 t1 n1,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_t_rec n1 t1 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_open_u_wrt_t_rec_lower :
forall u1 t1 n1,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_t_rec n1 t1 u1).
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_u_rec_lower_mutual :
(forall u1 u2 n1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_u_rec n1 u2 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_u_rec_lower :
forall u1 u2 n1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_u_rec n1 u2 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_u_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_t_rec_lower_mutual :
(forall u1 t1 n1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_t_rec n1 t1 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_t_rec_lower :
forall u1 t1 n1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_t_rec n1 t1 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_t_rec_lower : lngen.

(* end hide *)

Lemma tt_fv_t_open_t_wrt_t_lower :
forall t1 t2,
  tt_fv_t t1 [<=] tt_fv_t (open_t_wrt_t t1 t2).
Proof. Admitted.

Hint Resolve tt_fv_t_open_t_wrt_t_lower : lngen.

Lemma e_fv_u_open_u_wrt_u_lower :
forall u1 u2,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_u_lower : lngen.

Lemma e_fv_u_open_u_wrt_t_lower :
forall u1 t1,
  e_fv_u u1 [<=] e_fv_u (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_t_lower : lngen.

Lemma tt_fv_u_open_u_wrt_u_lower :
forall u1 u2,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_u_lower : lngen.

Lemma tt_fv_u_open_u_wrt_t_lower :
forall u1 t1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_t u1 t1).
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_t_lower : lngen.

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

Lemma e_fv_u_open_u_wrt_u_rec_upper_mutual :
(forall u1 u2 n1,
  e_fv_u (open_u_wrt_u_rec n1 u2 u1) [<=] e_fv_u u2 `union` e_fv_u u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_open_u_wrt_u_rec_upper :
forall u1 u2 n1,
  e_fv_u (open_u_wrt_u_rec n1 u2 u1) [<=] e_fv_u u2 `union` e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_u_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_open_u_wrt_t_rec_upper_mutual :
(forall u1 t1 n1,
  e_fv_u (open_u_wrt_t_rec n1 t1 u1) [<=] e_fv_u u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_fv_u_open_u_wrt_t_rec_upper :
forall u1 t1 n1,
  e_fv_u (open_u_wrt_t_rec n1 t1 u1) [<=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_u_rec_upper_mutual :
(forall u1 u2 n1,
  tt_fv_u (open_u_wrt_u_rec n1 u2 u1) [<=] tt_fv_u u2 `union` tt_fv_u u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_u_rec_upper :
forall u1 u2 n1,
  tt_fv_u (open_u_wrt_u_rec n1 u2 u1) [<=] tt_fv_u u2 `union` tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_u_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_t_rec_upper_mutual :
(forall u1 t1 n1,
  tt_fv_u (open_u_wrt_t_rec n1 t1 u1) [<=] tt_fv_t t1 `union` tt_fv_u u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_t_rec_upper :
forall u1 t1 n1,
  tt_fv_u (open_u_wrt_t_rec n1 t1 u1) [<=] tt_fv_t t1 `union` tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_t_rec_upper : lngen.

(* end hide *)

Lemma tt_fv_t_open_t_wrt_t_upper :
forall t1 t2,
  tt_fv_t (open_t_wrt_t t1 t2) [<=] tt_fv_t t2 `union` tt_fv_t t1.
Proof. Admitted.

Hint Resolve tt_fv_t_open_t_wrt_t_upper : lngen.

Lemma e_fv_u_open_u_wrt_u_upper :
forall u1 u2,
  e_fv_u (open_u_wrt_u u1 u2) [<=] e_fv_u u2 `union` e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_u_upper : lngen.

Lemma e_fv_u_open_u_wrt_t_upper :
forall u1 t1,
  e_fv_u (open_u_wrt_t u1 t1) [<=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_open_u_wrt_t_upper : lngen.

Lemma tt_fv_u_open_u_wrt_u_upper :
forall u1 u2,
  tt_fv_u (open_u_wrt_u u1 u2) [<=] tt_fv_u u2 `union` tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_u_upper : lngen.

Lemma tt_fv_u_open_u_wrt_t_upper :
forall u1 t1,
  tt_fv_u (open_u_wrt_t u1 t1) [<=] tt_fv_t t1 `union` tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_open_u_wrt_t_upper : lngen.

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

Lemma e_fv_u_e_subst_u_fresh_mutual :
(forall u1 u2 x1,
  x1 `notin` e_fv_u u1 ->
  e_fv_u (e_subst_u u2 x1 u1) [=] e_fv_u u1).
Proof. Admitted.

(* end hide *)

Lemma e_fv_u_e_subst_u_fresh :
forall u1 u2 x1,
  x1 `notin` e_fv_u u1 ->
  e_fv_u (e_subst_u u2 x1 u1) [=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_e_subst_u_fresh : lngen.
Hint Rewrite e_fv_u_e_subst_u_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_u_e_subst_u_fresh_mutual :
(forall u1 t1 a1,
  e_fv_u (t_subst_u t1 a1 u1) [=] e_fv_u u1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_u_e_subst_u_fresh :
forall u1 t1 a1,
  e_fv_u (t_subst_u t1 a1 u1) [=] e_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_e_subst_u_fresh : lngen.
Hint Rewrite tt_fv_u_e_subst_u_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_u_t_subst_u_fresh_mutual :
(forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  tt_fv_u (t_subst_u t1 a1 u1) [=] tt_fv_u u1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_u_t_subst_u_fresh :
forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  tt_fv_u (t_subst_u t1 a1 u1) [=] tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_t_subst_u_fresh : lngen.
Hint Rewrite tt_fv_u_t_subst_u_fresh using solve [auto] : lngen.

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

Lemma e_fv_u_e_subst_u_lower_mutual :
(forall u1 u2 x1,
  remove x1 (e_fv_u u1) [<=] e_fv_u (e_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_u_e_subst_u_lower :
forall u1 u2 x1,
  remove x1 (e_fv_u u1) [<=] e_fv_u (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_fv_u_e_subst_u_lower : lngen.

(* begin hide *)

Lemma e_fv_u_t_subst_u_lower_mutual :
(forall u1 t1 a1,
  e_fv_u u1 [<=] e_fv_u (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_u_t_subst_u_lower :
forall u1 t1 a1,
  e_fv_u u1 [<=] e_fv_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve e_fv_u_t_subst_u_lower : lngen.

(* begin hide *)

Lemma tt_fv_u_e_subst_u_lower_mutual :
(forall u1 u2 x1,
  tt_fv_u u1 [<=] tt_fv_u (e_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_u_e_subst_u_lower :
forall u1 u2 x1,
  tt_fv_u u1 [<=] tt_fv_u (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_e_subst_u_lower : lngen.

(* begin hide *)

Lemma tt_fv_u_t_subst_u_lower_mutual :
(forall u1 t1 a1,
  remove a1 (tt_fv_u u1) [<=] tt_fv_u (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_u_t_subst_u_lower :
forall u1 t1 a1,
  remove a1 (tt_fv_u u1) [<=] tt_fv_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_t_subst_u_lower : lngen.

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

Lemma e_fv_u_e_subst_u_notin_mutual :
(forall u1 u2 x1 x2,
  x2 `notin` e_fv_u u1 ->
  x2 `notin` e_fv_u u2 ->
  x2 `notin` e_fv_u (e_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_u_e_subst_u_notin :
forall u1 u2 x1 x2,
  x2 `notin` e_fv_u u1 ->
  x2 `notin` e_fv_u u2 ->
  x2 `notin` e_fv_u (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_fv_u_e_subst_u_notin : lngen.

(* begin hide *)

Lemma e_fv_u_t_subst_u_notin_mutual :
(forall u1 t1 a1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_u_t_subst_u_notin :
forall u1 t1 a1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve e_fv_u_t_subst_u_notin : lngen.

(* begin hide *)

Lemma tt_fv_u_e_subst_u_notin_mutual :
(forall u1 u2 x1 a1,
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u (e_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_u_e_subst_u_notin :
forall u1 u2 x1 a1,
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_e_subst_u_notin : lngen.

(* begin hide *)

Lemma tt_fv_u_t_subst_u_notin_mutual :
(forall u1 t1 a1 a2,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_u (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_u_t_subst_u_notin :
forall u1 t1 a1 a2,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve tt_fv_u_t_subst_u_notin : lngen.

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

Lemma e_fv_u_e_subst_u_upper_mutual :
(forall u1 u2 x1,
  e_fv_u (e_subst_u u2 x1 u1) [<=] e_fv_u u2 `union` remove x1 (e_fv_u u1)).
Proof. Admitted.

(* end hide *)

Lemma e_fv_u_e_subst_u_upper :
forall u1 u2 x1,
  e_fv_u (e_subst_u u2 x1 u1) [<=] e_fv_u u2 `union` remove x1 (e_fv_u u1).
Proof. Admitted.

Hint Resolve e_fv_u_e_subst_u_upper : lngen.

(* begin hide *)

Lemma e_fv_u_t_subst_u_upper_mutual :
(forall u1 t1 a1,
  e_fv_u (t_subst_u t1 a1 u1) [<=] e_fv_u u1).
Proof. Admitted.

(* end hide *)

Lemma e_fv_u_t_subst_u_upper :
forall u1 t1 a1,
  e_fv_u (t_subst_u t1 a1 u1) [<=] e_fv_u u1.
Proof. Admitted.

Hint Resolve e_fv_u_t_subst_u_upper : lngen.

(* begin hide *)

Lemma tt_fv_u_e_subst_u_upper_mutual :
(forall u1 u2 x1,
  tt_fv_u (e_subst_u u2 x1 u1) [<=] tt_fv_u u2 `union` tt_fv_u u1).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_u_e_subst_u_upper :
forall u1 u2 x1,
  tt_fv_u (e_subst_u u2 x1 u1) [<=] tt_fv_u u2 `union` tt_fv_u u1.
Proof. Admitted.

Hint Resolve tt_fv_u_e_subst_u_upper : lngen.

(* begin hide *)

Lemma tt_fv_u_t_subst_u_upper_mutual :
(forall u1 t1 a1,
  tt_fv_u (t_subst_u t1 a1 u1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_u u1)).
Proof. Admitted.

(* end hide *)

Lemma tt_fv_u_t_subst_u_upper :
forall u1 t1 a1,
  tt_fv_u (t_subst_u t1 a1 u1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_u u1).
Proof. Admitted.

Hint Resolve tt_fv_u_t_subst_u_upper : lngen.


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

Lemma e_subst_u_close_u_wrt_u_rec_mutual :
(forall u2 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_u u1 x1 (close_u_wrt_u_rec n1 x2 u2) = close_u_wrt_u_rec n1 x2 (e_subst_u u1 x1 u2)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_u_close_u_wrt_u_rec :
forall u2 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_u u1 x1 (close_u_wrt_u_rec n1 x2 u2) = close_u_wrt_u_rec n1 x2 (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_u_rec : lngen.

(* begin hide *)

Lemma e_subst_u_close_u_wrt_t_rec_mutual :
(forall u2 u1 a1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  x1 `notin` tt_fv_u u1 ->
  e_subst_u u1 a1 (close_u_wrt_t_rec n1 x1 u2) = close_u_wrt_t_rec n1 x1 (e_subst_u u1 a1 u2)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_u_close_u_wrt_t_rec :
forall u2 u1 a1 x1 n1,
  degree_u_wrt_t n1 u1 ->
  x1 `notin` tt_fv_u u1 ->
  e_subst_u u1 a1 (close_u_wrt_t_rec n1 x1 u2) = close_u_wrt_t_rec n1 x1 (e_subst_u u1 a1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_t_rec : lngen.

(* begin hide *)

Lemma t_subst_u_close_u_wrt_u_rec_mutual :
(forall u1 t1 x1 a1 n1,
  t_subst_u t1 x1 (close_u_wrt_u_rec n1 a1 u1) = close_u_wrt_u_rec n1 a1 (t_subst_u t1 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_u_close_u_wrt_u_rec :
forall u1 t1 x1 a1 n1,
  t_subst_u t1 x1 (close_u_wrt_u_rec n1 a1 u1) = close_u_wrt_u_rec n1 a1 (t_subst_u t1 x1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_u_rec : lngen.

(* begin hide *)

Lemma t_subst_u_close_u_wrt_t_rec_mutual :
(forall u1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_u t1 a1 (close_u_wrt_t_rec n1 a2 u1) = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_u_close_u_wrt_t_rec :
forall u1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_u t1 a1 (close_u_wrt_t_rec n1 a2 u1) = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_t_rec : lngen.

Lemma t_subst_t_close_t_wrt_t :
forall t2 t1 a1 a2,
  lc_t t1 ->  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_t t1 a1 (close_t_wrt_t a2 t2) = close_t_wrt_t a2 (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_t_close_t_wrt_t : lngen.

Lemma e_subst_u_close_u_wrt_u :
forall u2 u1 x1 x2,
  lc_u u1 ->  x1 <> x2 ->
  x2 `notin` e_fv_u u1 ->
  e_subst_u u1 x1 (close_u_wrt_u x2 u2) = close_u_wrt_u x2 (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_u : lngen.

Lemma e_subst_u_close_u_wrt_t :
forall u2 u1 a1 x1,
  lc_u u1 ->  x1 `notin` tt_fv_u u1 ->
  e_subst_u u1 a1 (close_u_wrt_t x1 u2) = close_u_wrt_t x1 (e_subst_u u1 a1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_t : lngen.

Lemma t_subst_u_close_u_wrt_u :
forall u1 t1 x1 a1,
  lc_t t1 ->  t_subst_u t1 x1 (close_u_wrt_u a1 u1) = close_u_wrt_u a1 (t_subst_u t1 x1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_u : lngen.

Lemma t_subst_u_close_u_wrt_t :
forall u1 t1 a1 a2,
  lc_t t1 ->  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_u t1 a1 (close_u_wrt_t a2 u1) = close_u_wrt_t a2 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_t : lngen.

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

Lemma e_subst_u_degree_u_wrt_u_mutual :
(forall u1 u2 x1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 u2 ->
  degree_u_wrt_u n1 (e_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_u_degree_u_wrt_u :
forall u1 u2 x1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 u2 ->
  degree_u_wrt_u n1 (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_degree_u_wrt_u : lngen.

(* begin hide *)

Lemma e_subst_u_degree_u_wrt_t_mutual :
(forall u1 u2 x1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 u2 ->
  degree_u_wrt_t n1 (e_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_u_degree_u_wrt_t :
forall u1 u2 x1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t n1 u2 ->
  degree_u_wrt_t n1 (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_degree_u_wrt_t : lngen.

(* begin hide *)

Lemma t_subst_u_degree_u_wrt_u_mutual :
(forall u1 t1 a1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_u_degree_u_wrt_u :
forall u1 t1 a1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_degree_u_wrt_u : lngen.

(* begin hide *)

Lemma t_subst_u_degree_u_wrt_t_mutual :
(forall u1 t1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_u_degree_u_wrt_t :
forall u1 t1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_degree_u_wrt_t : lngen.

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

Lemma e_subst_u_fresh_eq_mutual :
(forall u2 u1 x1,
  x1 `notin` e_fv_u u2 ->
  e_subst_u u1 x1 u2 = u2).
Proof. Admitted.

(* end hide *)

Lemma e_subst_u_fresh_eq :
forall u2 u1 x1,
  x1 `notin` e_fv_u u2 ->
  e_subst_u u1 x1 u2 = u2.
Proof. Admitted.

Hint Resolve e_subst_u_fresh_eq : lngen.
Hint Rewrite e_subst_u_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_u_fresh_eq_mutual :
(forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  t_subst_u t1 a1 u1 = u1).
Proof. Admitted.

(* end hide *)

Lemma t_subst_u_fresh_eq :
forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  t_subst_u t1 a1 u1 = u1.
Proof. Admitted.

Hint Resolve t_subst_u_fresh_eq : lngen.
Hint Rewrite t_subst_u_fresh_eq using solve [auto] : lngen.

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

Lemma e_subst_u_fresh_same_mutual :
(forall u2 u1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (e_subst_u u1 x1 u2)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_u_fresh_same :
forall u2 u1 x1,
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_fresh_same : lngen.

(* begin hide *)

Lemma t_subst_u_fresh_same_mutual :
(forall u1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_u_fresh_same :
forall u1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_fresh_same : lngen.

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

Lemma e_subst_u_fresh_mutual :
(forall u2 u1 x1 x2,
  x1 `notin` e_fv_u u2 ->
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (e_subst_u u1 x2 u2)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_u_fresh :
forall u2 u1 x1 x2,
  x1 `notin` e_fv_u u2 ->
  x1 `notin` e_fv_u u1 ->
  x1 `notin` e_fv_u (e_subst_u u1 x2 u2).
Proof. Admitted.

Hint Resolve e_subst_u_fresh : lngen.

(* begin hide *)

Lemma t_subst_u_fresh_mutual :
(forall u1 t1 a1 a2,
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a2 u1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_u_fresh :
forall u1 t1 a1 a2,
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a2 u1).
Proof. Admitted.

Hint Resolve t_subst_u_fresh : lngen.

Lemma t_subst_t_lc_t :
forall t1 t2 a1,
  lc_t t1 ->
  lc_t t2 ->
  lc_t (t_subst_t t2 a1 t1).
Proof. Admitted.

Hint Resolve t_subst_t_lc_t : lngen.

Lemma e_subst_u_lc_u :
forall u1 u2 x1,
  lc_u u1 ->
  lc_u u2 ->
  lc_u (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_lc_u : lngen.

Lemma t_subst_u_lc_u :
forall u1 t1 a1,
  lc_u u1 ->
  lc_t t1 ->
  lc_u (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_lc_u : lngen.

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

Lemma e_subst_u_open_u_wrt_u_rec_mutual :
(forall u3 u1 u2 x1 n1,
  lc_u u1 ->
  e_subst_u u1 x1 (open_u_wrt_u_rec n1 u2 u3) = open_u_wrt_u_rec n1 (e_subst_u u1 x1 u2) (e_subst_u u1 x1 u3)).
Proof. Admitted.

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

Lemma e_subst_u_open_u_wrt_t_rec_mutual :
(forall u2 u1 t1 x1 n1,
  lc_u u1 ->
  e_subst_u u1 x1 (open_u_wrt_t_rec n1 t1 u2) = open_u_wrt_t_rec n1 t1 (e_subst_u u1 x1 u2)).
Proof. Admitted.

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

Lemma t_subst_u_open_u_wrt_u_rec_mutual :
(forall u2 t1 u1 a1 n1,
  t_subst_u t1 a1 (open_u_wrt_u_rec n1 u1 u2) = open_u_wrt_u_rec n1 (t_subst_u t1 a1 u1) (t_subst_u t1 a1 u2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_open_u_wrt_u_rec :
forall u2 t1 u1 a1 n1,
  t_subst_u t1 a1 (open_u_wrt_u_rec n1 u1 u2) = open_u_wrt_u_rec n1 (t_subst_u t1 a1 u1) (t_subst_u t1 a1 u2).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_open_u_wrt_t_rec_mutual :
(forall u1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_u t1 a1 (open_u_wrt_t_rec n1 t2 u1) = open_u_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_open_u_wrt_t_rec :
forall u1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_u t1 a1 (open_u_wrt_t_rec n1 t2 u1) = open_u_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_t_rec : lngen.

(* end hide *)

Lemma t_subst_t_open_t_wrt_t :
forall t3 t1 t2 a1,
  lc_t t1 ->
  t_subst_t t1 a1 (open_t_wrt_t t3 t2) = open_t_wrt_t (t_subst_t t1 a1 t3) (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_t_open_t_wrt_t : lngen.

Lemma e_subst_u_open_u_wrt_u :
forall u3 u1 u2 x1,
  lc_u u1 ->
  e_subst_u u1 x1 (open_u_wrt_u u3 u2) = open_u_wrt_u (e_subst_u u1 x1 u3) (e_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve e_subst_u_open_u_wrt_u : lngen.

Lemma e_subst_u_open_u_wrt_t :
forall u2 u1 t1 x1,
  lc_u u1 ->
  e_subst_u u1 x1 (open_u_wrt_t u2 t1) = open_u_wrt_t (e_subst_u u1 x1 u2) t1.
Proof. Admitted.

Hint Resolve e_subst_u_open_u_wrt_t : lngen.

Lemma t_subst_u_open_u_wrt_u :
forall u2 t1 u1 a1,
  t_subst_u t1 a1 (open_u_wrt_u u2 u1) = open_u_wrt_u (t_subst_u t1 a1 u2) (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_u : lngen.

Lemma t_subst_u_open_u_wrt_t :
forall u1 t1 t2 a1,
  lc_t t1 ->
  t_subst_u t1 a1 (open_u_wrt_t u1 t2) = open_u_wrt_t (t_subst_u t1 a1 u1) (t_subst_t t1 a1 t2).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_t : lngen.

Lemma t_subst_t_open_t_wrt_t_var :
forall t2 t1 a1 a2,
  a1 <> a2 ->
  lc_t t1 ->
  open_t_wrt_t (t_subst_t t1 a1 t2) (t_var_f a2) = t_subst_t t1 a1 (open_t_wrt_t t2 (t_var_f a2)).
Proof. Admitted.

Hint Resolve t_subst_t_open_t_wrt_t_var : lngen.

Lemma e_subst_u_open_u_wrt_u_var :
forall u2 u1 x1 x2,
  x1 <> x2 ->
  lc_u u1 ->
  open_u_wrt_u (e_subst_u u1 x1 u2) (u_var_f x2) = e_subst_u u1 x1 (open_u_wrt_u u2 (u_var_f x2)).
Proof. Admitted.

Hint Resolve e_subst_u_open_u_wrt_u_var : lngen.

Lemma e_subst_u_open_u_wrt_t_var :
forall u2 u1 x1 a1,
  lc_u u1 ->
  open_u_wrt_t (e_subst_u u1 x1 u2) (t_var_f a1) = e_subst_u u1 x1 (open_u_wrt_t u2 (t_var_f a1)).
Proof. Admitted.

Hint Resolve e_subst_u_open_u_wrt_t_var : lngen.

Lemma t_subst_u_open_u_wrt_u_var :
forall u1 t1 a1 x1,
  open_u_wrt_u (t_subst_u t1 a1 u1) (u_var_f x1) = t_subst_u t1 a1 (open_u_wrt_u u1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_u_var : lngen.

Lemma t_subst_u_open_u_wrt_t_var :
forall u1 t1 a1 a2,
  a1 <> a2 ->
  lc_t t1 ->
  open_u_wrt_t (t_subst_u t1 a1 u1) (t_var_f a2) = t_subst_u t1 a1 (open_u_wrt_t u1 (t_var_f a2)).
Proof. Admitted.

Hint Resolve t_subst_u_open_u_wrt_t_var : lngen.

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

Lemma e_subst_u_spec_rec_mutual :
(forall u1 u2 x1 n1,
  e_subst_u u2 x1 u1 = open_u_wrt_u_rec n1 u2 (close_u_wrt_u_rec n1 x1 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma e_subst_u_spec_rec :
forall u1 u2 x1 n1,
  e_subst_u u2 x1 u1 = open_u_wrt_u_rec n1 u2 (close_u_wrt_u_rec n1 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_spec_rec_mutual :
(forall u1 t1 a1 n1,
  t_subst_u t1 a1 u1 = open_u_wrt_t_rec n1 t1 (close_u_wrt_t_rec n1 a1 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_spec_rec :
forall u1 t1 a1 n1,
  t_subst_u t1 a1 u1 = open_u_wrt_t_rec n1 t1 (close_u_wrt_t_rec n1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_spec_rec : lngen.

(* end hide *)

Lemma t_subst_t_spec :
forall t1 t2 a1,
  t_subst_t t2 a1 t1 = open_t_wrt_t (close_t_wrt_t a1 t1) t2.
Proof. Admitted.

Hint Resolve t_subst_t_spec : lngen.

Lemma e_subst_u_spec :
forall u1 u2 x1,
  e_subst_u u2 x1 u1 = open_u_wrt_u (close_u_wrt_u x1 u1) u2.
Proof. Admitted.

Hint Resolve e_subst_u_spec : lngen.

Lemma t_subst_u_spec :
forall u1 t1 a1,
  t_subst_u t1 a1 u1 = open_u_wrt_t (close_u_wrt_t a1 u1) t1.
Proof. Admitted.

Hint Resolve t_subst_u_spec : lngen.

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

Lemma e_subst_u_e_subst_u_mutual :
(forall u1 u2 u3 x2 x1,
  x2 `notin` e_fv_u u2 ->
  x2 <> x1 ->
  e_subst_u u2 x1 (e_subst_u u3 x2 u1) = e_subst_u (e_subst_u u2 x1 u3) x2 (e_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_u_e_subst_u :
forall u1 u2 u3 x2 x1,
  x2 `notin` e_fv_u u2 ->
  x2 <> x1 ->
  e_subst_u u2 x1 (e_subst_u u3 x2 u1) = e_subst_u (e_subst_u u2 x1 u3) x2 (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_e_subst_u : lngen.

(* begin hide *)

Lemma e_subst_u_t_subst_u_mutual :
(forall u1 u2 t1 a1 x1,
  a1 `notin` tt_fv_u u2 ->
  e_subst_u u2 x1 (t_subst_u t1 a1 u1) = t_subst_u t1 a1 (e_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_u_t_subst_u :
forall u1 u2 t1 a1 x1,
  a1 `notin` tt_fv_u u2 ->
  e_subst_u u2 x1 (t_subst_u t1 a1 u1) = t_subst_u t1 a1 (e_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve e_subst_u_t_subst_u : lngen.

(* begin hide *)

Lemma t_subst_u_e_subst_u_mutual :
(forall u1 t1 u2 x1 a1,
  t_subst_u t1 a1 (e_subst_u u2 x1 u1) = e_subst_u (t_subst_u t1 a1 u2) x1 (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_u_e_subst_u :
forall u1 t1 u2 x1 a1,
  t_subst_u t1 a1 (e_subst_u u2 x1 u1) = e_subst_u (t_subst_u t1 a1 u2) x1 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_e_subst_u : lngen.

(* begin hide *)

Lemma t_subst_u_t_subst_u_mutual :
(forall u1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_u t1 a1 (t_subst_u t2 a2 u1) = t_subst_u (t_subst_t t1 a1 t2) a2 (t_subst_u t1 a1 u1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_u_t_subst_u :
forall u1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_u t1 a1 (t_subst_u t2 a2 u1) = t_subst_u (t_subst_t t1 a1 t2) a2 (t_subst_u t1 a1 u1).
Proof. Admitted.

Hint Resolve t_subst_u_t_subst_u : lngen.

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

Lemma e_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec_mutual :
(forall u2 u1 x1 x2 n1,
  x2 `notin` e_fv_u u2 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  e_subst_u u1 x1 u2 = close_u_wrt_u_rec n1 x2 (e_subst_u u1 x1 (open_u_wrt_u_rec n1 (u_var_f x2) u2))).
Proof. Admitted.

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

Lemma e_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec_mutual :
(forall u2 u1 x1 a1 n1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  degree_u_wrt_t n1 u1 ->
  e_subst_u u1 x1 u2 = close_u_wrt_t_rec n1 a1 (e_subst_u u1 x1 (open_u_wrt_t_rec n1 (t_var_f a1) u2))).
Proof. Admitted.

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

Lemma t_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec_mutual :
(forall u1 t1 a1 x1 n1,
  x1 `notin` e_fv_u u1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_u_rec n1 x1 (t_subst_u t1 a1 (open_u_wrt_u_rec n1 (u_var_f x1) u1))).
Proof. Admitted.

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

Lemma t_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec_mutual :
(forall u1 t1 a1 a2 n1,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a2) u1))).
Proof. Admitted.

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

Lemma t_subst_t_close_t_wrt_t_open_t_wrt_t :
forall t2 t1 a1 a2,
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  lc_t t1 ->
  t_subst_t t1 a1 t2 = close_t_wrt_t a2 (t_subst_t t1 a1 (open_t_wrt_t t2 (t_var_f a2))).
Proof. Admitted.

Hint Resolve t_subst_t_close_t_wrt_t_open_t_wrt_t : lngen.

Lemma e_subst_u_close_u_wrt_u_open_u_wrt_u :
forall u2 u1 x1 x2,
  x2 `notin` e_fv_u u2 ->
  x2 `notin` e_fv_u u1 ->
  x2 <> x1 ->
  lc_u u1 ->
  e_subst_u u1 x1 u2 = close_u_wrt_u x2 (e_subst_u u1 x1 (open_u_wrt_u u2 (u_var_f x2))).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_u_open_u_wrt_u : lngen.

Lemma e_subst_u_close_u_wrt_t_open_u_wrt_t :
forall u2 u1 x1 a1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  lc_u u1 ->
  e_subst_u u1 x1 u2 = close_u_wrt_t a1 (e_subst_u u1 x1 (open_u_wrt_t u2 (t_var_f a1))).
Proof. Admitted.

Hint Resolve e_subst_u_close_u_wrt_t_open_u_wrt_t : lngen.

Lemma t_subst_u_close_u_wrt_u_open_u_wrt_u :
forall u1 t1 a1 x1,
  x1 `notin` e_fv_u u1 ->
  lc_t t1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_u x1 (t_subst_u t1 a1 (open_u_wrt_u u1 (u_var_f x1))).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_u_open_u_wrt_u : lngen.

Lemma t_subst_u_close_u_wrt_t_open_u_wrt_t :
forall u1 t1 a1 a2,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  lc_t t1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_t a2 (t_subst_u t1 a1 (open_u_wrt_t u1 (t_var_f a2))).
Proof. Admitted.

Hint Resolve t_subst_u_close_u_wrt_t_open_u_wrt_t : lngen.

Lemma t_subst_t_t_all :
forall a2 t2 t1 a1,
  lc_t t1 ->
  a2 `notin` tt_fv_t t1 `union` tt_fv_t t2 `union` singleton a1 ->
  t_subst_t t1 a1 (t_all t2) = t_all (close_t_wrt_t a2 (t_subst_t t1 a1 (open_t_wrt_t t2 (t_var_f a2)))).
Proof. Admitted.

Hint Resolve t_subst_t_t_all : lngen.

Lemma e_subst_u_u_fix :
forall x2 t1 t2 e1 u1 x1,
  lc_u u1 ->
  x2 `notin` e_fv_u u1 `union` e_fv_u e1 `union` singleton x1 ->
  e_subst_u u1 x1 (u_fix t1 t2 e1) = u_fix (t1) (t2) (close_u_wrt_u x2 (e_subst_u u1 x1 (open_u_wrt_u e1 (u_var_f x2)))).
Proof. Admitted.

Hint Resolve e_subst_u_u_fix : lngen.

Lemma e_subst_u_u_lam :
forall x2 t1 e1 u1 x1,
  lc_u u1 ->
  x2 `notin` e_fv_u u1 `union` e_fv_u e1 `union` singleton x1 ->
  e_subst_u u1 x1 (u_lam t1 e1) = u_lam (t1) (close_u_wrt_u x2 (e_subst_u u1 x1 (open_u_wrt_u e1 (u_var_f x2)))).
Proof. Admitted.

Hint Resolve e_subst_u_u_lam : lngen.

Lemma e_subst_u_u_tlam :
forall a1 e1 u1 x1,
  lc_u u1 ->
  a1 `notin` tt_fv_u u1 `union` tt_fv_u e1 ->
  e_subst_u u1 x1 (u_tlam e1) = u_tlam (close_u_wrt_t a1 (e_subst_u u1 x1 (open_u_wrt_t e1 (t_var_f a1)))).
Proof. Admitted.

Hint Resolve e_subst_u_u_tlam : lngen.

Lemma t_subst_u_u_fix :
forall x1 t2 t3 e1 t1 a1,
  lc_t t1 ->
  x1 `notin` e_fv_u e1 ->
  t_subst_u t1 a1 (u_fix t2 t3 e1) = u_fix (t_subst_t t1 a1 t2) (t_subst_t t1 a1 t3) (close_u_wrt_u x1 (t_subst_u t1 a1 (open_u_wrt_u e1 (u_var_f x1)))).
Proof. Admitted.

Hint Resolve t_subst_u_u_fix : lngen.

Lemma t_subst_u_u_lam :
forall x1 t2 e1 t1 a1,
  lc_t t1 ->
  x1 `notin` e_fv_u e1 ->
  t_subst_u t1 a1 (u_lam t2 e1) = u_lam (t_subst_t t1 a1 t2) (close_u_wrt_u x1 (t_subst_u t1 a1 (open_u_wrt_u e1 (u_var_f x1)))).
Proof. Admitted.

Hint Resolve t_subst_u_u_lam : lngen.

Lemma t_subst_u_u_tlam :
forall a2 e1 t1 a1,
  lc_t t1 ->
  a2 `notin` tt_fv_t t1 `union` tt_fv_u e1 `union` singleton a1 ->
  t_subst_u t1 a1 (u_tlam e1) = u_tlam (close_u_wrt_t a2 (t_subst_u t1 a1 (open_u_wrt_t e1 (t_var_f a2)))).
Proof. Admitted.

Hint Resolve t_subst_u_u_tlam : lngen.

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

Lemma e_subst_u_intro_rec_mutual :
(forall u1 x1 u2 n1,
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u_rec n1 u2 u1 = e_subst_u u2 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1)).
Proof. Admitted.

(* end hide *)

Lemma e_subst_u_intro_rec :
forall u1 x1 u2 n1,
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u_rec n1 u2 u1 = e_subst_u u2 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1).
Proof. Admitted.

Hint Resolve e_subst_u_intro_rec : lngen.
Hint Rewrite e_subst_u_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_u_intro_rec_mutual :
(forall u1 a1 t1 n1,
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 t1 u1 = t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1)).
Proof. Admitted.

(* end hide *)

Lemma t_subst_u_intro_rec :
forall u1 a1 t1 n1,
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 t1 u1 = t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1).
Proof. Admitted.

Hint Resolve t_subst_u_intro_rec : lngen.
Hint Rewrite t_subst_u_intro_rec using solve [auto] : lngen.

Lemma t_subst_t_intro :
forall a1 t1 t2,
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t t1 t2 = t_subst_t t2 a1 (open_t_wrt_t t1 (t_var_f a1)).
Proof. Admitted.

Hint Resolve t_subst_t_intro : lngen.

Lemma e_subst_u_intro :
forall x1 u1 u2,
  x1 `notin` e_fv_u u1 ->
  open_u_wrt_u u1 u2 = e_subst_u u2 x1 (open_u_wrt_u u1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve e_subst_u_intro : lngen.

Lemma t_subst_u_intro :
forall a1 u1 t1,
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t u1 t1 = t_subst_u t1 a1 (open_u_wrt_t u1 (t_var_f a1)).
Proof. Admitted.

Hint Resolve t_subst_u_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
