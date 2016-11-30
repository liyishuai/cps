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
  fun H1 H2 H3 H4 H5 =>
  t_ind' H1 H2 H3 H4 H5.

Scheme t_rec' := Induction for t Sort Set.

Definition t_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  t_rec' H1 H2 H3 H4 H5.

Scheme p_ind' := Induction for p Sort Prop.

Definition p_mutind :=
  fun H1 H2 H3 =>
  p_ind' H1 H2 H3.

Scheme p_rec' := Induction for p Sort Set.

Definition p_mutrec :=
  fun H1 H2 H3 =>
  p_rec' H1 H2 H3.

Scheme e_ind' := Induction for e Sort Prop
  with u_ind' := Induction for u Sort Prop.

Definition e_u_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (conj (e_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)).

Scheme e_rec' := Induction for e Sort Set
  with u_rec' := Induction for u Sort Set.

Definition e_u_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (pair (e_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (u_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)).


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_e_wrt_u_rec (n1 : nat) (x1 : x) (e1 : e) {struct e1} : e :=
  match e1 with
    | e_ann u1 t1 => e_ann (close_u_wrt_u_rec n1 x1 u1) t1
  end

with close_u_wrt_u_rec (n1 : nat) (x1 : x) (u1 : u) {struct u1} : u :=
  match u1 with
    | u_var_f x2 => if (x1 == x2) then (u_var_b n1) else (u_var_f x2)
    | u_var_b n2 => if (lt_ge_dec n2 n1) then (u_var_b n2) else (u_var_b (S n2))
    | u_int i1 => u_int i1
    | u_lam t1 e1 => u_lam t1 (close_e_wrt_u_rec (S n1) x1 e1)
    | u_app e1 e2 => u_app (close_e_wrt_u_rec n1 x1 e1) (close_e_wrt_u_rec n1 x1 e2)
    | u_pair e1 e2 => u_pair (close_e_wrt_u_rec n1 x1 e1) (close_e_wrt_u_rec n1 x1 e2)
    | u_prl e1 => u_prl (close_e_wrt_u_rec n1 x1 e1)
    | u_prr e1 => u_prr (close_e_wrt_u_rec n1 x1 e1)
    | u_prim e1 p1 e2 => u_prim (close_e_wrt_u_rec n1 x1 e1) p1 (close_e_wrt_u_rec n1 x1 e2)
    | u_if0 e1 e2 e3 => u_if0 (close_e_wrt_u_rec n1 x1 e1) (close_e_wrt_u_rec n1 x1 e2) (close_e_wrt_u_rec n1 x1 e3)
    | u_let e1 u2 => u_let (close_e_wrt_u_rec n1 x1 e1) (close_u_wrt_u_rec (S n1) x1 u2)
    | u_halt e1 => u_halt (close_e_wrt_u_rec n1 x1 e1)
  end.

Definition close_e_wrt_u x1 e1 := close_e_wrt_u_rec 0 x1 e1.

Definition close_u_wrt_u x1 u1 := close_u_wrt_u_rec 0 x1 u1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_t (t1 : t) {struct t1} : nat :=
  match t1 with
    | t_int => 1
    | t_void => 1
    | t_arr t2 t3 => 1 + (size_t t2) + (size_t t3)
    | t_prod t2 t3 => 1 + (size_t t2) + (size_t t3)
  end.

Fixpoint size_p (p1 : p) {struct p1} : nat :=
  match p1 with
    | p_plus => 1
    | p_minus => 1
  end.

Fixpoint size_e (e1 : e) {struct e1} : nat :=
  match e1 with
    | e_ann u1 t1 => 1 + (size_u u1) + (size_t t1)
  end

with size_u (u1 : u) {struct u1} : nat :=
  match u1 with
    | u_var_f x1 => 1
    | u_var_b n1 => 1
    | u_int i1 => 1
    | u_lam t1 e1 => 1 + (size_t t1) + (size_e e1)
    | u_app e1 e2 => 1 + (size_e e1) + (size_e e2)
    | u_pair e1 e2 => 1 + (size_e e1) + (size_e e2)
    | u_prl e1 => 1 + (size_e e1)
    | u_prr e1 => 1 + (size_e e1)
    | u_prim e1 p1 e2 => 1 + (size_e e1) + (size_p p1) + (size_e e2)
    | u_if0 e1 e2 e3 => 1 + (size_e e1) + (size_e e2) + (size_e e3)
    | u_let e1 u2 => 1 + (size_e e1) + (size_u u2)
    | u_halt e1 => 1 + (size_e e1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_e_wrt_u : nat -> e -> Prop :=
  | degree_wrt_u_e_ann : forall n1 u1 t1,
    degree_u_wrt_u n1 u1 ->
    degree_e_wrt_u n1 (e_ann u1 t1)

with degree_u_wrt_u : nat -> u -> Prop :=
  | degree_wrt_u_u_var_f : forall n1 x1,
    degree_u_wrt_u n1 (u_var_f x1)
  | degree_wrt_u_u_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_u_wrt_u n1 (u_var_b n2)
  | degree_wrt_u_u_int : forall n1 i1,
    degree_u_wrt_u n1 (u_int i1)
  | degree_wrt_u_u_lam : forall n1 t1 e1,
    degree_e_wrt_u (S n1) e1 ->
    degree_u_wrt_u n1 (u_lam t1 e1)
  | degree_wrt_u_u_app : forall n1 e1 e2,
    degree_e_wrt_u n1 e1 ->
    degree_e_wrt_u n1 e2 ->
    degree_u_wrt_u n1 (u_app e1 e2)
  | degree_wrt_u_u_pair : forall n1 e1 e2,
    degree_e_wrt_u n1 e1 ->
    degree_e_wrt_u n1 e2 ->
    degree_u_wrt_u n1 (u_pair e1 e2)
  | degree_wrt_u_u_prl : forall n1 e1,
    degree_e_wrt_u n1 e1 ->
    degree_u_wrt_u n1 (u_prl e1)
  | degree_wrt_u_u_prr : forall n1 e1,
    degree_e_wrt_u n1 e1 ->
    degree_u_wrt_u n1 (u_prr e1)
  | degree_wrt_u_u_prim : forall n1 e1 p1 e2,
    degree_e_wrt_u n1 e1 ->
    degree_e_wrt_u n1 e2 ->
    degree_u_wrt_u n1 (u_prim e1 p1 e2)
  | degree_wrt_u_u_if0 : forall n1 e1 e2 e3,
    degree_e_wrt_u n1 e1 ->
    degree_e_wrt_u n1 e2 ->
    degree_e_wrt_u n1 e3 ->
    degree_u_wrt_u n1 (u_if0 e1 e2 e3)
  | degree_wrt_u_u_let : forall n1 e1 u1,
    degree_e_wrt_u n1 e1 ->
    degree_u_wrt_u (S n1) u1 ->
    degree_u_wrt_u n1 (u_let e1 u1)
  | degree_wrt_u_u_halt : forall n1 e1,
    degree_e_wrt_u n1 e1 ->
    degree_u_wrt_u n1 (u_halt e1).

Scheme degree_e_wrt_u_ind' := Induction for degree_e_wrt_u Sort Prop
  with degree_u_wrt_u_ind' := Induction for degree_u_wrt_u Sort Prop.

Definition degree_e_wrt_u_degree_u_wrt_u_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (conj (degree_e_wrt_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (degree_u_wrt_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)).

Hint Constructors degree_e_wrt_u : core lngen.

Hint Constructors degree_u_wrt_u : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_e : e -> Set :=
  | lc_set_e_ann : forall u1 t1,
    lc_set_u u1 ->
    lc_set_e (e_ann u1 t1)

with lc_set_u : u -> Set :=
  | lc_set_u_var_f : forall x1,
    lc_set_u (u_var_f x1)
  | lc_set_u_int : forall i1,
    lc_set_u (u_int i1)
  | lc_set_u_lam : forall t1 e1,
    (forall x1 : x, lc_set_e (open_e_wrt_u e1 (u_var_f x1))) ->
    lc_set_u (u_lam t1 e1)
  | lc_set_u_app : forall e1 e2,
    lc_set_e e1 ->
    lc_set_e e2 ->
    lc_set_u (u_app e1 e2)
  | lc_set_u_pair : forall e1 e2,
    lc_set_e e1 ->
    lc_set_e e2 ->
    lc_set_u (u_pair e1 e2)
  | lc_set_u_prl : forall e1,
    lc_set_e e1 ->
    lc_set_u (u_prl e1)
  | lc_set_u_prr : forall e1,
    lc_set_e e1 ->
    lc_set_u (u_prr e1)
  | lc_set_u_prim : forall e1 p1 e2,
    lc_set_e e1 ->
    lc_set_e e2 ->
    lc_set_u (u_prim e1 p1 e2)
  | lc_set_u_if0 : forall e1 e2 e3,
    lc_set_e e1 ->
    lc_set_e e2 ->
    lc_set_e e3 ->
    lc_set_u (u_if0 e1 e2 e3)
  | lc_set_u_let : forall e1 u1,
    lc_set_e e1 ->
    (forall x1 : x, lc_set_u (open_u_wrt_u u1 (u_var_f x1))) ->
    lc_set_u (u_let e1 u1)
  | lc_set_u_halt : forall e1,
    lc_set_e e1 ->
    lc_set_u (u_halt e1).

Scheme lc_e_ind' := Induction for lc_e Sort Prop
  with lc_u_ind' := Induction for lc_u Sort Prop.

Definition lc_e_lc_u_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  (conj (lc_e_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  (lc_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)).

Scheme lc_set_e_ind' := Induction for lc_set_e Sort Prop
  with lc_set_u_ind' := Induction for lc_set_u Sort Prop.

Definition lc_set_e_lc_set_u_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  (conj (lc_set_e_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  (lc_set_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)).

Scheme lc_set_e_rec' := Induction for lc_set_e Sort Set
  with lc_set_u_rec' := Induction for lc_set_u Sort Set.

Definition lc_set_e_lc_set_u_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  (pair (lc_set_e_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  (lc_set_u_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)).

Hint Constructors lc_e : core lngen.

Hint Constructors lc_u : core lngen.

Hint Constructors lc_set_e : core lngen.

Hint Constructors lc_set_u : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_e_wrt_u e1 := forall x1, lc_e (open_e_wrt_u e1 (u_var_f x1)).

Definition body_u_wrt_u u1 := forall x1, lc_u (open_u_wrt_u u1 (u_var_f x1)).

Hint Unfold body_e_wrt_u.

Hint Unfold body_u_wrt_u.


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

Lemma size_e_min_size_u_min_mutual :
(forall e1, 1 <= size_e e1) /\
(forall u1, 1 <= size_u u1).
Proof. Admitted.

(* end hide *)

Lemma size_e_min :
forall e1, 1 <= size_e e1.
Proof. Admitted.

Hint Resolve size_e_min : lngen.

Lemma size_u_min :
forall u1, 1 <= size_u u1.
Proof. Admitted.

Hint Resolve size_u_min : lngen.

(* begin hide *)

Lemma size_e_close_e_wrt_u_rec_size_u_close_u_wrt_u_rec_mutual :
(forall e1 x1 n1,
  size_e (close_e_wrt_u_rec n1 x1 e1) = size_e e1) /\
(forall u1 x1 n1,
  size_u (close_u_wrt_u_rec n1 x1 u1) = size_u u1).
Proof. Admitted.

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

(* begin hide *)

Lemma size_e_open_e_wrt_u_rec_size_u_open_u_wrt_u_rec_mutual :
(forall e1 u1 n1,
  size_e e1 <= size_e (open_e_wrt_u_rec n1 u1 e1)) /\
(forall u1 u2 n1,
  size_u u1 <= size_u (open_u_wrt_u_rec n1 u2 u1)).
Proof. Admitted.

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

(* begin hide *)

Lemma size_e_open_e_wrt_u_rec_var_size_u_open_u_wrt_u_rec_var_mutual :
(forall e1 x1 n1,
  size_e (open_e_wrt_u_rec n1 (u_var_f x1) e1) = size_e e1) /\
(forall u1 x1 n1,
  size_u (open_u_wrt_u_rec n1 (u_var_f x1) u1) = size_u u1).
Proof. Admitted.

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


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_e_wrt_u_S_degree_u_wrt_u_S_mutual :
(forall n1 e1,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u (S n1) e1) /\
(forall n1 u1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u (S n1) u1).
Proof. Admitted.

(* end hide *)

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

(* begin hide *)

Lemma degree_e_wrt_u_close_e_wrt_u_rec_degree_u_wrt_u_close_u_wrt_u_rec_mutual :
(forall e1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_e_wrt_u (S n1) (close_e_wrt_u_rec n1 x1 e1)) /\
(forall u1 x1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u (S n1) (close_u_wrt_u_rec n1 x1 u1)).
Proof. Admitted.

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

(* begin hide *)

Lemma degree_e_wrt_u_close_e_wrt_u_rec_inv_degree_u_wrt_u_close_u_wrt_u_rec_inv_mutual :
(forall e1 x1 n1,
  degree_e_wrt_u (S n1) (close_e_wrt_u_rec n1 x1 e1) ->
  degree_e_wrt_u n1 e1) /\
(forall u1 x1 n1,
  degree_u_wrt_u (S n1) (close_u_wrt_u_rec n1 x1 u1) ->
  degree_u_wrt_u n1 u1).
Proof. Admitted.

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

(* begin hide *)

Lemma degree_e_wrt_u_open_e_wrt_u_rec_degree_u_wrt_u_open_u_wrt_u_rec_mutual :
(forall e1 u1 n1,
  degree_e_wrt_u (S n1) e1 ->
  degree_u_wrt_u n1 u1 ->
  degree_e_wrt_u n1 (open_e_wrt_u_rec n1 u1 e1)) /\
(forall u1 u2 n1,
  degree_u_wrt_u (S n1) u1 ->
  degree_u_wrt_u n1 u2 ->
  degree_u_wrt_u n1 (open_u_wrt_u_rec n1 u2 u1)).
Proof. Admitted.

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

(* begin hide *)

Lemma degree_e_wrt_u_open_e_wrt_u_rec_inv_degree_u_wrt_u_open_u_wrt_u_rec_inv_mutual :
(forall e1 u1 n1,
  degree_e_wrt_u n1 (open_e_wrt_u_rec n1 u1 e1) ->
  degree_e_wrt_u (S n1) e1) /\
(forall u1 u2 n1,
  degree_u_wrt_u n1 (open_u_wrt_u_rec n1 u2 u1) ->
  degree_u_wrt_u (S n1) u1).
Proof. Admitted.

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


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_e_wrt_u_rec_inj_close_u_wrt_u_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_e_wrt_u_rec n1 x1 e1 = close_e_wrt_u_rec n1 x1 e2 ->
  e1 = e2) /\
(forall u1 u2 x1 n1,
  close_u_wrt_u_rec n1 x1 u1 = close_u_wrt_u_rec n1 x1 u2 ->
  u1 = u2).
Proof. Admitted.

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

(* begin hide *)

Lemma close_e_wrt_u_rec_open_e_wrt_u_rec_close_u_wrt_u_rec_open_u_wrt_u_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` u_fv_e e1 ->
  close_e_wrt_u_rec n1 x1 (open_e_wrt_u_rec n1 (u_var_f x1) e1) = e1) /\
(forall u1 x1 n1,
  x1 `notin` u_fv_u u1 ->
  close_u_wrt_u_rec n1 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1) = u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_u_rec_open_e_wrt_u_rec :
forall e1 x1 n1,
  x1 `notin` u_fv_e e1 ->
  close_e_wrt_u_rec n1 x1 (open_e_wrt_u_rec n1 (u_var_f x1) e1) = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_u_rec_open_e_wrt_u_rec : lngen.
Hint Rewrite close_e_wrt_u_rec_open_e_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_u_rec_open_u_wrt_u_rec :
forall u1 x1 n1,
  x1 `notin` u_fv_u u1 ->
  close_u_wrt_u_rec n1 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1) = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_u_rec_open_u_wrt_u_rec : lngen.
Hint Rewrite close_u_wrt_u_rec_open_u_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_e_wrt_u_open_e_wrt_u :
forall e1 x1,
  x1 `notin` u_fv_e e1 ->
  close_e_wrt_u x1 (open_e_wrt_u e1 (u_var_f x1)) = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_u_open_e_wrt_u : lngen.
Hint Rewrite close_e_wrt_u_open_e_wrt_u using solve [auto] : lngen.

Lemma close_u_wrt_u_open_u_wrt_u :
forall u1 x1,
  x1 `notin` u_fv_u u1 ->
  close_u_wrt_u x1 (open_u_wrt_u u1 (u_var_f x1)) = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_u_open_u_wrt_u : lngen.
Hint Rewrite close_u_wrt_u_open_u_wrt_u using solve [auto] : lngen.

(* begin hide *)

Lemma open_e_wrt_u_rec_close_e_wrt_u_rec_open_u_wrt_u_rec_close_u_wrt_u_rec_mutual :
(forall e1 x1 n1,
  open_e_wrt_u_rec n1 (u_var_f x1) (close_e_wrt_u_rec n1 x1 e1) = e1) /\
(forall u1 x1 n1,
  open_u_wrt_u_rec n1 (u_var_f x1) (close_u_wrt_u_rec n1 x1 u1) = u1).
Proof. Admitted.

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

(* begin hide *)

Lemma open_e_wrt_u_rec_inj_open_u_wrt_u_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` u_fv_e e2 ->
  x1 `notin` u_fv_e e1 ->
  open_e_wrt_u_rec n1 (u_var_f x1) e2 = open_e_wrt_u_rec n1 (u_var_f x1) e1 ->
  e2 = e1) /\
(forall u2 u1 x1 n1,
  x1 `notin` u_fv_u u2 ->
  x1 `notin` u_fv_u u1 ->
  open_u_wrt_u_rec n1 (u_var_f x1) u2 = open_u_wrt_u_rec n1 (u_var_f x1) u1 ->
  u2 = u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_u_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` u_fv_e e2 ->
  x1 `notin` u_fv_e e1 ->
  open_e_wrt_u_rec n1 (u_var_f x1) e2 = open_e_wrt_u_rec n1 (u_var_f x1) e1 ->
  e2 = e1.
Proof. Admitted.

Hint Immediate open_e_wrt_u_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_u_rec_inj :
forall u2 u1 x1 n1,
  x1 `notin` u_fv_u u2 ->
  x1 `notin` u_fv_u u1 ->
  open_u_wrt_u_rec n1 (u_var_f x1) u2 = open_u_wrt_u_rec n1 (u_var_f x1) u1 ->
  u2 = u1.
Proof. Admitted.

Hint Immediate open_u_wrt_u_rec_inj : lngen.

(* end hide *)

Lemma open_e_wrt_u_inj :
forall e2 e1 x1,
  x1 `notin` u_fv_e e2 ->
  x1 `notin` u_fv_e e1 ->
  open_e_wrt_u e2 (u_var_f x1) = open_e_wrt_u e1 (u_var_f x1) ->
  e2 = e1.
Proof. Admitted.

Hint Immediate open_e_wrt_u_inj : lngen.

Lemma open_u_wrt_u_inj :
forall u2 u1 x1,
  x1 `notin` u_fv_u u2 ->
  x1 `notin` u_fv_u u1 ->
  open_u_wrt_u u2 (u_var_f x1) = open_u_wrt_u u1 (u_var_f x1) ->
  u2 = u1.
Proof. Admitted.

Hint Immediate open_u_wrt_u_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_e_wrt_u_of_lc_e_degree_u_wrt_u_of_lc_u_mutual :
(forall e1,
  lc_e e1 ->
  degree_e_wrt_u 0 e1) /\
(forall u1,
  lc_u u1 ->
  degree_u_wrt_u 0 u1).
Proof. Admitted.

(* end hide *)

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

(* begin hide *)

Lemma lc_e_of_degree_lc_u_of_degree_size_mutual :
forall i1,
(forall e1,
  size_e e1 = i1 ->
  degree_e_wrt_u 0 e1 ->
  lc_e e1) /\
(forall u1,
  size_u u1 = i1 ->
  degree_u_wrt_u 0 u1 ->
  lc_u u1).
Proof. Admitted.

(* end hide *)

Lemma lc_e_of_degree :
forall e1,
  degree_e_wrt_u 0 e1 ->
  lc_e e1.
Proof. Admitted.

Hint Resolve lc_e_of_degree : lngen.

Lemma lc_u_of_degree :
forall u1,
  degree_u_wrt_u 0 u1 ->
  lc_u u1.
Proof. Admitted.

Hint Resolve lc_u_of_degree : lngen.

Ltac t_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac p_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac e_u_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_e_wrt_u_of_lc_e in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_u_wrt_u_of_lc_u in J1; clear H
          end).

Lemma lc_u_lam_exists :
forall x1 t1 e1,
  lc_e (open_e_wrt_u e1 (u_var_f x1)) ->
  lc_u (u_lam t1 e1).
Proof. Admitted.

Lemma lc_u_let_exists :
forall x1 e1 u1,
  lc_e e1 ->
  lc_u (open_u_wrt_u u1 (u_var_f x1)) ->
  lc_u (u_let e1 u1).
Proof. Admitted.

Hint Extern 1 (lc_u (u_lam _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_u_lam_exists x1).

Hint Extern 1 (lc_u (u_let _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_u_let_exists x1).

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

Lemma lc_body_u_lam_2 :
forall t1 e1,
  lc_u (u_lam t1 e1) ->
  body_e_wrt_u e1.
Proof. Admitted.

Hint Resolve lc_body_u_lam_2 : lngen.

Lemma lc_body_u_let_2 :
forall e1 u1,
  lc_u (u_let e1 u1) ->
  body_u_wrt_u u1.
Proof. Admitted.

Hint Resolve lc_body_u_let_2 : lngen.

(* begin hide *)

Lemma lc_e_unique_lc_u_unique_mutual :
(forall e1 (proof2 proof3 : lc_e e1), proof2 = proof3) /\
(forall u1 (proof2 proof3 : lc_u u1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_e_unique :
forall e1 (proof2 proof3 : lc_e e1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_e_unique : lngen.

Lemma lc_u_unique :
forall u1 (proof2 proof3 : lc_u u1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_u_unique : lngen.

(* begin hide *)

Lemma lc_e_of_lc_set_e_lc_u_of_lc_set_u_mutual :
(forall e1, lc_set_e e1 -> lc_e e1) /\
(forall u1, lc_set_u u1 -> lc_u u1).
Proof. Admitted.

(* end hide *)

Lemma lc_e_of_lc_set_e :
forall e1, lc_set_e e1 -> lc_e e1.
Proof. Admitted.

Hint Resolve lc_e_of_lc_set_e : lngen.

Lemma lc_u_of_lc_set_u :
forall u1, lc_set_u u1 -> lc_u u1.
Proof. Admitted.

Hint Resolve lc_u_of_lc_set_u : lngen.

(* begin hide *)

Lemma lc_set_e_of_lc_e_lc_set_u_of_lc_u_size_mutual :
forall i1,
(forall e1,
  size_e e1 = i1 ->
  lc_e e1 ->
  lc_set_e e1) *
(forall u1,
  size_u u1 = i1 ->
  lc_u u1 ->
  lc_set_u u1).
Proof. Admitted.

(* end hide *)

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


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_e_wrt_u_rec_degree_e_wrt_u_close_u_wrt_u_rec_degree_u_wrt_u_mutual :
(forall e1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  x1 `notin` u_fv_e e1 ->
  close_e_wrt_u_rec n1 x1 e1 = e1) /\
(forall u1 x1 n1,
  degree_u_wrt_u n1 u1 ->
  x1 `notin` u_fv_u u1 ->
  close_u_wrt_u_rec n1 x1 u1 = u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_u_rec_degree_e_wrt_u :
forall e1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  x1 `notin` u_fv_e e1 ->
  close_e_wrt_u_rec n1 x1 e1 = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_u_rec_degree_e_wrt_u : lngen.
Hint Rewrite close_e_wrt_u_rec_degree_e_wrt_u using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_u_rec_degree_u_wrt_u :
forall u1 x1 n1,
  degree_u_wrt_u n1 u1 ->
  x1 `notin` u_fv_u u1 ->
  close_u_wrt_u_rec n1 x1 u1 = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_u_rec_degree_u_wrt_u : lngen.
Hint Rewrite close_u_wrt_u_rec_degree_u_wrt_u using solve [auto] : lngen.

(* end hide *)

Lemma close_e_wrt_u_lc_e :
forall e1 x1,
  lc_e e1 ->
  x1 `notin` u_fv_e e1 ->
  close_e_wrt_u x1 e1 = e1.
Proof. Admitted.

Hint Resolve close_e_wrt_u_lc_e : lngen.
Hint Rewrite close_e_wrt_u_lc_e using solve [auto] : lngen.

Lemma close_u_wrt_u_lc_u :
forall u1 x1,
  lc_u u1 ->
  x1 `notin` u_fv_u u1 ->
  close_u_wrt_u x1 u1 = u1.
Proof. Admitted.

Hint Resolve close_u_wrt_u_lc_u : lngen.
Hint Rewrite close_u_wrt_u_lc_u using solve [auto] : lngen.

(* begin hide *)

Lemma open_e_wrt_u_rec_degree_e_wrt_u_open_u_wrt_u_rec_degree_u_wrt_u_mutual :
(forall e1 u1 n1,
  degree_e_wrt_u n1 e1 ->
  open_e_wrt_u_rec n1 u1 e1 = e1) /\
(forall u2 u1 n1,
  degree_u_wrt_u n1 u2 ->
  open_u_wrt_u_rec n1 u1 u2 = u2).
Proof. Admitted.

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


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma u_fv_e_close_e_wrt_u_rec_u_fv_u_close_u_wrt_u_rec_mutual :
(forall e1 x1 n1,
  u_fv_e (close_e_wrt_u_rec n1 x1 e1) [=] remove x1 (u_fv_e e1)) /\
(forall u1 x1 n1,
  u_fv_u (close_u_wrt_u_rec n1 x1 u1) [=] remove x1 (u_fv_u u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma u_fv_e_close_e_wrt_u_rec :
forall e1 x1 n1,
  u_fv_e (close_e_wrt_u_rec n1 x1 e1) [=] remove x1 (u_fv_e e1).
Proof. Admitted.

Hint Resolve u_fv_e_close_e_wrt_u_rec : lngen.
Hint Rewrite u_fv_e_close_e_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma u_fv_u_close_u_wrt_u_rec :
forall u1 x1 n1,
  u_fv_u (close_u_wrt_u_rec n1 x1 u1) [=] remove x1 (u_fv_u u1).
Proof. Admitted.

Hint Resolve u_fv_u_close_u_wrt_u_rec : lngen.
Hint Rewrite u_fv_u_close_u_wrt_u_rec using solve [auto] : lngen.

(* end hide *)

Lemma u_fv_e_close_e_wrt_u :
forall e1 x1,
  u_fv_e (close_e_wrt_u x1 e1) [=] remove x1 (u_fv_e e1).
Proof. Admitted.

Hint Resolve u_fv_e_close_e_wrt_u : lngen.
Hint Rewrite u_fv_e_close_e_wrt_u using solve [auto] : lngen.

Lemma u_fv_u_close_u_wrt_u :
forall u1 x1,
  u_fv_u (close_u_wrt_u x1 u1) [=] remove x1 (u_fv_u u1).
Proof. Admitted.

Hint Resolve u_fv_u_close_u_wrt_u : lngen.
Hint Rewrite u_fv_u_close_u_wrt_u using solve [auto] : lngen.

(* begin hide *)

Lemma u_fv_e_open_e_wrt_u_rec_lower_u_fv_u_open_u_wrt_u_rec_lower_mutual :
(forall e1 u1 n1,
  u_fv_e e1 [<=] u_fv_e (open_e_wrt_u_rec n1 u1 e1)) /\
(forall u1 u2 n1,
  u_fv_u u1 [<=] u_fv_u (open_u_wrt_u_rec n1 u2 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma u_fv_e_open_e_wrt_u_rec_lower :
forall e1 u1 n1,
  u_fv_e e1 [<=] u_fv_e (open_e_wrt_u_rec n1 u1 e1).
Proof. Admitted.

Hint Resolve u_fv_e_open_e_wrt_u_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma u_fv_u_open_u_wrt_u_rec_lower :
forall u1 u2 n1,
  u_fv_u u1 [<=] u_fv_u (open_u_wrt_u_rec n1 u2 u1).
Proof. Admitted.

Hint Resolve u_fv_u_open_u_wrt_u_rec_lower : lngen.

(* end hide *)

Lemma u_fv_e_open_e_wrt_u_lower :
forall e1 u1,
  u_fv_e e1 [<=] u_fv_e (open_e_wrt_u e1 u1).
Proof. Admitted.

Hint Resolve u_fv_e_open_e_wrt_u_lower : lngen.

Lemma u_fv_u_open_u_wrt_u_lower :
forall u1 u2,
  u_fv_u u1 [<=] u_fv_u (open_u_wrt_u u1 u2).
Proof. Admitted.

Hint Resolve u_fv_u_open_u_wrt_u_lower : lngen.

(* begin hide *)

Lemma u_fv_e_open_e_wrt_u_rec_upper_u_fv_u_open_u_wrt_u_rec_upper_mutual :
(forall e1 u1 n1,
  u_fv_e (open_e_wrt_u_rec n1 u1 e1) [<=] u_fv_u u1 `union` u_fv_e e1) /\
(forall u1 u2 n1,
  u_fv_u (open_u_wrt_u_rec n1 u2 u1) [<=] u_fv_u u2 `union` u_fv_u u1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma u_fv_e_open_e_wrt_u_rec_upper :
forall e1 u1 n1,
  u_fv_e (open_e_wrt_u_rec n1 u1 e1) [<=] u_fv_u u1 `union` u_fv_e e1.
Proof. Admitted.

Hint Resolve u_fv_e_open_e_wrt_u_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma u_fv_u_open_u_wrt_u_rec_upper :
forall u1 u2 n1,
  u_fv_u (open_u_wrt_u_rec n1 u2 u1) [<=] u_fv_u u2 `union` u_fv_u u1.
Proof. Admitted.

Hint Resolve u_fv_u_open_u_wrt_u_rec_upper : lngen.

(* end hide *)

Lemma u_fv_e_open_e_wrt_u_upper :
forall e1 u1,
  u_fv_e (open_e_wrt_u e1 u1) [<=] u_fv_u u1 `union` u_fv_e e1.
Proof. Admitted.

Hint Resolve u_fv_e_open_e_wrt_u_upper : lngen.

Lemma u_fv_u_open_u_wrt_u_upper :
forall u1 u2,
  u_fv_u (open_u_wrt_u u1 u2) [<=] u_fv_u u2 `union` u_fv_u u1.
Proof. Admitted.

Hint Resolve u_fv_u_open_u_wrt_u_upper : lngen.

(* begin hide *)

Lemma u_fv_e_u_subst_e_fresh_u_fv_u_u_subst_u_fresh_mutual :
(forall e1 u1 x1,
  x1 `notin` u_fv_e e1 ->
  u_fv_e (u_subst_e u1 x1 e1) [=] u_fv_e e1) /\
(forall u1 u2 x1,
  x1 `notin` u_fv_u u1 ->
  u_fv_u (u_subst_u u2 x1 u1) [=] u_fv_u u1).
Proof. Admitted.

(* end hide *)

Lemma u_fv_e_u_subst_e_fresh :
forall e1 u1 x1,
  x1 `notin` u_fv_e e1 ->
  u_fv_e (u_subst_e u1 x1 e1) [=] u_fv_e e1.
Proof. Admitted.

Hint Resolve u_fv_e_u_subst_e_fresh : lngen.
Hint Rewrite u_fv_e_u_subst_e_fresh using solve [auto] : lngen.

Lemma u_fv_u_u_subst_u_fresh :
forall u1 u2 x1,
  x1 `notin` u_fv_u u1 ->
  u_fv_u (u_subst_u u2 x1 u1) [=] u_fv_u u1.
Proof. Admitted.

Hint Resolve u_fv_u_u_subst_u_fresh : lngen.
Hint Rewrite u_fv_u_u_subst_u_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma u_fv_e_u_subst_e_lower_u_fv_u_u_subst_u_lower_mutual :
(forall e1 u1 x1,
  remove x1 (u_fv_e e1) [<=] u_fv_e (u_subst_e u1 x1 e1)) /\
(forall u1 u2 x1,
  remove x1 (u_fv_u u1) [<=] u_fv_u (u_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma u_fv_e_u_subst_e_lower :
forall e1 u1 x1,
  remove x1 (u_fv_e e1) [<=] u_fv_e (u_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve u_fv_e_u_subst_e_lower : lngen.

Lemma u_fv_u_u_subst_u_lower :
forall u1 u2 x1,
  remove x1 (u_fv_u u1) [<=] u_fv_u (u_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve u_fv_u_u_subst_u_lower : lngen.

(* begin hide *)

Lemma u_fv_e_u_subst_e_notin_u_fv_u_u_subst_u_notin_mutual :
(forall e1 u1 x1 x2,
  x2 `notin` u_fv_e e1 ->
  x2 `notin` u_fv_u u1 ->
  x2 `notin` u_fv_e (u_subst_e u1 x1 e1)) /\
(forall u1 u2 x1 x2,
  x2 `notin` u_fv_u u1 ->
  x2 `notin` u_fv_u u2 ->
  x2 `notin` u_fv_u (u_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma u_fv_e_u_subst_e_notin :
forall e1 u1 x1 x2,
  x2 `notin` u_fv_e e1 ->
  x2 `notin` u_fv_u u1 ->
  x2 `notin` u_fv_e (u_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve u_fv_e_u_subst_e_notin : lngen.

Lemma u_fv_u_u_subst_u_notin :
forall u1 u2 x1 x2,
  x2 `notin` u_fv_u u1 ->
  x2 `notin` u_fv_u u2 ->
  x2 `notin` u_fv_u (u_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve u_fv_u_u_subst_u_notin : lngen.

(* begin hide *)

Lemma u_fv_e_u_subst_e_upper_u_fv_u_u_subst_u_upper_mutual :
(forall e1 u1 x1,
  u_fv_e (u_subst_e u1 x1 e1) [<=] u_fv_u u1 `union` remove x1 (u_fv_e e1)) /\
(forall u1 u2 x1,
  u_fv_u (u_subst_u u2 x1 u1) [<=] u_fv_u u2 `union` remove x1 (u_fv_u u1)).
Proof. Admitted.

(* end hide *)

Lemma u_fv_e_u_subst_e_upper :
forall e1 u1 x1,
  u_fv_e (u_subst_e u1 x1 e1) [<=] u_fv_u u1 `union` remove x1 (u_fv_e e1).
Proof. Admitted.

Hint Resolve u_fv_e_u_subst_e_upper : lngen.

Lemma u_fv_u_u_subst_u_upper :
forall u1 u2 x1,
  u_fv_u (u_subst_u u2 x1 u1) [<=] u_fv_u u2 `union` remove x1 (u_fv_u u1).
Proof. Admitted.

Hint Resolve u_fv_u_u_subst_u_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma u_subst_e_close_e_wrt_u_rec_u_subst_u_close_u_wrt_u_rec_mutual :
(forall e1 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` u_fv_u u1 ->
  u_subst_e u1 x1 (close_e_wrt_u_rec n1 x2 e1) = close_e_wrt_u_rec n1 x2 (u_subst_e u1 x1 e1)) /\
(forall u2 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` u_fv_u u1 ->
  u_subst_u u1 x1 (close_u_wrt_u_rec n1 x2 u2) = close_u_wrt_u_rec n1 x2 (u_subst_u u1 x1 u2)).
Proof. Admitted.

(* end hide *)

Lemma u_subst_e_close_e_wrt_u_rec :
forall e1 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` u_fv_u u1 ->
  u_subst_e u1 x1 (close_e_wrt_u_rec n1 x2 e1) = close_e_wrt_u_rec n1 x2 (u_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve u_subst_e_close_e_wrt_u_rec : lngen.

Lemma u_subst_u_close_u_wrt_u_rec :
forall u2 u1 x1 x2 n1,
  degree_u_wrt_u n1 u1 ->
  x1 <> x2 ->
  x2 `notin` u_fv_u u1 ->
  u_subst_u u1 x1 (close_u_wrt_u_rec n1 x2 u2) = close_u_wrt_u_rec n1 x2 (u_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve u_subst_u_close_u_wrt_u_rec : lngen.

Lemma u_subst_e_close_e_wrt_u :
forall e1 u1 x1 x2,
  lc_u u1 ->  x1 <> x2 ->
  x2 `notin` u_fv_u u1 ->
  u_subst_e u1 x1 (close_e_wrt_u x2 e1) = close_e_wrt_u x2 (u_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve u_subst_e_close_e_wrt_u : lngen.

Lemma u_subst_u_close_u_wrt_u :
forall u2 u1 x1 x2,
  lc_u u1 ->  x1 <> x2 ->
  x2 `notin` u_fv_u u1 ->
  u_subst_u u1 x1 (close_u_wrt_u x2 u2) = close_u_wrt_u x2 (u_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve u_subst_u_close_u_wrt_u : lngen.

(* begin hide *)

Lemma u_subst_e_degree_e_wrt_u_u_subst_u_degree_u_wrt_u_mutual :
(forall e1 u1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_u_wrt_u n1 u1 ->
  degree_e_wrt_u n1 (u_subst_e u1 x1 e1)) /\
(forall u1 u2 x1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 u2 ->
  degree_u_wrt_u n1 (u_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma u_subst_e_degree_e_wrt_u :
forall e1 u1 x1 n1,
  degree_e_wrt_u n1 e1 ->
  degree_u_wrt_u n1 u1 ->
  degree_e_wrt_u n1 (u_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve u_subst_e_degree_e_wrt_u : lngen.

Lemma u_subst_u_degree_u_wrt_u :
forall u1 u2 x1 n1,
  degree_u_wrt_u n1 u1 ->
  degree_u_wrt_u n1 u2 ->
  degree_u_wrt_u n1 (u_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve u_subst_u_degree_u_wrt_u : lngen.

(* begin hide *)

Lemma u_subst_e_fresh_eq_u_subst_u_fresh_eq_mutual :
(forall e1 u1 x1,
  x1 `notin` u_fv_e e1 ->
  u_subst_e u1 x1 e1 = e1) /\
(forall u2 u1 x1,
  x1 `notin` u_fv_u u2 ->
  u_subst_u u1 x1 u2 = u2).
Proof. Admitted.

(* end hide *)

Lemma u_subst_e_fresh_eq :
forall e1 u1 x1,
  x1 `notin` u_fv_e e1 ->
  u_subst_e u1 x1 e1 = e1.
Proof. Admitted.

Hint Resolve u_subst_e_fresh_eq : lngen.
Hint Rewrite u_subst_e_fresh_eq using solve [auto] : lngen.

Lemma u_subst_u_fresh_eq :
forall u2 u1 x1,
  x1 `notin` u_fv_u u2 ->
  u_subst_u u1 x1 u2 = u2.
Proof. Admitted.

Hint Resolve u_subst_u_fresh_eq : lngen.
Hint Rewrite u_subst_u_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma u_subst_e_fresh_same_u_subst_u_fresh_same_mutual :
(forall e1 u1 x1,
  x1 `notin` u_fv_u u1 ->
  x1 `notin` u_fv_e (u_subst_e u1 x1 e1)) /\
(forall u2 u1 x1,
  x1 `notin` u_fv_u u1 ->
  x1 `notin` u_fv_u (u_subst_u u1 x1 u2)).
Proof. Admitted.

(* end hide *)

Lemma u_subst_e_fresh_same :
forall e1 u1 x1,
  x1 `notin` u_fv_u u1 ->
  x1 `notin` u_fv_e (u_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve u_subst_e_fresh_same : lngen.

Lemma u_subst_u_fresh_same :
forall u2 u1 x1,
  x1 `notin` u_fv_u u1 ->
  x1 `notin` u_fv_u (u_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve u_subst_u_fresh_same : lngen.

(* begin hide *)

Lemma u_subst_e_fresh_u_subst_u_fresh_mutual :
(forall e1 u1 x1 x2,
  x1 `notin` u_fv_e e1 ->
  x1 `notin` u_fv_u u1 ->
  x1 `notin` u_fv_e (u_subst_e u1 x2 e1)) /\
(forall u2 u1 x1 x2,
  x1 `notin` u_fv_u u2 ->
  x1 `notin` u_fv_u u1 ->
  x1 `notin` u_fv_u (u_subst_u u1 x2 u2)).
Proof. Admitted.

(* end hide *)

Lemma u_subst_e_fresh :
forall e1 u1 x1 x2,
  x1 `notin` u_fv_e e1 ->
  x1 `notin` u_fv_u u1 ->
  x1 `notin` u_fv_e (u_subst_e u1 x2 e1).
Proof. Admitted.

Hint Resolve u_subst_e_fresh : lngen.

Lemma u_subst_u_fresh :
forall u2 u1 x1 x2,
  x1 `notin` u_fv_u u2 ->
  x1 `notin` u_fv_u u1 ->
  x1 `notin` u_fv_u (u_subst_u u1 x2 u2).
Proof. Admitted.

Hint Resolve u_subst_u_fresh : lngen.

Lemma u_subst_e_lc_e :
forall e1 u1 x1,
  lc_e e1 ->
  lc_u u1 ->
  lc_e (u_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve u_subst_e_lc_e : lngen.

Lemma u_subst_u_lc_u :
forall u1 u2 x1,
  lc_u u1 ->
  lc_u u2 ->
  lc_u (u_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve u_subst_u_lc_u : lngen.

(* begin hide *)

Lemma u_subst_e_open_e_wrt_u_rec_u_subst_u_open_u_wrt_u_rec_mutual :
(forall e1 u1 u2 x1 n1,
  lc_u u1 ->
  u_subst_e u1 x1 (open_e_wrt_u_rec n1 u2 e1) = open_e_wrt_u_rec n1 (u_subst_u u1 x1 u2) (u_subst_e u1 x1 e1)) /\
(forall u3 u1 u2 x1 n1,
  lc_u u1 ->
  u_subst_u u1 x1 (open_u_wrt_u_rec n1 u2 u3) = open_u_wrt_u_rec n1 (u_subst_u u1 x1 u2) (u_subst_u u1 x1 u3)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma u_subst_e_open_e_wrt_u_rec :
forall e1 u1 u2 x1 n1,
  lc_u u1 ->
  u_subst_e u1 x1 (open_e_wrt_u_rec n1 u2 e1) = open_e_wrt_u_rec n1 (u_subst_u u1 x1 u2) (u_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve u_subst_e_open_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma u_subst_u_open_u_wrt_u_rec :
forall u3 u1 u2 x1 n1,
  lc_u u1 ->
  u_subst_u u1 x1 (open_u_wrt_u_rec n1 u2 u3) = open_u_wrt_u_rec n1 (u_subst_u u1 x1 u2) (u_subst_u u1 x1 u3).
Proof. Admitted.

Hint Resolve u_subst_u_open_u_wrt_u_rec : lngen.

(* end hide *)

Lemma u_subst_e_open_e_wrt_u :
forall e1 u1 u2 x1,
  lc_u u1 ->
  u_subst_e u1 x1 (open_e_wrt_u e1 u2) = open_e_wrt_u (u_subst_e u1 x1 e1) (u_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve u_subst_e_open_e_wrt_u : lngen.

Lemma u_subst_u_open_u_wrt_u :
forall u3 u1 u2 x1,
  lc_u u1 ->
  u_subst_u u1 x1 (open_u_wrt_u u3 u2) = open_u_wrt_u (u_subst_u u1 x1 u3) (u_subst_u u1 x1 u2).
Proof. Admitted.

Hint Resolve u_subst_u_open_u_wrt_u : lngen.

Lemma u_subst_e_open_e_wrt_u_var :
forall e1 u1 x1 x2,
  x1 <> x2 ->
  lc_u u1 ->
  open_e_wrt_u (u_subst_e u1 x1 e1) (u_var_f x2) = u_subst_e u1 x1 (open_e_wrt_u e1 (u_var_f x2)).
Proof. Admitted.

Hint Resolve u_subst_e_open_e_wrt_u_var : lngen.

Lemma u_subst_u_open_u_wrt_u_var :
forall u2 u1 x1 x2,
  x1 <> x2 ->
  lc_u u1 ->
  open_u_wrt_u (u_subst_u u1 x1 u2) (u_var_f x2) = u_subst_u u1 x1 (open_u_wrt_u u2 (u_var_f x2)).
Proof. Admitted.

Hint Resolve u_subst_u_open_u_wrt_u_var : lngen.

(* begin hide *)

Lemma u_subst_e_spec_rec_u_subst_u_spec_rec_mutual :
(forall e1 u1 x1 n1,
  u_subst_e u1 x1 e1 = open_e_wrt_u_rec n1 u1 (close_e_wrt_u_rec n1 x1 e1)) /\
(forall u1 u2 x1 n1,
  u_subst_u u2 x1 u1 = open_u_wrt_u_rec n1 u2 (close_u_wrt_u_rec n1 x1 u1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma u_subst_e_spec_rec :
forall e1 u1 x1 n1,
  u_subst_e u1 x1 e1 = open_e_wrt_u_rec n1 u1 (close_e_wrt_u_rec n1 x1 e1).
Proof. Admitted.

Hint Resolve u_subst_e_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma u_subst_u_spec_rec :
forall u1 u2 x1 n1,
  u_subst_u u2 x1 u1 = open_u_wrt_u_rec n1 u2 (close_u_wrt_u_rec n1 x1 u1).
Proof. Admitted.

Hint Resolve u_subst_u_spec_rec : lngen.

(* end hide *)

Lemma u_subst_e_spec :
forall e1 u1 x1,
  u_subst_e u1 x1 e1 = open_e_wrt_u (close_e_wrt_u x1 e1) u1.
Proof. Admitted.

Hint Resolve u_subst_e_spec : lngen.

Lemma u_subst_u_spec :
forall u1 u2 x1,
  u_subst_u u2 x1 u1 = open_u_wrt_u (close_u_wrt_u x1 u1) u2.
Proof. Admitted.

Hint Resolve u_subst_u_spec : lngen.

(* begin hide *)

Lemma u_subst_e_u_subst_e_u_subst_u_u_subst_u_mutual :
(forall e1 u1 u2 x2 x1,
  x2 `notin` u_fv_u u1 ->
  x2 <> x1 ->
  u_subst_e u1 x1 (u_subst_e u2 x2 e1) = u_subst_e (u_subst_u u1 x1 u2) x2 (u_subst_e u1 x1 e1)) /\
(forall u1 u2 u3 x2 x1,
  x2 `notin` u_fv_u u2 ->
  x2 <> x1 ->
  u_subst_u u2 x1 (u_subst_u u3 x2 u1) = u_subst_u (u_subst_u u2 x1 u3) x2 (u_subst_u u2 x1 u1)).
Proof. Admitted.

(* end hide *)

Lemma u_subst_e_u_subst_e :
forall e1 u1 u2 x2 x1,
  x2 `notin` u_fv_u u1 ->
  x2 <> x1 ->
  u_subst_e u1 x1 (u_subst_e u2 x2 e1) = u_subst_e (u_subst_u u1 x1 u2) x2 (u_subst_e u1 x1 e1).
Proof. Admitted.

Hint Resolve u_subst_e_u_subst_e : lngen.

Lemma u_subst_u_u_subst_u :
forall u1 u2 u3 x2 x1,
  x2 `notin` u_fv_u u2 ->
  x2 <> x1 ->
  u_subst_u u2 x1 (u_subst_u u3 x2 u1) = u_subst_u (u_subst_u u2 x1 u3) x2 (u_subst_u u2 x1 u1).
Proof. Admitted.

Hint Resolve u_subst_u_u_subst_u : lngen.

(* begin hide *)

Lemma u_subst_e_close_e_wrt_u_rec_open_e_wrt_u_rec_u_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec_mutual :
(forall e1 u1 x1 x2 n1,
  x2 `notin` u_fv_e e1 ->
  x2 `notin` u_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  u_subst_e u1 x1 e1 = close_e_wrt_u_rec n1 x2 (u_subst_e u1 x1 (open_e_wrt_u_rec n1 (u_var_f x2) e1))) *
(forall u2 u1 x1 x2 n1,
  x2 `notin` u_fv_u u2 ->
  x2 `notin` u_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  u_subst_u u1 x1 u2 = close_u_wrt_u_rec n1 x2 (u_subst_u u1 x1 (open_u_wrt_u_rec n1 (u_var_f x2) u2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma u_subst_e_close_e_wrt_u_rec_open_e_wrt_u_rec :
forall e1 u1 x1 x2 n1,
  x2 `notin` u_fv_e e1 ->
  x2 `notin` u_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  u_subst_e u1 x1 e1 = close_e_wrt_u_rec n1 x2 (u_subst_e u1 x1 (open_e_wrt_u_rec n1 (u_var_f x2) e1)).
Proof. Admitted.

Hint Resolve u_subst_e_close_e_wrt_u_rec_open_e_wrt_u_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma u_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec :
forall u2 u1 x1 x2 n1,
  x2 `notin` u_fv_u u2 ->
  x2 `notin` u_fv_u u1 ->
  x2 <> x1 ->
  degree_u_wrt_u n1 u1 ->
  u_subst_u u1 x1 u2 = close_u_wrt_u_rec n1 x2 (u_subst_u u1 x1 (open_u_wrt_u_rec n1 (u_var_f x2) u2)).
Proof. Admitted.

Hint Resolve u_subst_u_close_u_wrt_u_rec_open_u_wrt_u_rec : lngen.

(* end hide *)

Lemma u_subst_e_close_e_wrt_u_open_e_wrt_u :
forall e1 u1 x1 x2,
  x2 `notin` u_fv_e e1 ->
  x2 `notin` u_fv_u u1 ->
  x2 <> x1 ->
  lc_u u1 ->
  u_subst_e u1 x1 e1 = close_e_wrt_u x2 (u_subst_e u1 x1 (open_e_wrt_u e1 (u_var_f x2))).
Proof. Admitted.

Hint Resolve u_subst_e_close_e_wrt_u_open_e_wrt_u : lngen.

Lemma u_subst_u_close_u_wrt_u_open_u_wrt_u :
forall u2 u1 x1 x2,
  x2 `notin` u_fv_u u2 ->
  x2 `notin` u_fv_u u1 ->
  x2 <> x1 ->
  lc_u u1 ->
  u_subst_u u1 x1 u2 = close_u_wrt_u x2 (u_subst_u u1 x1 (open_u_wrt_u u2 (u_var_f x2))).
Proof. Admitted.

Hint Resolve u_subst_u_close_u_wrt_u_open_u_wrt_u : lngen.

Lemma u_subst_u_u_lam :
forall x2 t1 e1 u1 x1,
  lc_u u1 ->
  x2 `notin` u_fv_u u1 `union` u_fv_e e1 `union` singleton x1 ->
  u_subst_u u1 x1 (u_lam t1 e1) = u_lam (t1) (close_e_wrt_u x2 (u_subst_e u1 x1 (open_e_wrt_u e1 (u_var_f x2)))).
Proof. Admitted.

Hint Resolve u_subst_u_u_lam : lngen.

Lemma u_subst_u_u_let :
forall x2 e1 u2 u1 x1,
  lc_u u1 ->
  x2 `notin` u_fv_u u1 `union` u_fv_u u2 `union` singleton x1 ->
  u_subst_u u1 x1 (u_let e1 u2) = u_let (u_subst_e u1 x1 e1) (close_u_wrt_u x2 (u_subst_u u1 x1 (open_u_wrt_u u2 (u_var_f x2)))).
Proof. Admitted.

Hint Resolve u_subst_u_u_let : lngen.

(* begin hide *)

Lemma u_subst_e_intro_rec_u_subst_u_intro_rec_mutual :
(forall e1 x1 u1 n1,
  x1 `notin` u_fv_e e1 ->
  open_e_wrt_u_rec n1 u1 e1 = u_subst_e u1 x1 (open_e_wrt_u_rec n1 (u_var_f x1) e1)) /\
(forall u1 x1 u2 n1,
  x1 `notin` u_fv_u u1 ->
  open_u_wrt_u_rec n1 u2 u1 = u_subst_u u2 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1)).
Proof. Admitted.

(* end hide *)

Lemma u_subst_e_intro_rec :
forall e1 x1 u1 n1,
  x1 `notin` u_fv_e e1 ->
  open_e_wrt_u_rec n1 u1 e1 = u_subst_e u1 x1 (open_e_wrt_u_rec n1 (u_var_f x1) e1).
Proof. Admitted.

Hint Resolve u_subst_e_intro_rec : lngen.
Hint Rewrite u_subst_e_intro_rec using solve [auto] : lngen.

Lemma u_subst_u_intro_rec :
forall u1 x1 u2 n1,
  x1 `notin` u_fv_u u1 ->
  open_u_wrt_u_rec n1 u2 u1 = u_subst_u u2 x1 (open_u_wrt_u_rec n1 (u_var_f x1) u1).
Proof. Admitted.

Hint Resolve u_subst_u_intro_rec : lngen.
Hint Rewrite u_subst_u_intro_rec using solve [auto] : lngen.

Lemma u_subst_e_intro :
forall x1 e1 u1,
  x1 `notin` u_fv_e e1 ->
  open_e_wrt_u e1 u1 = u_subst_e u1 x1 (open_e_wrt_u e1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve u_subst_e_intro : lngen.

Lemma u_subst_u_intro :
forall x1 u1 u2,
  x1 `notin` u_fv_u u1 ->
  open_u_wrt_u u1 u2 = u_subst_u u2 x1 (open_u_wrt_u u1 (u_var_f x1)).
Proof. Admitted.

Hint Resolve u_subst_u_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
