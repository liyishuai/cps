Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metatheory.
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
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme u_rec' := Induction for u Sort Set.

Definition u_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  u_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.


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

Fixpoint close_u_wrt_t_rec (n1 : nat) (a1 : a) (u1 : u) {struct u1} : u :=
  match u1 with
    | u_var x1 => u_var x1
    | u_int i1 => u_int i1
    | u_fix x1 x2 t1 t2 e1 => u_fix x1 x2 (close_t_wrt_t_rec n1 a1 t1) (close_t_wrt_t_rec n1 a1 t2) (close_u_wrt_t_rec n1 a1 e1)
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
    | u_var x1 => 1
    | u_int i1 => 1
    | u_fix x1 x2 t1 t2 e1 => 1 + (size_t t1) + (size_t t2) + (size_u e1)
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

Inductive degree_u_wrt_t : nat -> u -> Prop :=
  | degree_wrt_t_u_var : forall n1 x1,
    degree_u_wrt_t n1 (u_var x1)
  | degree_wrt_t_u_int : forall n1 i1,
    degree_u_wrt_t n1 (u_int i1)
  | degree_wrt_t_u_fix : forall n1 x1 x2 t1 t2 e1,
    degree_t_wrt_t n1 t1 ->
    degree_t_wrt_t n1 t2 ->
    degree_u_wrt_t n1 e1 ->
    degree_u_wrt_t n1 (u_fix x1 x2 t1 t2 e1)
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

Scheme degree_u_wrt_t_ind' := Induction for degree_u_wrt_t Sort Prop.

Definition degree_u_wrt_t_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  degree_u_wrt_t_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

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
  | lc_set_u_var : forall x1,
    lc_set_u (u_var x1)
  | lc_set_u_int : forall i1,
    lc_set_u (u_int i1)
  | lc_set_u_fix : forall x1 x2 t1 t2 e1,
    lc_set_t t1 ->
    lc_set_t t2 ->
    lc_set_u e1 ->
    lc_set_u (u_fix x1 x2 t1 t2 e1)
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
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  lc_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme lc_set_u_ind' := Induction for lc_set_u Sort Prop.

Definition lc_set_u_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  lc_set_u_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme lc_set_u_rec' := Induction for lc_set_u Sort Set.

Definition lc_set_u_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  lc_set_u_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Hint Constructors lc_u : core lngen.

Hint Constructors lc_set_u : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_t_wrt_t t1 := forall a1, lc_t (open_t_wrt_t t1 (t_var_f a1)).

Hint Unfold body_t_wrt_t.

Definition body_u_wrt_t u1 := forall a1, lc_u (open_u_wrt_t u1 (t_var_f a1)).

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
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_t_min :
forall t1, 1 <= size_t t1.
Proof.
pose proof size_t_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_t_min : lngen.

(* begin hide *)

Lemma size_p_min_mutual :
(forall p1, 1 <= size_p p1).
Proof.
apply_mutual_ind p_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_p_min :
forall p1, 1 <= size_p p1.
Proof.
pose proof size_p_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_p_min : lngen.

(* begin hide *)

Lemma size_u_min_mutual :
(forall u1, 1 <= size_u u1).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_u_min :
forall u1, 1 <= size_u u1.
Proof.
pose proof size_u_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_u_min : lngen.

(* begin hide *)

Lemma size_t_close_t_wrt_t_rec_mutual :
(forall t1 a1 n1,
  size_t (close_t_wrt_t_rec n1 a1 t1) = size_t t1).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_t_close_t_wrt_t_rec :
forall t1 a1 n1,
  size_t (close_t_wrt_t_rec n1 a1 t1) = size_t t1.
Proof.
pose proof size_t_close_t_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_t_close_t_wrt_t_rec : lngen.
Hint Rewrite size_t_close_t_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_u_close_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  size_u (close_u_wrt_t_rec n1 a1 u1) = size_u u1).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_u_close_u_wrt_t_rec :
forall u1 a1 n1,
  size_u (close_u_wrt_t_rec n1 a1 u1) = size_u u1.
Proof.
pose proof size_u_close_u_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_u_close_u_wrt_t_rec : lngen.
Hint Rewrite size_u_close_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_t_close_t_wrt_t :
forall t1 a1,
  size_t (close_t_wrt_t a1 t1) = size_t t1.
Proof.
unfold close_t_wrt_t; default_simp.
Qed.

Hint Resolve size_t_close_t_wrt_t : lngen.
Hint Rewrite size_t_close_t_wrt_t using solve [auto] : lngen.

Lemma size_u_close_u_wrt_t :
forall u1 a1,
  size_u (close_u_wrt_t a1 u1) = size_u u1.
Proof.
unfold close_u_wrt_t; default_simp.
Qed.

Hint Resolve size_u_close_u_wrt_t : lngen.
Hint Rewrite size_u_close_u_wrt_t using solve [auto] : lngen.

(* begin hide *)

Lemma size_t_open_t_wrt_t_rec_mutual :
(forall t1 t2 n1,
  size_t t1 <= size_t (open_t_wrt_t_rec n1 t2 t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_t_open_t_wrt_t_rec :
forall t1 t2 n1,
  size_t t1 <= size_t (open_t_wrt_t_rec n1 t2 t1).
Proof.
pose proof size_t_open_t_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_t_open_t_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_t_rec_mutual :
(forall u1 t1 n1,
  size_u u1 <= size_u (open_u_wrt_t_rec n1 t1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_t_rec :
forall u1 t1 n1,
  size_u u1 <= size_u (open_u_wrt_t_rec n1 t1 u1).
Proof.
pose proof size_u_open_u_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_u_open_u_wrt_t_rec : lngen.

(* end hide *)

Lemma size_t_open_t_wrt_t :
forall t1 t2,
  size_t t1 <= size_t (open_t_wrt_t t1 t2).
Proof.
unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve size_t_open_t_wrt_t : lngen.

Lemma size_u_open_u_wrt_t :
forall u1 t1,
  size_u u1 <= size_u (open_u_wrt_t u1 t1).
Proof.
unfold open_u_wrt_t; default_simp.
Qed.

Hint Resolve size_u_open_u_wrt_t : lngen.

(* begin hide *)

Lemma size_t_open_t_wrt_t_rec_var_mutual :
(forall t1 a1 n1,
  size_t (open_t_wrt_t_rec n1 (t_var_f a1) t1) = size_t t1).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_t_open_t_wrt_t_rec_var :
forall t1 a1 n1,
  size_t (open_t_wrt_t_rec n1 (t_var_f a1) t1) = size_t t1.
Proof.
pose proof size_t_open_t_wrt_t_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_t_open_t_wrt_t_rec_var : lngen.
Hint Rewrite size_t_open_t_wrt_t_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_t_rec_var_mutual :
(forall u1 a1 n1,
  size_u (open_u_wrt_t_rec n1 (t_var_f a1) u1) = size_u u1).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_u_open_u_wrt_t_rec_var :
forall u1 a1 n1,
  size_u (open_u_wrt_t_rec n1 (t_var_f a1) u1) = size_u u1.
Proof.
pose proof size_u_open_u_wrt_t_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_u_open_u_wrt_t_rec_var : lngen.
Hint Rewrite size_u_open_u_wrt_t_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_t_open_t_wrt_t_var :
forall t1 a1,
  size_t (open_t_wrt_t t1 (t_var_f a1)) = size_t t1.
Proof.
unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve size_t_open_t_wrt_t_var : lngen.
Hint Rewrite size_t_open_t_wrt_t_var using solve [auto] : lngen.

Lemma size_u_open_u_wrt_t_var :
forall u1 a1,
  size_u (open_u_wrt_t u1 (t_var_f a1)) = size_u u1.
Proof.
unfold open_u_wrt_t; default_simp.
Qed.

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
Proof.
apply_mutual_ind degree_t_wrt_t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_t_wrt_t_S :
forall n1 t1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t (S n1) t1.
Proof.
pose proof degree_t_wrt_t_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_t_wrt_t_S : lngen.

(* begin hide *)

Lemma degree_u_wrt_t_S_mutual :
(forall n1 u1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) u1).
Proof.
apply_mutual_ind degree_u_wrt_t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_u_wrt_t_S :
forall n1 u1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) u1.
Proof.
pose proof degree_u_wrt_t_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_u_wrt_t_S : lngen.

Lemma degree_t_wrt_t_O :
forall n1 t1,
  degree_t_wrt_t O t1 ->
  degree_t_wrt_t n1 t1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_t_wrt_t_O : lngen.

Lemma degree_u_wrt_t_O :
forall n1 u1,
  degree_u_wrt_t O u1 ->
  degree_u_wrt_t n1 u1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_u_wrt_t_O : lngen.

(* begin hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_rec_mutual :
(forall t1 a1 n1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t (S n1) (close_t_wrt_t_rec n1 a1 t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_rec :
forall t1 a1 n1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t (S n1) (close_t_wrt_t_rec n1 a1 t1).
Proof.
pose proof degree_t_wrt_t_close_t_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_t_wrt_t_close_t_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_close_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_close_u_wrt_t_rec :
forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1).
Proof.
pose proof degree_u_wrt_t_close_u_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_u_wrt_t_close_u_wrt_t_rec : lngen.

(* end hide *)

Lemma degree_t_wrt_t_close_t_wrt_t :
forall t1 a1,
  degree_t_wrt_t 0 t1 ->
  degree_t_wrt_t 1 (close_t_wrt_t a1 t1).
Proof.
unfold close_t_wrt_t; default_simp.
Qed.

Hint Resolve degree_t_wrt_t_close_t_wrt_t : lngen.

Lemma degree_u_wrt_t_close_u_wrt_t :
forall u1 a1,
  degree_u_wrt_t 0 u1 ->
  degree_u_wrt_t 1 (close_u_wrt_t a1 u1).
Proof.
unfold close_u_wrt_t; default_simp.
Qed.

Hint Resolve degree_u_wrt_t_close_u_wrt_t : lngen.

(* begin hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_rec_inv_mutual :
(forall t1 a1 n1,
  degree_t_wrt_t (S n1) (close_t_wrt_t_rec n1 a1 t1) ->
  degree_t_wrt_t n1 t1).
Proof.
apply_mutual_ind t_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_rec_inv :
forall t1 a1 n1,
  degree_t_wrt_t (S n1) (close_t_wrt_t_rec n1 a1 t1) ->
  degree_t_wrt_t n1 t1.
Proof.
pose proof degree_t_wrt_t_close_t_wrt_t_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_t_wrt_t_close_t_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_close_u_wrt_t_rec_inv_mutual :
(forall u1 a1 n1,
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1) ->
  degree_u_wrt_t n1 u1).
Proof.
apply_mutual_ind u_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_close_u_wrt_t_rec_inv :
forall u1 a1 n1,
  degree_u_wrt_t (S n1) (close_u_wrt_t_rec n1 a1 u1) ->
  degree_u_wrt_t n1 u1.
Proof.
pose proof degree_u_wrt_t_close_u_wrt_t_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_u_wrt_t_close_u_wrt_t_rec_inv : lngen.

(* end hide *)

Lemma degree_t_wrt_t_close_t_wrt_t_inv :
forall t1 a1,
  degree_t_wrt_t 1 (close_t_wrt_t a1 t1) ->
  degree_t_wrt_t 0 t1.
Proof.
unfold close_t_wrt_t; eauto with lngen.
Qed.

Hint Immediate degree_t_wrt_t_close_t_wrt_t_inv : lngen.

Lemma degree_u_wrt_t_close_u_wrt_t_inv :
forall u1 a1,
  degree_u_wrt_t 1 (close_u_wrt_t a1 u1) ->
  degree_u_wrt_t 0 u1.
Proof.
unfold close_u_wrt_t; eauto with lngen.
Qed.

Hint Immediate degree_u_wrt_t_close_u_wrt_t_inv : lngen.

(* begin hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_rec_mutual :
(forall t1 t2 n1,
  degree_t_wrt_t (S n1) t1 ->
  degree_t_wrt_t n1 t2 ->
  degree_t_wrt_t n1 (open_t_wrt_t_rec n1 t2 t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_rec :
forall t1 t2 n1,
  degree_t_wrt_t (S n1) t1 ->
  degree_t_wrt_t n1 t2 ->
  degree_t_wrt_t n1 (open_t_wrt_t_rec n1 t2 t1).
Proof.
pose proof degree_t_wrt_t_open_t_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_t_wrt_t_open_t_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_open_u_wrt_t_rec_mutual :
(forall u1 t1 n1,
  degree_u_wrt_t (S n1) u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_open_u_wrt_t_rec :
forall u1 t1 n1,
  degree_u_wrt_t (S n1) u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1).
Proof.
pose proof degree_u_wrt_t_open_u_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_u_wrt_t_open_u_wrt_t_rec : lngen.

(* end hide *)

Lemma degree_t_wrt_t_open_t_wrt_t :
forall t1 t2,
  degree_t_wrt_t 1 t1 ->
  degree_t_wrt_t 0 t2 ->
  degree_t_wrt_t 0 (open_t_wrt_t t1 t2).
Proof.
unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve degree_t_wrt_t_open_t_wrt_t : lngen.

Lemma degree_u_wrt_t_open_u_wrt_t :
forall u1 t1,
  degree_u_wrt_t 1 u1 ->
  degree_t_wrt_t 0 t1 ->
  degree_u_wrt_t 0 (open_u_wrt_t u1 t1).
Proof.
unfold open_u_wrt_t; default_simp.
Qed.

Hint Resolve degree_u_wrt_t_open_u_wrt_t : lngen.

(* begin hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_rec_inv_mutual :
(forall t1 t2 n1,
  degree_t_wrt_t n1 (open_t_wrt_t_rec n1 t2 t1) ->
  degree_t_wrt_t (S n1) t1).
Proof.
apply_mutual_ind t_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_rec_inv :
forall t1 t2 n1,
  degree_t_wrt_t n1 (open_t_wrt_t_rec n1 t2 t1) ->
  degree_t_wrt_t (S n1) t1.
Proof.
pose proof degree_t_wrt_t_open_t_wrt_t_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_t_wrt_t_open_t_wrt_t_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_open_u_wrt_t_rec_inv_mutual :
(forall u1 t1 n1,
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1) ->
  degree_u_wrt_t (S n1) u1).
Proof.
apply_mutual_ind u_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_u_wrt_t_open_u_wrt_t_rec_inv :
forall u1 t1 n1,
  degree_u_wrt_t n1 (open_u_wrt_t_rec n1 t1 u1) ->
  degree_u_wrt_t (S n1) u1.
Proof.
pose proof degree_u_wrt_t_open_u_wrt_t_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_u_wrt_t_open_u_wrt_t_rec_inv : lngen.

(* end hide *)

Lemma degree_t_wrt_t_open_t_wrt_t_inv :
forall t1 t2,
  degree_t_wrt_t 0 (open_t_wrt_t t1 t2) ->
  degree_t_wrt_t 1 t1.
Proof.
unfold open_t_wrt_t; eauto with lngen.
Qed.

Hint Immediate degree_t_wrt_t_open_t_wrt_t_inv : lngen.

Lemma degree_u_wrt_t_open_u_wrt_t_inv :
forall u1 t1,
  degree_u_wrt_t 0 (open_u_wrt_t u1 t1) ->
  degree_u_wrt_t 1 u1.
Proof.
unfold open_u_wrt_t; eauto with lngen.
Qed.

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
Proof.
apply_mutual_ind t_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_t_wrt_t_rec_inj :
forall t1 t2 a1 n1,
  close_t_wrt_t_rec n1 a1 t1 = close_t_wrt_t_rec n1 a1 t2 ->
  t1 = t2.
Proof.
pose proof close_t_wrt_t_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_t_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_t_rec_inj_mutual :
(forall u1 u2 a1 n1,
  close_u_wrt_t_rec n1 a1 u1 = close_u_wrt_t_rec n1 a1 u2 ->
  u1 = u2).
Proof.
apply_mutual_ind u_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_t_rec_inj :
forall u1 u2 a1 n1,
  close_u_wrt_t_rec n1 a1 u1 = close_u_wrt_t_rec n1 a1 u2 ->
  u1 = u2.
Proof.
pose proof close_u_wrt_t_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_u_wrt_t_rec_inj : lngen.

(* end hide *)

Lemma close_t_wrt_t_inj :
forall t1 t2 a1,
  close_t_wrt_t a1 t1 = close_t_wrt_t a1 t2 ->
  t1 = t2.
Proof.
unfold close_t_wrt_t; eauto with lngen.
Qed.

Hint Immediate close_t_wrt_t_inj : lngen.

Lemma close_u_wrt_t_inj :
forall u1 u2 a1,
  close_u_wrt_t a1 u1 = close_u_wrt_t a1 u2 ->
  u1 = u2.
Proof.
unfold close_u_wrt_t; eauto with lngen.
Qed.

Hint Immediate close_u_wrt_t_inj : lngen.

(* begin hide *)

Lemma close_t_wrt_t_rec_open_t_wrt_t_rec_mutual :
(forall t1 a1 n1,
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t_rec n1 a1 (open_t_wrt_t_rec n1 (t_var_f a1) t1) = t1).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_t_wrt_t_rec_open_t_wrt_t_rec :
forall t1 a1 n1,
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t_rec n1 a1 (open_t_wrt_t_rec n1 (t_var_f a1) t1) = t1.
Proof.
pose proof close_t_wrt_t_rec_open_t_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_t_wrt_t_rec_open_t_wrt_t_rec : lngen.
Hint Rewrite close_t_wrt_t_rec_open_t_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_t_rec_open_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t_rec n1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1) = u1).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_t_rec_open_u_wrt_t_rec :
forall u1 a1 n1,
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t_rec n1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1) = u1.
Proof.
pose proof close_u_wrt_t_rec_open_u_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_u_wrt_t_rec_open_u_wrt_t_rec : lngen.
Hint Rewrite close_u_wrt_t_rec_open_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_t_wrt_t_open_t_wrt_t :
forall t1 a1,
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t a1 (open_t_wrt_t t1 (t_var_f a1)) = t1.
Proof.
unfold close_t_wrt_t; unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve close_t_wrt_t_open_t_wrt_t : lngen.
Hint Rewrite close_t_wrt_t_open_t_wrt_t using solve [auto] : lngen.

Lemma close_u_wrt_t_open_u_wrt_t :
forall u1 a1,
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t a1 (open_u_wrt_t u1 (t_var_f a1)) = u1.
Proof.
unfold close_u_wrt_t; unfold open_u_wrt_t; default_simp.
Qed.

Hint Resolve close_u_wrt_t_open_u_wrt_t : lngen.
Hint Rewrite close_u_wrt_t_open_u_wrt_t using solve [auto] : lngen.

(* begin hide *)

Lemma open_t_wrt_t_rec_close_t_wrt_t_rec_mutual :
(forall t1 a1 n1,
  open_t_wrt_t_rec n1 (t_var_f a1) (close_t_wrt_t_rec n1 a1 t1) = t1).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_t_wrt_t_rec_close_t_wrt_t_rec :
forall t1 a1 n1,
  open_t_wrt_t_rec n1 (t_var_f a1) (close_t_wrt_t_rec n1 a1 t1) = t1.
Proof.
pose proof open_t_wrt_t_rec_close_t_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_t_wrt_t_rec_close_t_wrt_t_rec : lngen.
Hint Rewrite open_t_wrt_t_rec_close_t_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_t_rec_close_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  open_u_wrt_t_rec n1 (t_var_f a1) (close_u_wrt_t_rec n1 a1 u1) = u1).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_t_rec_close_u_wrt_t_rec :
forall u1 a1 n1,
  open_u_wrt_t_rec n1 (t_var_f a1) (close_u_wrt_t_rec n1 a1 u1) = u1.
Proof.
pose proof open_u_wrt_t_rec_close_u_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_u_wrt_t_rec_close_u_wrt_t_rec : lngen.
Hint Rewrite open_u_wrt_t_rec_close_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_t_wrt_t_close_t_wrt_t :
forall t1 a1,
  open_t_wrt_t (close_t_wrt_t a1 t1) (t_var_f a1) = t1.
Proof.
unfold close_t_wrt_t; unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve open_t_wrt_t_close_t_wrt_t : lngen.
Hint Rewrite open_t_wrt_t_close_t_wrt_t using solve [auto] : lngen.

Lemma open_u_wrt_t_close_u_wrt_t :
forall u1 a1,
  open_u_wrt_t (close_u_wrt_t a1 u1) (t_var_f a1) = u1.
Proof.
unfold close_u_wrt_t; unfold open_u_wrt_t; default_simp.
Qed.

Hint Resolve open_u_wrt_t_close_u_wrt_t : lngen.
Hint Rewrite open_u_wrt_t_close_u_wrt_t using solve [auto] : lngen.

(* begin hide *)

Lemma open_t_wrt_t_rec_inj_mutual :
(forall t2 t1 a1 n1,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t_rec n1 (t_var_f a1) t2 = open_t_wrt_t_rec n1 (t_var_f a1) t1 ->
  t2 = t1).
Proof.
apply_mutual_ind t_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_t_wrt_t_rec_inj :
forall t2 t1 a1 n1,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t_rec n1 (t_var_f a1) t2 = open_t_wrt_t_rec n1 (t_var_f a1) t1 ->
  t2 = t1.
Proof.
pose proof open_t_wrt_t_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_t_wrt_t_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_t_rec_inj_mutual :
(forall u2 u1 a1 n1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 (t_var_f a1) u2 = open_u_wrt_t_rec n1 (t_var_f a1) u1 ->
  u2 = u1).
Proof.
apply_mutual_ind u_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_t_rec_inj :
forall u2 u1 a1 n1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 (t_var_f a1) u2 = open_u_wrt_t_rec n1 (t_var_f a1) u1 ->
  u2 = u1.
Proof.
pose proof open_u_wrt_t_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_u_wrt_t_rec_inj : lngen.

(* end hide *)

Lemma open_t_wrt_t_inj :
forall t2 t1 a1,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t t2 (t_var_f a1) = open_t_wrt_t t1 (t_var_f a1) ->
  t2 = t1.
Proof.
unfold open_t_wrt_t; eauto with lngen.
Qed.

Hint Immediate open_t_wrt_t_inj : lngen.

Lemma open_u_wrt_t_inj :
forall u2 u1 a1,
  a1 `notin` tt_fv_u u2 ->
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t u2 (t_var_f a1) = open_u_wrt_t u1 (t_var_f a1) ->
  u2 = u1.
Proof.
unfold open_u_wrt_t; eauto with lngen.
Qed.

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
Proof.
apply_mutual_ind lc_t_mutind;
intros;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_t_wrt_t_of_lc_t :
forall t1,
  lc_t t1 ->
  degree_t_wrt_t 0 t1.
Proof.
pose proof degree_t_wrt_t_of_lc_t_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_t_wrt_t_of_lc_t : lngen.

(* begin hide *)

Lemma degree_u_wrt_t_of_lc_u_mutual :
(forall u1,
  lc_u u1 ->
  degree_u_wrt_t 0 u1).
Proof.
apply_mutual_ind lc_u_mutind;
intros;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_u_wrt_t_of_lc_u :
forall u1,
  lc_u u1 ->
  degree_u_wrt_t 0 u1.
Proof.
pose proof degree_u_wrt_t_of_lc_u_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_u_wrt_t_of_lc_u : lngen.

(* begin hide *)

Lemma lc_t_of_degree_size_mutual :
forall i1,
(forall t1,
  size_t t1 = i1 ->
  degree_t_wrt_t 0 t1 ->
  lc_t t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind t_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_t_of_degree :
forall t1,
  degree_t_wrt_t 0 t1 ->
  lc_t t1.
Proof.
intros t1; intros;
pose proof (lc_t_of_degree_size_mutual (size_t t1));
intuition eauto.
Qed.

Hint Resolve lc_t_of_degree : lngen.

(* begin hide *)

Lemma lc_u_of_degree_size_mutual :
forall i1,
(forall u1,
  size_u u1 = i1 ->
  degree_u_wrt_t 0 u1 ->
  lc_u u1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind u_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_u_of_degree :
forall u1,
  degree_u_wrt_t 0 u1 ->
  lc_u u1.
Proof.
intros u1; intros;
pose proof (lc_u_of_degree_size_mutual (size_u u1));
intuition eauto.
Qed.

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
              let J1 := fresh in pose proof H as J1; apply degree_u_wrt_t_of_lc_u in J1; clear H
          end).

Lemma lc_t_all_exists :
forall a1 t1,
  lc_t (open_t_wrt_t t1 (t_var_f a1)) ->
  lc_t (t_all t1).
Proof.
intros; t_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_u_tlam_exists :
forall a1 e1,
  lc_u (open_u_wrt_t e1 (t_var_f a1)) ->
  lc_u (u_tlam e1).
Proof.
intros; u_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_t (t_all _)) =>
  let a1 := fresh in
  pick_fresh a1;
  apply (lc_t_all_exists a1).

Hint Extern 1 (lc_u (u_tlam _)) =>
  let a1 := fresh in
  pick_fresh a1;
  apply (lc_u_tlam_exists a1).

Lemma lc_body_t_wrt_t :
forall t1 t2,
  body_t_wrt_t t1 ->
  lc_t t2 ->
  lc_t (open_t_wrt_t t1 t2).
Proof.
unfold body_t_wrt_t;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
t_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_t_wrt_t : lngen.

Lemma lc_body_u_wrt_t :
forall u1 t1,
  body_u_wrt_t u1 ->
  lc_t t1 ->
  lc_u (open_u_wrt_t u1 t1).
Proof.
unfold body_u_wrt_t;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
u_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_u_wrt_t : lngen.

Lemma lc_body_t_all_1 :
forall t1,
  lc_t (t_all t1) ->
  body_t_wrt_t t1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_t_all_1 : lngen.

Lemma lc_body_u_tlam_1 :
forall e1,
  lc_u (u_tlam e1) ->
  body_u_wrt_t e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_u_tlam_1 : lngen.

(* begin hide *)

Lemma lc_t_unique_mutual :
(forall t1 (proof2 proof3 : lc_t t1), proof2 = proof3).
Proof.
apply_mutual_ind lc_t_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_t_unique :
forall t1 (proof2 proof3 : lc_t t1), proof2 = proof3.
Proof.
pose proof lc_t_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_t_unique : lngen.

(* begin hide *)

Lemma lc_u_unique_mutual :
(forall u1 (proof2 proof3 : lc_u u1), proof2 = proof3).
Proof.
apply_mutual_ind lc_u_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_u_unique :
forall u1 (proof2 proof3 : lc_u u1), proof2 = proof3.
Proof.
pose proof lc_u_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_u_unique : lngen.

(* begin hide *)

Lemma lc_t_of_lc_set_t_mutual :
(forall t1, lc_set_t t1 -> lc_t t1).
Proof.
apply_mutual_ind lc_set_t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_t_of_lc_set_t :
forall t1, lc_set_t t1 -> lc_t t1.
Proof.
pose proof lc_t_of_lc_set_t_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_t_of_lc_set_t : lngen.

(* begin hide *)

Lemma lc_u_of_lc_set_u_mutual :
(forall u1, lc_set_u u1 -> lc_u u1).
Proof.
apply_mutual_ind lc_set_u_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_u_of_lc_set_u :
forall u1, lc_set_u u1 -> lc_u u1.
Proof.
pose proof lc_u_of_lc_set_u_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_u_of_lc_set_u : lngen.

(* begin hide *)

Lemma lc_set_t_of_lc_t_size_mutual :
forall i1,
(forall t1,
  size_t t1 = i1 ->
  lc_t t1 ->
  lc_set_t t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind t_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_t_of_lc_t];
default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_t_of_lc_t :
forall t1,
  lc_t t1 ->
  lc_set_t t1.
Proof.
intros t1; intros;
pose proof (lc_set_t_of_lc_t_size_mutual (size_t t1));
intuition eauto.
Qed.

Hint Resolve lc_set_t_of_lc_t : lngen.

(* begin hide *)

Lemma lc_set_u_of_lc_u_size_mutual :
forall i1,
(forall u1,
  size_u u1 = i1 ->
  lc_u u1 ->
  lc_set_u u1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind u_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_u_of_lc_u
 | apply lc_set_p_of_lc_p
 | apply lc_set_t_of_lc_t];
default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_u_of_lc_u :
forall u1,
  lc_u u1 ->
  lc_set_u u1.
Proof.
intros u1; intros;
pose proof (lc_set_u_of_lc_u_size_mutual (size_u u1));
intuition eauto.
Qed.

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
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_t_wrt_t_rec_degree_t_wrt_t :
forall t1 a1 n1,
  degree_t_wrt_t n1 t1 ->
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t_rec n1 a1 t1 = t1.
Proof.
pose proof close_t_wrt_t_rec_degree_t_wrt_t_mutual as H; intuition eauto.
Qed.

Hint Resolve close_t_wrt_t_rec_degree_t_wrt_t : lngen.
Hint Rewrite close_t_wrt_t_rec_degree_t_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_t_rec_degree_u_wrt_t_mutual :
(forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t_rec n1 a1 u1 = u1).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_u_wrt_t_rec_degree_u_wrt_t :
forall u1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t_rec n1 a1 u1 = u1.
Proof.
pose proof close_u_wrt_t_rec_degree_u_wrt_t_mutual as H; intuition eauto.
Qed.

Hint Resolve close_u_wrt_t_rec_degree_u_wrt_t : lngen.
Hint Rewrite close_u_wrt_t_rec_degree_u_wrt_t using solve [auto] : lngen.

(* end hide *)

Lemma close_t_wrt_t_lc_t :
forall t1 a1,
  lc_t t1 ->
  a1 `notin` tt_fv_t t1 ->
  close_t_wrt_t a1 t1 = t1.
Proof.
unfold close_t_wrt_t; default_simp.
Qed.

Hint Resolve close_t_wrt_t_lc_t : lngen.
Hint Rewrite close_t_wrt_t_lc_t using solve [auto] : lngen.

Lemma close_u_wrt_t_lc_u :
forall u1 a1,
  lc_u u1 ->
  a1 `notin` tt_fv_u u1 ->
  close_u_wrt_t a1 u1 = u1.
Proof.
unfold close_u_wrt_t; default_simp.
Qed.

Hint Resolve close_u_wrt_t_lc_u : lngen.
Hint Rewrite close_u_wrt_t_lc_u using solve [auto] : lngen.

(* begin hide *)

Lemma open_t_wrt_t_rec_degree_t_wrt_t_mutual :
(forall t2 t1 n1,
  degree_t_wrt_t n1 t2 ->
  open_t_wrt_t_rec n1 t1 t2 = t2).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_t_wrt_t_rec_degree_t_wrt_t :
forall t2 t1 n1,
  degree_t_wrt_t n1 t2 ->
  open_t_wrt_t_rec n1 t1 t2 = t2.
Proof.
pose proof open_t_wrt_t_rec_degree_t_wrt_t_mutual as H; intuition eauto.
Qed.

Hint Resolve open_t_wrt_t_rec_degree_t_wrt_t : lngen.
Hint Rewrite open_t_wrt_t_rec_degree_t_wrt_t using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_t_rec_degree_u_wrt_t_mutual :
(forall u1 t1 n1,
  degree_u_wrt_t n1 u1 ->
  open_u_wrt_t_rec n1 t1 u1 = u1).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_u_wrt_t_rec_degree_u_wrt_t :
forall u1 t1 n1,
  degree_u_wrt_t n1 u1 ->
  open_u_wrt_t_rec n1 t1 u1 = u1.
Proof.
pose proof open_u_wrt_t_rec_degree_u_wrt_t_mutual as H; intuition eauto.
Qed.

Hint Resolve open_u_wrt_t_rec_degree_u_wrt_t : lngen.
Hint Rewrite open_u_wrt_t_rec_degree_u_wrt_t using solve [auto] : lngen.

(* end hide *)

Lemma open_t_wrt_t_lc_t :
forall t2 t1,
  lc_t t2 ->
  open_t_wrt_t t2 t1 = t2.
Proof.
unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve open_t_wrt_t_lc_t : lngen.
Hint Rewrite open_t_wrt_t_lc_t using solve [auto] : lngen.

Lemma open_u_wrt_t_lc_u :
forall u1 t1,
  lc_u u1 ->
  open_u_wrt_t u1 t1 = u1.
Proof.
unfold open_u_wrt_t; default_simp.
Qed.

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
Proof.
apply_mutual_ind t_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tt_fv_t_close_t_wrt_t_rec :
forall t1 a1 n1,
  tt_fv_t (close_t_wrt_t_rec n1 a1 t1) [=] remove a1 (tt_fv_t t1).
Proof.
pose proof tt_fv_t_close_t_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_t_close_t_wrt_t_rec : lngen.
Hint Rewrite tt_fv_t_close_t_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_close_u_wrt_t_rec_mutual :
(forall u1 a1 n1,
  tt_fv_u (close_u_wrt_t_rec n1 a1 u1) [=] remove a1 (tt_fv_u u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_close_u_wrt_t_rec :
forall u1 a1 n1,
  tt_fv_u (close_u_wrt_t_rec n1 a1 u1) [=] remove a1 (tt_fv_u u1).
Proof.
pose proof tt_fv_u_close_u_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_u_close_u_wrt_t_rec : lngen.
Hint Rewrite tt_fv_u_close_u_wrt_t_rec using solve [auto] : lngen.

(* end hide *)

Lemma tt_fv_t_close_t_wrt_t :
forall t1 a1,
  tt_fv_t (close_t_wrt_t a1 t1) [=] remove a1 (tt_fv_t t1).
Proof.
unfold close_t_wrt_t; default_simp.
Qed.

Hint Resolve tt_fv_t_close_t_wrt_t : lngen.
Hint Rewrite tt_fv_t_close_t_wrt_t using solve [auto] : lngen.

Lemma tt_fv_u_close_u_wrt_t :
forall u1 a1,
  tt_fv_u (close_u_wrt_t a1 u1) [=] remove a1 (tt_fv_u u1).
Proof.
unfold close_u_wrt_t; default_simp.
Qed.

Hint Resolve tt_fv_u_close_u_wrt_t : lngen.
Hint Rewrite tt_fv_u_close_u_wrt_t using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_t_open_t_wrt_t_rec_lower_mutual :
(forall t1 t2 n1,
  tt_fv_t t1 [<=] tt_fv_t (open_t_wrt_t_rec n1 t2 t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tt_fv_t_open_t_wrt_t_rec_lower :
forall t1 t2 n1,
  tt_fv_t t1 [<=] tt_fv_t (open_t_wrt_t_rec n1 t2 t1).
Proof.
pose proof tt_fv_t_open_t_wrt_t_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_t_open_t_wrt_t_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_t_rec_lower_mutual :
(forall u1 t1 n1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_t_rec n1 t1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_t_rec_lower :
forall u1 t1 n1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_t_rec n1 t1 u1).
Proof.
pose proof tt_fv_u_open_u_wrt_t_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_u_open_u_wrt_t_rec_lower : lngen.

(* end hide *)

Lemma tt_fv_t_open_t_wrt_t_lower :
forall t1 t2,
  tt_fv_t t1 [<=] tt_fv_t (open_t_wrt_t t1 t2).
Proof.
unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve tt_fv_t_open_t_wrt_t_lower : lngen.

Lemma tt_fv_u_open_u_wrt_t_lower :
forall u1 t1,
  tt_fv_u u1 [<=] tt_fv_u (open_u_wrt_t u1 t1).
Proof.
unfold open_u_wrt_t; default_simp.
Qed.

Hint Resolve tt_fv_u_open_u_wrt_t_lower : lngen.

(* begin hide *)

Lemma tt_fv_t_open_t_wrt_t_rec_upper_mutual :
(forall t1 t2 n1,
  tt_fv_t (open_t_wrt_t_rec n1 t2 t1) [<=] tt_fv_t t2 `union` tt_fv_t t1).
Proof.
apply_mutual_ind t_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tt_fv_t_open_t_wrt_t_rec_upper :
forall t1 t2 n1,
  tt_fv_t (open_t_wrt_t_rec n1 t2 t1) [<=] tt_fv_t t2 `union` tt_fv_t t1.
Proof.
pose proof tt_fv_t_open_t_wrt_t_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_t_open_t_wrt_t_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_t_rec_upper_mutual :
(forall u1 t1 n1,
  tt_fv_u (open_u_wrt_t_rec n1 t1 u1) [<=] tt_fv_t t1 `union` tt_fv_u u1).
Proof.
apply_mutual_ind u_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tt_fv_u_open_u_wrt_t_rec_upper :
forall u1 t1 n1,
  tt_fv_u (open_u_wrt_t_rec n1 t1 u1) [<=] tt_fv_t t1 `union` tt_fv_u u1.
Proof.
pose proof tt_fv_u_open_u_wrt_t_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_u_open_u_wrt_t_rec_upper : lngen.

(* end hide *)

Lemma tt_fv_t_open_t_wrt_t_upper :
forall t1 t2,
  tt_fv_t (open_t_wrt_t t1 t2) [<=] tt_fv_t t2 `union` tt_fv_t t1.
Proof.
unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve tt_fv_t_open_t_wrt_t_upper : lngen.

Lemma tt_fv_u_open_u_wrt_t_upper :
forall u1 t1,
  tt_fv_u (open_u_wrt_t u1 t1) [<=] tt_fv_t t1 `union` tt_fv_u u1.
Proof.
unfold open_u_wrt_t; default_simp.
Qed.

Hint Resolve tt_fv_u_open_u_wrt_t_upper : lngen.

(* begin hide *)

Lemma tt_fv_t_t_subst_t_fresh_mutual :
(forall t1 t2 a1,
  a1 `notin` tt_fv_t t1 ->
  tt_fv_t (t_subst_t t2 a1 t1) [=] tt_fv_t t1).
Proof.
apply_mutual_ind t_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tt_fv_t_t_subst_t_fresh :
forall t1 t2 a1,
  a1 `notin` tt_fv_t t1 ->
  tt_fv_t (t_subst_t t2 a1 t1) [=] tt_fv_t t1.
Proof.
pose proof tt_fv_t_t_subst_t_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_t_t_subst_t_fresh : lngen.
Hint Rewrite tt_fv_t_t_subst_t_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_u_t_subst_u_fresh_mutual :
(forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  tt_fv_u (t_subst_u t1 a1 u1) [=] tt_fv_u u1).
Proof.
apply_mutual_ind u_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tt_fv_u_t_subst_u_fresh :
forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  tt_fv_u (t_subst_u t1 a1 u1) [=] tt_fv_u u1.
Proof.
pose proof tt_fv_u_t_subst_u_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_u_t_subst_u_fresh : lngen.
Hint Rewrite tt_fv_u_t_subst_u_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tt_fv_t_t_subst_t_lower_mutual :
(forall t1 t2 a1,
  remove a1 (tt_fv_t t1) [<=] tt_fv_t (t_subst_t t2 a1 t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tt_fv_t_t_subst_t_lower :
forall t1 t2 a1,
  remove a1 (tt_fv_t t1) [<=] tt_fv_t (t_subst_t t2 a1 t1).
Proof.
pose proof tt_fv_t_t_subst_t_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_t_t_subst_t_lower : lngen.

(* begin hide *)

Lemma tt_fv_u_t_subst_u_lower_mutual :
(forall u1 t1 a1,
  remove a1 (tt_fv_u u1) [<=] tt_fv_u (t_subst_u t1 a1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tt_fv_u_t_subst_u_lower :
forall u1 t1 a1,
  remove a1 (tt_fv_u u1) [<=] tt_fv_u (t_subst_u t1 a1 u1).
Proof.
pose proof tt_fv_u_t_subst_u_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_u_t_subst_u_lower : lngen.

(* begin hide *)

Lemma tt_fv_t_t_subst_t_notin_mutual :
(forall t1 t2 a1 a2,
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t (t_subst_t t2 a1 t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tt_fv_t_t_subst_t_notin :
forall t1 t2 a1 a2,
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t (t_subst_t t2 a1 t1).
Proof.
pose proof tt_fv_t_t_subst_t_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_t_t_subst_t_notin : lngen.

(* begin hide *)

Lemma tt_fv_u_t_subst_u_notin_mutual :
(forall u1 t1 a1 a2,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_u (t_subst_u t1 a1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tt_fv_u_t_subst_u_notin :
forall u1 t1 a1 a2,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 `notin` tt_fv_u (t_subst_u t1 a1 u1).
Proof.
pose proof tt_fv_u_t_subst_u_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_u_t_subst_u_notin : lngen.

(* begin hide *)

Lemma tt_fv_t_t_subst_t_upper_mutual :
(forall t1 t2 a1,
  tt_fv_t (t_subst_t t2 a1 t1) [<=] tt_fv_t t2 `union` remove a1 (tt_fv_t t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tt_fv_t_t_subst_t_upper :
forall t1 t2 a1,
  tt_fv_t (t_subst_t t2 a1 t1) [<=] tt_fv_t t2 `union` remove a1 (tt_fv_t t1).
Proof.
pose proof tt_fv_t_t_subst_t_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve tt_fv_t_t_subst_t_upper : lngen.

(* begin hide *)

Lemma tt_fv_u_t_subst_u_upper_mutual :
(forall u1 t1 a1,
  tt_fv_u (t_subst_u t1 a1 u1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_u u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tt_fv_u_t_subst_u_upper :
forall u1 t1 a1,
  tt_fv_u (t_subst_u t1 a1 u1) [<=] tt_fv_t t1 `union` remove a1 (tt_fv_u u1).
Proof.
pose proof tt_fv_u_t_subst_u_upper_mutual as H; intuition eauto.
Qed.

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
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_t_close_t_wrt_t_rec :
forall t2 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_t t1 a1 (close_t_wrt_t_rec n1 a2 t2) = close_t_wrt_t_rec n1 a2 (t_subst_t t1 a1 t2).
Proof.
pose proof t_subst_t_close_t_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_t_close_t_wrt_t_rec : lngen.

(* begin hide *)

Lemma t_subst_u_close_u_wrt_t_rec_mutual :
(forall u1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_u t1 a1 (close_u_wrt_t_rec n1 a2 u1) = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_u_close_u_wrt_t_rec :
forall u1 t1 a1 a2 n1,
  degree_t_wrt_t n1 t1 ->
  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_u t1 a1 (close_u_wrt_t_rec n1 a2 u1) = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 u1).
Proof.
pose proof t_subst_u_close_u_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_u_close_u_wrt_t_rec : lngen.

Lemma t_subst_t_close_t_wrt_t :
forall t2 t1 a1 a2,
  lc_t t1 ->  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_t t1 a1 (close_t_wrt_t a2 t2) = close_t_wrt_t a2 (t_subst_t t1 a1 t2).
Proof.
unfold close_t_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_t_close_t_wrt_t : lngen.

Lemma t_subst_u_close_u_wrt_t :
forall u1 t1 a1 a2,
  lc_t t1 ->  a1 <> a2 ->
  a2 `notin` tt_fv_t t1 ->
  t_subst_u t1 a1 (close_u_wrt_t a2 u1) = close_u_wrt_t a2 (t_subst_u t1 a1 u1).
Proof.
unfold close_u_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_u_close_u_wrt_t : lngen.

(* begin hide *)

Lemma t_subst_t_degree_t_wrt_t_mutual :
(forall t1 t2 a1 n1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t n1 t2 ->
  degree_t_wrt_t n1 (t_subst_t t2 a1 t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_t_degree_t_wrt_t :
forall t1 t2 a1 n1,
  degree_t_wrt_t n1 t1 ->
  degree_t_wrt_t n1 t2 ->
  degree_t_wrt_t n1 (t_subst_t t2 a1 t1).
Proof.
pose proof t_subst_t_degree_t_wrt_t_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_t_degree_t_wrt_t : lngen.

(* begin hide *)

Lemma t_subst_u_degree_u_wrt_t_mutual :
(forall u1 t1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (t_subst_u t1 a1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_u_degree_u_wrt_t :
forall u1 t1 a1 n1,
  degree_u_wrt_t n1 u1 ->
  degree_t_wrt_t n1 t1 ->
  degree_u_wrt_t n1 (t_subst_u t1 a1 u1).
Proof.
pose proof t_subst_u_degree_u_wrt_t_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_u_degree_u_wrt_t : lngen.

(* begin hide *)

Lemma t_subst_t_fresh_eq_mutual :
(forall t2 t1 a1,
  a1 `notin` tt_fv_t t2 ->
  t_subst_t t1 a1 t2 = t2).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_t_fresh_eq :
forall t2 t1 a1,
  a1 `notin` tt_fv_t t2 ->
  t_subst_t t1 a1 t2 = t2.
Proof.
pose proof t_subst_t_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_t_fresh_eq : lngen.
Hint Rewrite t_subst_t_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_u_fresh_eq_mutual :
(forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  t_subst_u t1 a1 u1 = u1).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_u_fresh_eq :
forall u1 t1 a1,
  a1 `notin` tt_fv_u u1 ->
  t_subst_u t1 a1 u1 = u1.
Proof.
pose proof t_subst_u_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_u_fresh_eq : lngen.
Hint Rewrite t_subst_u_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_t_fresh_same_mutual :
(forall t2 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_t (t_subst_t t1 a1 t2)).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_t_fresh_same :
forall t2 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_t (t_subst_t t1 a1 t2).
Proof.
pose proof t_subst_t_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_t_fresh_same : lngen.

(* begin hide *)

Lemma t_subst_u_fresh_same_mutual :
(forall u1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_u_fresh_same :
forall u1 t1 a1,
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a1 u1).
Proof.
pose proof t_subst_u_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_u_fresh_same : lngen.

(* begin hide *)

Lemma t_subst_t_fresh_mutual :
(forall t2 t1 a1 a2,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_t (t_subst_t t1 a2 t2)).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_t_fresh :
forall t2 t1 a1 a2,
  a1 `notin` tt_fv_t t2 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_t (t_subst_t t1 a2 t2).
Proof.
pose proof t_subst_t_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_t_fresh : lngen.

(* begin hide *)

Lemma t_subst_u_fresh_mutual :
(forall u1 t1 a1 a2,
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a2 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_u_fresh :
forall u1 t1 a1 a2,
  a1 `notin` tt_fv_u u1 ->
  a1 `notin` tt_fv_t t1 ->
  a1 `notin` tt_fv_u (t_subst_u t1 a2 u1).
Proof.
pose proof t_subst_u_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_u_fresh : lngen.

Lemma t_subst_t_lc_t :
forall t1 t2 a1,
  lc_t t1 ->
  lc_t t2 ->
  lc_t (t_subst_t t2 a1 t1).
Proof.
default_simp.
Qed.

Hint Resolve t_subst_t_lc_t : lngen.

Lemma t_subst_u_lc_u :
forall u1 t1 a1,
  lc_u u1 ->
  lc_t t1 ->
  lc_u (t_subst_u t1 a1 u1).
Proof.
default_simp.
Qed.

Hint Resolve t_subst_u_lc_u : lngen.

(* begin hide *)

Lemma t_subst_t_open_t_wrt_t_rec_mutual :
(forall t3 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_t t1 a1 (open_t_wrt_t_rec n1 t2 t3) = open_t_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_t t1 a1 t3)).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma t_subst_t_open_t_wrt_t_rec :
forall t3 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_t t1 a1 (open_t_wrt_t_rec n1 t2 t3) = open_t_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_t t1 a1 t3).
Proof.
pose proof t_subst_t_open_t_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_t_open_t_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_open_u_wrt_t_rec_mutual :
(forall u1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_u t1 a1 (open_u_wrt_t_rec n1 t2 u1) = open_u_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_u t1 a1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_open_u_wrt_t_rec :
forall u1 t1 t2 a1 n1,
  lc_t t1 ->
  t_subst_u t1 a1 (open_u_wrt_t_rec n1 t2 u1) = open_u_wrt_t_rec n1 (t_subst_t t1 a1 t2) (t_subst_u t1 a1 u1).
Proof.
pose proof t_subst_u_open_u_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_u_open_u_wrt_t_rec : lngen.

(* end hide *)

Lemma t_subst_t_open_t_wrt_t :
forall t3 t1 t2 a1,
  lc_t t1 ->
  t_subst_t t1 a1 (open_t_wrt_t t3 t2) = open_t_wrt_t (t_subst_t t1 a1 t3) (t_subst_t t1 a1 t2).
Proof.
unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_t_open_t_wrt_t : lngen.

Lemma t_subst_u_open_u_wrt_t :
forall u1 t1 t2 a1,
  lc_t t1 ->
  t_subst_u t1 a1 (open_u_wrt_t u1 t2) = open_u_wrt_t (t_subst_u t1 a1 u1) (t_subst_t t1 a1 t2).
Proof.
unfold open_u_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_u_open_u_wrt_t : lngen.

Lemma t_subst_t_open_t_wrt_t_var :
forall t2 t1 a1 a2,
  a1 <> a2 ->
  lc_t t1 ->
  open_t_wrt_t (t_subst_t t1 a1 t2) (t_var_f a2) = t_subst_t t1 a1 (open_t_wrt_t t2 (t_var_f a2)).
Proof.
intros; rewrite t_subst_t_open_t_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_t_open_t_wrt_t_var : lngen.

Lemma t_subst_u_open_u_wrt_t_var :
forall u1 t1 a1 a2,
  a1 <> a2 ->
  lc_t t1 ->
  open_u_wrt_t (t_subst_u t1 a1 u1) (t_var_f a2) = t_subst_u t1 a1 (open_u_wrt_t u1 (t_var_f a2)).
Proof.
intros; rewrite t_subst_u_open_u_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_u_open_u_wrt_t_var : lngen.

(* begin hide *)

Lemma t_subst_t_spec_rec_mutual :
(forall t1 t2 a1 n1,
  t_subst_t t2 a1 t1 = open_t_wrt_t_rec n1 t2 (close_t_wrt_t_rec n1 a1 t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma t_subst_t_spec_rec :
forall t1 t2 a1 n1,
  t_subst_t t2 a1 t1 = open_t_wrt_t_rec n1 t2 (close_t_wrt_t_rec n1 a1 t1).
Proof.
pose proof t_subst_t_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_t_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_spec_rec_mutual :
(forall u1 t1 a1 n1,
  t_subst_u t1 a1 u1 = open_u_wrt_t_rec n1 t1 (close_u_wrt_t_rec n1 a1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_spec_rec :
forall u1 t1 a1 n1,
  t_subst_u t1 a1 u1 = open_u_wrt_t_rec n1 t1 (close_u_wrt_t_rec n1 a1 u1).
Proof.
pose proof t_subst_u_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_u_spec_rec : lngen.

(* end hide *)

Lemma t_subst_t_spec :
forall t1 t2 a1,
  t_subst_t t2 a1 t1 = open_t_wrt_t (close_t_wrt_t a1 t1) t2.
Proof.
unfold close_t_wrt_t; unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_t_spec : lngen.

Lemma t_subst_u_spec :
forall u1 t1 a1,
  t_subst_u t1 a1 u1 = open_u_wrt_t (close_u_wrt_t a1 u1) t1.
Proof.
unfold close_u_wrt_t; unfold open_u_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_u_spec : lngen.

(* begin hide *)

Lemma t_subst_t_t_subst_t_mutual :
(forall t1 t2 t3 a2 a1,
  a2 `notin` tt_fv_t t2 ->
  a2 <> a1 ->
  t_subst_t t2 a1 (t_subst_t t3 a2 t1) = t_subst_t (t_subst_t t2 a1 t3) a2 (t_subst_t t2 a1 t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_t_t_subst_t :
forall t1 t2 t3 a2 a1,
  a2 `notin` tt_fv_t t2 ->
  a2 <> a1 ->
  t_subst_t t2 a1 (t_subst_t t3 a2 t1) = t_subst_t (t_subst_t t2 a1 t3) a2 (t_subst_t t2 a1 t1).
Proof.
pose proof t_subst_t_t_subst_t_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_t_t_subst_t : lngen.

(* begin hide *)

Lemma t_subst_u_t_subst_u_mutual :
(forall u1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_u t1 a1 (t_subst_u t2 a2 u1) = t_subst_u (t_subst_t t1 a1 t2) a2 (t_subst_u t1 a1 u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_u_t_subst_u :
forall u1 t1 t2 a2 a1,
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  t_subst_u t1 a1 (t_subst_u t2 a2 u1) = t_subst_u (t_subst_t t1 a1 t2) a2 (t_subst_u t1 a1 u1).
Proof.
pose proof t_subst_u_t_subst_u_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_u_t_subst_u : lngen.

(* begin hide *)

Lemma t_subst_t_close_t_wrt_t_rec_open_t_wrt_t_rec_mutual :
(forall t2 t1 a1 a2 n1,
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_t t1 a1 t2 = close_t_wrt_t_rec n1 a2 (t_subst_t t1 a1 (open_t_wrt_t_rec n1 (t_var_f a2) t2))).
Proof.
apply_mutual_ind t_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma t_subst_t_close_t_wrt_t_rec_open_t_wrt_t_rec :
forall t2 t1 a1 a2 n1,
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_t t1 a1 t2 = close_t_wrt_t_rec n1 a2 (t_subst_t t1 a1 (open_t_wrt_t_rec n1 (t_var_f a2) t2)).
Proof.
pose proof t_subst_t_close_t_wrt_t_rec_open_t_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_t_close_t_wrt_t_rec_open_t_wrt_t_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec_mutual :
(forall u1 t1 a1 a2 n1,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a2) u1))).
Proof.
apply_mutual_ind u_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma t_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec :
forall u1 t1 a1 a2 n1,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  degree_t_wrt_t n1 t1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_t_rec n1 a2 (t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a2) u1)).
Proof.
pose proof t_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_u_close_u_wrt_t_rec_open_u_wrt_t_rec : lngen.

(* end hide *)

Lemma t_subst_t_close_t_wrt_t_open_t_wrt_t :
forall t2 t1 a1 a2,
  a2 `notin` tt_fv_t t2 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  lc_t t1 ->
  t_subst_t t1 a1 t2 = close_t_wrt_t a2 (t_subst_t t1 a1 (open_t_wrt_t t2 (t_var_f a2))).
Proof.
unfold close_t_wrt_t; unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_t_close_t_wrt_t_open_t_wrt_t : lngen.

Lemma t_subst_u_close_u_wrt_t_open_u_wrt_t :
forall u1 t1 a1 a2,
  a2 `notin` tt_fv_u u1 ->
  a2 `notin` tt_fv_t t1 ->
  a2 <> a1 ->
  lc_t t1 ->
  t_subst_u t1 a1 u1 = close_u_wrt_t a2 (t_subst_u t1 a1 (open_u_wrt_t u1 (t_var_f a2))).
Proof.
unfold close_u_wrt_t; unfold open_u_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_u_close_u_wrt_t_open_u_wrt_t : lngen.

Lemma t_subst_t_t_all :
forall a2 t2 t1 a1,
  lc_t t1 ->
  a2 `notin` tt_fv_t t1 `union` tt_fv_t t2 `union` singleton a1 ->
  t_subst_t t1 a1 (t_all t2) = t_all (close_t_wrt_t a2 (t_subst_t t1 a1 (open_t_wrt_t t2 (t_var_f a2)))).
Proof.
default_simp.
Qed.

Hint Resolve t_subst_t_t_all : lngen.

Lemma t_subst_u_u_tlam :
forall a2 e1 t1 a1,
  lc_t t1 ->
  a2 `notin` tt_fv_t t1 `union` tt_fv_u e1 `union` singleton a1 ->
  t_subst_u t1 a1 (u_tlam e1) = u_tlam (close_u_wrt_t a2 (t_subst_u t1 a1 (open_u_wrt_t e1 (t_var_f a2)))).
Proof.
default_simp.
Qed.

Hint Resolve t_subst_u_u_tlam : lngen.

(* begin hide *)

Lemma t_subst_t_intro_rec_mutual :
(forall t1 a1 t2 n1,
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t_rec n1 t2 t1 = t_subst_t t2 a1 (open_t_wrt_t_rec n1 (t_var_f a1) t1)).
Proof.
apply_mutual_ind t_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_t_intro_rec :
forall t1 a1 t2 n1,
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t_rec n1 t2 t1 = t_subst_t t2 a1 (open_t_wrt_t_rec n1 (t_var_f a1) t1).
Proof.
pose proof t_subst_t_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_t_intro_rec : lngen.
Hint Rewrite t_subst_t_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma t_subst_u_intro_rec_mutual :
(forall u1 a1 t1 n1,
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 t1 u1 = t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1)).
Proof.
apply_mutual_ind u_mutind;
default_simp.
Qed.

(* end hide *)

Lemma t_subst_u_intro_rec :
forall u1 a1 t1 n1,
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t_rec n1 t1 u1 = t_subst_u t1 a1 (open_u_wrt_t_rec n1 (t_var_f a1) u1).
Proof.
pose proof t_subst_u_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve t_subst_u_intro_rec : lngen.
Hint Rewrite t_subst_u_intro_rec using solve [auto] : lngen.

Lemma t_subst_t_intro :
forall a1 t1 t2,
  a1 `notin` tt_fv_t t1 ->
  open_t_wrt_t t1 t2 = t_subst_t t2 a1 (open_t_wrt_t t1 (t_var_f a1)).
Proof.
unfold open_t_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_t_intro : lngen.

Lemma t_subst_u_intro :
forall a1 u1 t1,
  a1 `notin` tt_fv_u u1 ->
  open_u_wrt_t u1 t1 = t_subst_u t1 a1 (open_u_wrt_t u1 (t_var_f a1)).
Proof.
unfold open_u_wrt_t; default_simp.
Qed.

Hint Resolve t_subst_u_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
