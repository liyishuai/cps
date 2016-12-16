Require Import Translate.

Theorem lc_exp :
  forall ef,
    lc_e ef ->
    forall k ek,
      lc_e k ->
      kexp ef k ek ->
      lc_e ek.
Proof.
  destruct ef.
  induction u5; intros Hlcf k ek Hlck Hexp.
  - inversion Hexp; subst.
    inversion H1.
  - inversion Hexp; subst; repeat constructor; auto.
    inversion H1.
  - inversion Hexp; subst; repeat constructor; auto.
    inversion H1.
  - inversion Hexp; subst.
    inversion H1; subst.
    constructor.
    constructor; auto.
    constructor.
    constructor.
    intros x1.
    apply lc_e_of_degree.
    apply degree_e_wrt_u_open_e_wrt_u; auto.
    constructor.
    constructor.
    rewrite open_e_wrt_u_lc_e; auto.
    apply degree_e_wrt_u_O.
    apply degree_e_wrt_u_of_lc_e; auto.
  -
Abort.