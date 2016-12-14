Require Import k_ott.
Require Import k_inf.
Require Import Translate.

Theorem lc_exp :
  forall ef,
    lc_e ef ->
    forall k ek,
      lc_e k ->
      kexp ef k ek ->
      lc_e ek.
Proof.
  intros ef Hlcf.
  induction Hlcf; intros k ek Hlck Hexp; inversion Hexp; subst; auto.
  - constructor.
    constructor.
    + assumption.
    + 
Abort.