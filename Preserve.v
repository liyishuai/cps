Require Import Translate.

Theorem preserve : forall Gamma e0 t0, Gamma = nil -> T_ant Gamma e0 t0 -> K_ant Gamma (kp e0) t_void.
Proof.
  intros Gamma e0 t0 Hnil Ht.
  remember Hnil as Hnil'.
  inversion Ht.
  induction H; subst.
  - fsetdec.
  - repeat econstructor.
  - destruct e5.
Abort.

Theorem preservation : forall Gamma et ty pk,
    Gamma = nil ->
    T_ant Gamma et ty ->
    kprog et pk ->
    K_ant Gamma pk t_void.
Proof.
  intros Gamma et ty pk Hnil Ht.
  remember Gamma as Gm.
  inversion Ht; subst.
  induction H; subst.
  - fsetdec.
  - intros.
    inversion H; subst.
    inversion H0; subst.
Abort.
