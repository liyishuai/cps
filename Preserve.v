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