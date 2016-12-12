Require Export k_ott.
Require Export k_inf.

Fixpoint ktype ty :=
  match ty with
  | t_int => t_int
  | t_arr t1 t2 => t_arr t1 (t_arr (ktype t2) t_void)
  | t_void => t_void
  end.

Definition kcont ty :=
  t_arr (ktype ty) t_void.

Inductive kexp : e -> e -> e -> Prop :=
| exp_var : forall y ty k,
    kexp (e_ann (u_var_f y) ty) k
         (e_ann (u_app k (e_ann (u_var_f y)
                                (ktype ty)))
                t_void)
| exp_int : forall n ty k,
    kexp (e_ann (u_int n) ty) k
         (e_ann (u_app k (e_ann (u_int n)
                                (ktype ty)))
                t_void)
| exp_lam : forall ut t1 e2 u2 t2 x1 c1 e' k,
    ut = u_lam t1 e2 ->
    e2 = (e_ann u2 t2) ->
    x1 `notin` (fv_u ut) ->
    c1 `notin` (fv_u ut) ->
    (forall k',
        let xt := u_var_f x1 in
        let ct := u_var_f c1 in
        kexp (open_e_wrt_u (open_e_wrt_u e2 xt) ct) k' (open_e_wrt_u (open_e_wrt_u e' xt) ct)) ->
    kexp (e_ann ut (t_arr t1 t2)) k
         (e_ann (u_app k
                       (e_ann
                          (u_lam (ktype t1)
                                 (e_ann (u_lam (kcont t2)
                                               (e_ann (u_app e'
                                                             (e_ann (u_var_b 0)
                                                                    (kcont t2)))
                                                      t_void))
                                        (kcont t2)))
                          (kcont (t_arr t1 t2))))
                t_void)
.