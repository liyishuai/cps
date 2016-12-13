Require Export k_ott.
Require Export k_inf.

Reserved Notation "'kcont' ty" (at level 75).

Fixpoint ktype ty :=
  match ty with
  | t_int => t_int
  | t_arr t1 t2 => t_arr t1 (t_arr (kcont t2) t_void)
  | t_void => t_void
  end

where "'kcont' ty" := (t_arr (ktype ty) t_void).

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
        let xt := u_var_f x1 in
        let ct := u_var_f c1 in
        kexp (open_e_wrt_u e2 xt) (e_ann ct (kcont t2)) (open_e_wrt_u (open_e_wrt_u e' xt) ct) ->
    kexp (e_ann ut (t_arr t1 t2)) k
         (e_ann (u_app k
                       (e_ann
                          (u_lam (ktype t1)
                                 (e_ann (u_lam (kcont t2)
                                               (open_e_wrt_u e' (u_var_b 0)))
                                        (kcont t2)))
                          (kcont (t_arr t1 t2))))
                t_void)
| exp_app : forall e1 e1' u1 t1 e2 e2' u2 t2 c1 c2 ty k,
    e1 = e_ann u1 t1 ->
    e2 = e_ann u2 t2 ->
    c1 `notin` (fv_e e1) ->
    c2 `notin` (fv_e e2) ->
    let ct := u_var_f c1 in
    kexp e1 (e_ann ct (kcont t1)) (open_e_wrt_u e1' ct) ->
    let ct := u_var_f c2 in
    kexp e2 (e_ann ct (kcont t2)) (open_e_wrt_u e2' ct) ->
    kexp (e_ann (u_app e1 e2) ty) k
         (open_e_wrt_u e1'
                       (u_lam (ktype t1)
                              (open_e_wrt_u e2'
                                            (u_lam (ktype t2)
                                                   (e_ann (u_app (e_ann (u_app (e_ann (u_var_b 1)
                                                                                      (ktype t1))
                                                                               (e_ann (u_var_b 0)
                                                                                      (ktype t2)))
                                                                        (t_arr (kcont t2) t_void)) k)
                                                          t_void)))))
| exp_prim : forall e1 e1' e2 e2' c1 c2 p ty k,
    c1 `notin` (fv_e e1) ->
    c2 `notin` (fv_e e2) ->
    let ct := u_var_f c1 in
    kexp e1 (e_ann ct (kcont t_int)) (open_e_wrt_u e1' ct) ->
    let ct := u_var_f c2 in
    kexp e2 (e_ann ct (kcont t_int)) (open_e_wrt_u e2' ct) ->
    kexp (e_ann (u_prim e1 p e2) ty) k
         (open_e_wrt_u e1'
                       (u_lam t_int
                              (open_e_wrt_u e2'
                                            (u_lam t_int
                                                   (e_ann (u_let (e_ann (u_prim (e_ann (u_var_b 2) t_int) p
                                                                                (e_ann (u_var_b 1) t_int))
                                                                        t_int)
                                                                 (u_app k (e_ann (u_var_b 0) t_int)))
                                                          t_void)))))
.