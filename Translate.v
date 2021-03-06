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
| exp_lam : forall ut t1 e2 u2 t2 e' ty k,
    ut = u_lam t1 e2 ->
    e2 = (e_ann u2 t2) ->
    (forall x1 c1, x1 `notin` (fv_u ut) ->
    c1 `notin` (fv_u ut) ->
        let xt := u_var_f x1 in
        let ct := u_var_f c1 in
        kexp (open_e_wrt_u e2 xt) (e_ann ct (kcont t2)) (open_e_wrt_u (open_e_wrt_u e' xt) ct)) ->
    (forall xt ct,
       lc_u xt ->
       lc_u ct ->
       lc_e (open_e_wrt_u (open_e_wrt_u e' xt) ct)) ->
    kexp (e_ann ut ty) k
         (e_ann (u_app k
                       (e_ann
                          (u_lam (ktype t1)
                                 (e_ann (u_lam (kcont t2)
                                               e')
                                        (t_arr (kcont t2) t_void)))
                          (kcont ty)))
                t_void)
| exp_app : forall e1 e1' u1 t1 e2 e2' u2 t2 ty k,
    e1 = e_ann u1 t1 ->
    e2 = e_ann u2 t2 ->
    (forall c1, c1 `notin` (fv_e e1) ->
    let ct := u_var_f c1 in
    kexp e1 (e_ann ct (kcont t1)) (open_e_wrt_u e1' ct)) ->
    (forall c2, c2 `notin` (fv_e e2) ->
    let ct := u_var_f c2 in
    kexp e2 (e_ann ct (kcont t2)) (open_e_wrt_u e2' ct)) ->
    (forall ct,
       lc_u ct ->
       lc_e (open_e_wrt_u e1' ct)) ->
    (forall ct,
       lc_u ct ->
       lc_e (open_e_wrt_u e2' ct)) ->
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
| exp_prim : forall e1 e1' e2 e2' p ty k,
    (forall c1, c1 `notin` (fv_e e1) ->
    let ct := u_var_f c1 in
    kexp e1 (e_ann ct (kcont t_int)) (open_e_wrt_u e1' ct)) ->
    (forall c2, c2 `notin` (fv_e e2) ->
    let ct := u_var_f c2 in
    kexp e2 (e_ann ct (kcont t_int)) (open_e_wrt_u e2' ct)) ->
    (forall ct,
       lc_u ct ->
       lc_e (open_e_wrt_u e1' ct)) ->
    (forall ct,
       lc_u ct ->
       lc_e (open_e_wrt_u e2' ct)) ->
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
| exp_if0 : forall e1 e1' e2 e2' e3 e3' ty k,
    (forall c1, c1 `notin` (fv_e e1) ->
    let ct := u_var_f c1 in
    kexp e1 (e_ann ct (kcont t_int)) (open_e_wrt_u e1' ct)) ->
    kexp e2 k e2' ->
    kexp e3 k e3' ->
    (forall ct,
       lc_u ct ->
       lc_e (open_e_wrt_u e1' ct)) ->
    lc_e e2' ->
    lc_e e3' ->
    kexp (e_ann (u_if0 e1 e2 e3) ty) k
         (open_e_wrt_u e1'
                       (u_lam t_int
                              (e_ann (u_if0 (e_ann (u_var_b 0) t_int)
                                            e2'
                                            e3')
                                     t_void)))
.

Inductive kprog : e -> e -> Prop :=
| prog_halt:
    forall e1 u1 ty e',
    e1 = e_ann u1 ty ->
    (forall c1,
        c1 `notin` (fv_e e1) ->
        let ct := u_var_f c1 in
        kexp e1 (e_ann ct (kcont ty)) (open_e_wrt_u e' ct)) ->
    kprog e1
          (open_e_wrt_u e'
                        (u_lam (ktype ty)
                               (e_ann (u_halt (e_ann (u_var_b 0) (ktype ty)))
                                      t_void))).

Fixpoint ke e k :=
  match e with
  | e_ann u t =>
    match u with
    | u_var_f x =>
      e_ann (u_app k (e_ann (u_var_f x)
                            (ktype t)))
            t_void
    | u_int i =>
      e_ann (u_app k (e_ann (u_int i)
                            (ktype t)))
            t_void
    | u_lam t1 e2 =>
      match e2 with
      | e_ann u2 t2 =>
        e_ann (u_app k (e_ann (u_lam (kcont t1)
                                     (e_ann (u_lam (kcont t2)
                                                   (ke e2 (e_ann (u_var_b 0)
                                                                 (kcont t2))))
                                            (t_arr (kcont t2) t_void)))
                              (ktype t)))
              t_void
      end
    | u_app e1 e2 =>
      match e1,e2 with
      | e_ann u1 t1, e_ann u2 t2 =>
        ke e1 (e_ann (u_lam (ktype t1)
                            (ke e2 (e_ann (u_lam (ktype t2)
                                                 (e_ann (u_app (e_ann (u_app (e_ann (u_var_b 1) (ktype t1))
                                                                             (e_ann (u_var_b 0) (ktype t2)))
                                                                      (t_arr (kcont t) t_void))
                                                               k)
                                                        t_void))
                                          (kcont t2))))
                     (kcont t1))
      end
    | u_prim e1 p e2 =>
      ke e1 (e_ann (u_lam t_int
                          (ke e2 (e_ann (u_lam t_int
                                               (e_ann (u_let (e_ann (u_prim (e_ann (u_var_b 1) t_int) p
                                                                            (e_ann (u_var_b 0) t_int))
                                                                    t_int)
                                                             (u_app k (e_ann (u_var_b 0) t_int)))
                                                      t_void))
                                        (kcont t_int))))
                   (kcont t_int))
    | u_if0 e1 e2 e3 =>
      ke e1 (e_ann (u_lam t_int
                          (e_ann (u_if0 (e_ann (u_var_b 0) t_int)
                                        (ke e2 k)
                                        (ke e3 k))
                                 t_void))
                   (kcont t_int))
    | _ => e
    end
  end.

Definition kp e1 :=
  match e1 with
  | e_ann u1 t1 =>
    ke e1 (e_ann (u_lam (ktype t1)
                        (e_ann (u_halt (e_ann (u_var_b 0)
                                              (ktype t1)))
                               t_void))
                 (kcont t1))
  end.
