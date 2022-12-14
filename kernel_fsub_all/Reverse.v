Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Equiv.


Lemma label_transform3: forall (X X0:atom) T D,
    X \notin fl_tt T \u {{X0}} ->
    type D ->
    open_tt (subst_label X (subst_tt X (typ_label X D) T))
             (typ_label X0 (open_tt (subst_label X (subst_tt X (typ_label X D) T)) X0))
      = subst_label X (subst_tt X (typ_label X D) (open_tt T (typ_label X0 (open_tt T X0)))).
Proof with auto.
  intros.
  rewrite  subst_tt_open_tt ...
  rewrite subst_label_open_tt ...
  f_equal...
  rewrite drop_label_reverse_type...  
  rewrite drop_label_reverse_type...
  solve_notin.
Qed.

Lemma label_transform4 : forall (X X0:atom) T D,
    X \notin fl_tt T \u {{X0}} ->
    type D ->
    (open_tt (subst_label X (subst_tt X (typ_label X D) T)) X0) = (subst_label X (subst_tt X (typ_label X D) (open_tt T X0))).
Proof with auto.
  intros.
  rewrite <- subst_label_open_tt_var...
  f_equal...
  rewrite subst_tt_open_tt_var...
Qed.  


Lemma binds_subst_label_existial : forall E X Y T U,
    binds X (bind_sub U) (map (drop_label Y) (map (subst_tb Y (typ_label Y T)) E)) ->
    exists Q,
      binds X (bind_sub Q) E.
Proof with auto.
  induction E;intros;simpl in *...
  analyze_binds H...
  destruct a.
  analyze_binds H...
  2: {
    destruct IHE with (X:=X) (Y:=Y) (U:=U) (T:=T)...
    exists x...
  }  
  destruct b;simpl in *.
  + dependent destruction BindsTacVal.
    exists t...
  + inversion BindsTacVal.
  + inversion BindsTacVal.
Qed.


Lemma binds_subst_label_existial_lb : forall E X Y T U,
    binds X (bind_sub_lb U) (map (drop_label Y) (map (subst_tb Y (typ_label Y T)) E)) ->
    exists Q,
      binds X (bind_sub_lb Q) E.
Proof with auto.
  induction E;intros;simpl in *...
  analyze_binds H...
  destruct a.
  analyze_binds H...
  2: {
    destruct IHE with (X:=X) (Y:=Y) (U:=U) (T:=T)...
    exists x...
  }  
  destruct b;simpl in *.
  + inversion BindsTacVal.
  + dependent destruction BindsTacVal.
    exists t...
  + inversion BindsTacVal.
Qed.

Lemma WF_narrowing_env_subst_inv: forall E1 E2 (X:atom) Y S,
    WF (map (subst_tb Y S) E1 ++ Y ~ bind_sub typ_top ++ E2) X ->
    WF (E1 ++ Y ~ bind_sub typ_top ++ E2) X.
Proof with auto.
  induction E1;intros...
  simpl in *.
  destruct a.
  dependent destruction H...
  + analyze_binds H...
    -
      destruct b.
      * apply WF_var with (U:=t)...
      * simpl in *.
        inversion BindsTacVal...  
      * simpl in *.
        inversion BindsTacVal...
    -
      rewrite_env (nil ++ (a~ b) ++ E1 ++ (Y, bind_sub typ_top) :: E2).
      apply WF_weakening...
      apply IHE1  with (S:=S)...
      apply WF_var with (U:=U)...
    -
      apply WF_var with (U:=typ_top)...
    -
      apply WF_var with (U:=U)...
  + analyze_binds H...
    -
      destruct b.
      * apply WF_var with (U:=t)...
      * apply WF_var_lb with (U:=t)...
      * simpl in *.
        inversion BindsTacVal...
    -
      rewrite_env (nil ++ (a~ b) ++ E1 ++ (Y, bind_sub typ_top) :: E2).
      apply WF_weakening...
      apply IHE1  with (S:=S)...
      apply WF_var_lb with (U:=U)...
    -
      apply WF_var_lb with (U:=U)...
Qed.   

(* Lemma sub_map_inv_var: forall X Y X0 C E1 E2, 
    X <> Y -> X0 <> Y ->
  sub (map (subst_tb Y C) E1 ++ (Y, bind_sub typ_top) :: E2) X X0 ->
  sub (map (subst_tb Y C) E1 ++ (Y, bind_sub typ_top) :: E2) X0 X ->
  wf_env (E1 ++ (Y, bind_sub typ_top) :: E2) ->
  sub (E1 ++ (Y, bind_sub typ_top) :: E2) X X0.
Proof with auto.
  intros.
  pose proof suba_sub_tvar_chain H1.
  pose proof suba_sub_tvar_chain H2.
  destruct H4 as [W1 ?].
  destruct H5 as [W2 ?].
  pose proof sub_tvar_chain_antisym H4 H5.
  subst.
  apply sa_fvar...
  get_well_form.
  apply WF_narrowing_env_subst_inv in H6...
Qed. *)

Lemma drop_label_reverse_wf: forall E1 E2 C D A X,
    WF (map (drop_label X) (map (subst_tb X (typ_label X C)) E1) ++
            (X, bind_sub typ_top) :: E2)
       (subst_label X (subst_tt X (typ_label X D) A)) ->
    X \notin fl_tt A -> type D ->
    WF (E1 ++ (X, bind_sub typ_top) :: E2) A.
Proof with auto.
  intros.
  assert (type A) as HA.
  get_type...
  rewrite drop_label_reverse_type in H... 
  apply type_to_rec in HA.
  generalize dependent E1.
  generalize dependent E2.
  generalize dependent C.
  generalize dependent D.
  generalize dependent X.
  induction HA;intros;simpl in *;try solve [dependent destruction H;auto]...
  -
    destruct (X==X0);subst...
    +
      apply WF_var with (U:=typ_top)...
    +
      simpl in H...
      dependent destruction H...
      * analyze_binds H...
        apply binds_subst_label_existial in BindsTac.
        destruct_hypos.
        apply WF_var with (U:=x)...
        apply WF_var with (U:=U)...
      * analyze_binds H...
        apply binds_subst_label_existial_lb in BindsTac.
        destruct_hypos.
        apply WF_var_lb with (U:=x)...
        apply WF_var_lb with (U:=U)...
  -
    dependent destruction H.
    constructor...
    apply IHHA1 with (C:=C) (D:=D)...
    apply IHHA2 with (C:=C) (D:=D)...
  -
    dependent destruction H5.
    apply WF_rec with (L:=L \u L0 \u {{X}});intros...
    +
      rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ (X, bind_sub typ_top) :: E2).
      apply H2 with (C:=C) (D:=D)...
      solve_notin.
      rewrite <- subst_tt_open_tt_var...
      rewrite  subst_label_open_tt_var...
      apply H5...
    +
      rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ (X, bind_sub typ_top) :: E2).
      apply H0 with (C:=C) (D:=D)...
      solve_notin.
      rewrite <- label_transform3...
      apply H6...
  -
    dependent destruction H3.
    apply WF_all with (L:=L \u L0 \u {{X}});intros...
    +
      apply IHHA with (C:=C) (D:=D)...
    +
      rewrite_env ((X0 ~ bind_sub T1 ++ E1) ++ (X, bind_sub typ_top) :: E2).
      apply H0 with (C:=C) (D:=D)...
      solve_notin.
      rewrite <- label_transform4...
      simpl.
      rewrite drop_label_reverse_type...
      assert (T1 = subst_label X (subst_tt X (typ_label X D) T1)).
      rewrite drop_label_reverse_type ...
      rewrite H6.
      apply H4...
  -
    dependent destruction H3.
    apply WF_all_lb with (L:=L \u L0 \u {{X}});intros...
    +
      apply IHHA with (C:=C) (D:=D)...
    +
      rewrite_env ((X0 ~ bind_sub_lb T1 ++ E1) ++ (X, bind_sub typ_top) :: E2).
      apply H0 with (C:=C) (D:=D)...
      solve_notin.
      rewrite <- label_transform4...
      simpl.
      rewrite drop_label_reverse_type...
      assert (T1 = subst_label X (subst_tt X (typ_label X D) T1)).
      rewrite drop_label_reverse_type ...
      rewrite H6.
      apply H4...
  -
    destruct (l==X);subst...
    +
      apply notin_union  in H0.
      destruct_hypos.
      apply test_solve_notin_7 in H0.
      destruct H0.
    +
      dependent destruction H.
      constructor...
      apply IHHA with (C:=C) (D:=D)...
Qed.      


    
Lemma WF_nominal_inversion: forall E1 E2 X A (X0:atom) D C,
    WF (X0 ~ bind_sub typ_top ++
           map (subst_tb X (typ_label X (open_tt C X))) E1 ++ (X, bind_sub typ_top) :: E2)
          (open_tt (subst_tt X (typ_label X (open_tt D X)) A) X0)->
    X \notin {{X0}} \u fl_tt A  ->
    wf_env (X0 ~ bind_sub typ_top ++
           map (subst_tb X (typ_label X (open_tt C X))) E1 ++ (X, bind_sub typ_top) :: E2) ->
    type (open_tt D X) ->
    WF (X0 ~ bind_sub typ_top ++ E1 ++ (X, bind_sub typ_top) :: E2) (open_tt A X0) .
Proof with auto.
  intros.
  rewrite subst_tt_open_tt_var in H...
  rewrite_env ((X0 ~ bind_sub typ_top ++
           map (subst_tb X (typ_label X (open_tt C X))) E1) ++ (X, bind_sub typ_top) :: E2) in H.
  apply WF_drop_label in H...
  simpl in H...
  rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ (X, bind_sub typ_top) :: E2).
  apply drop_label_reverse_wf with (C:=open_tt C X) (D:=open_tt D X)...
  solve_notin.
Qed.

Ltac solve_bind_inv :=
repeat match goal with
| H: sub _ _ (typ_fvar ?X) |- _ => inversion H;clear H
| H: sub _ (typ_fvar ?X) _ |- _ => inversion H;clear H
end;subst;
let InvTac := fresh "InvTac" in
match goal with
| [ H1: binds ?X (bind_sub_lb _) ?E ,
  H2: binds ?X (bind_sub _) ?E |- _ ] =>
  pose proof binds_ub_lb_invalid _ _ _ H1 H2 as InvTac
end;
try solve [exfalso;apply InvTac;apply uniq_from_wf_env;get_well_form;auto].


Lemma binds_ub_lb_invalid_ext: forall E1 E2 X X1 S U B U0,
  binds X (bind_sub_lb U) 
      (map (subst_tb X1 S) E1 ++ (X1, bind_sub B) :: E2) ->
  binds X (bind_sub U0) (E1 ++ (X1, bind_sub B) :: E2) ->
  wf_env (E1 ++ (X1,bind_sub B) :: E2) -> 
  False.
Proof with auto.
  intros.
  destruct (X == X1).
  + subst. analyze_binds_uniq H0. apply uniq_from_wf_env...
    apply binds_mid_eq in H... inversion H.
  + apply binds_map_free_sub with (S:=S) in H0...
      analyze_binds H.
      { analyze_binds H0.
        + pose proof binds_ub_lb_invalid _ _ _ BindsTac BindsTac0.
          apply H. apply uniq_from_wf_env in H1.
          apply uniq_app_1 in H1. apply uniq_map_2...
        + apply in_split in BindsTac0.
          destruct_hypos. subst E2.
          apply uniq_from_wf_env in H1.
          apply fresh_app_l with (x:=X) (a:=bind_sub (subst_tt X1 S U0)) in H1...
          apply binds_In in BindsTac. rewrite dom_map in BindsTac... }
      { analyze_binds H0.
        + apply in_split in BindsTac0. 
          destruct_hypos. subst E2.
          apply uniq_from_wf_env in H1.
          apply fresh_app_l with (x:=X) (a:=bind_sub_lb U) in H1...
          apply binds_In in BindsTac. rewrite dom_map in BindsTac...
        + pose proof binds_ub_lb_invalid _ _ _ BindsTac0 BindsTac.
          apply H. apply uniq_from_wf_env in H1.
          apply uniq_app_2 in H1. inversion H1...
      }
Qed.


Lemma subst_reverse_equiv: forall A,
    type4rec A -> forall B, type4rec B ->
    forall X C D E1 E2 S,
    X \notin fl_tt A \u fl_tt B \u fv_tt S \u fv_tt C \u fv_tt D->
    equiv (map (subst_tb X (typ_label X (open_tt S X))) E1 ++ (X, bind_sub typ_top) :: E2 ) (subst_tt X (typ_label X (open_tt C X)) A) (subst_tt X (typ_label X (open_tt D X)) B) ->
    equiv (E1 ++ (X, bind_sub typ_top) :: E2) A B ->
    WF ((X, bind_sub typ_top) :: E2) (open_tt C X) ->
    WF ((X, bind_sub typ_top) :: E2) (open_tt D X) ->
    WF ((X, bind_sub typ_top) :: E2) (open_tt S X) ->
    wf_env (E1 ++ (X, bind_sub typ_top) :: E2) ->
    (equiv ((X, bind_sub typ_top) ::E2) (open_tt C X)  (open_tt D X) \/ (X \notin fv_tt A \u fv_tt B )) .
Proof with auto.
  unfold equiv.
  intros A HA;induction HA;
    intros B HB;induction HB;intros;destruct_hypos;simpl in *;try solve [inversion H0|
      inversion H1|inversion H2|inversion H3|inversion H4|inversion H5|inversion H6|inversion H7|inversion H8|inversion H9|inversion H10|destruct (X==X0);subst;auto;inversion H0
      ]...
  - destruct (X == X0)... subst X0.
    dependent destruction H7...
  -
    destruct (X==X0);subst...
    inversion H6. subst.
    apply binds_mid_eq in H9... inversion H9.
      apply uniq_from_wf_env...
  -
    destruct (X==X1);destruct (X0==X1);subst...
    +
      dependent destruction H0.
      dependent destruction H7.
      left.
      apply wf_env_cons in H5...
      apply sub_strengthening_env in H0...
      apply sub_strengthening_env in H7...
    +
      inversion H0...
      subst. inversion H6;subst...
      2:{ apply binds_mid_eq in H10... inversion H10. apply uniq_from_wf_env... }
      pose proof binds_ub_lb_invalid_ext _ _ _ _ _ _ _ _ H9 H10.
      destruct H8...
    +
      inversion H7...
      subst. inversion H1;subst...
      2:{ apply binds_mid_eq in H10... inversion H10. apply uniq_from_wf_env... }
      pose proof binds_ub_lb_invalid_ext _ _ _ _ _ _ _ _ H9 H10.
      destruct H8...
  - solve_bind_inv.
  - solve_bind_inv.
  - solve_bind_inv.
  - solve_bind_inv.
  - solve_bind_inv.
  - solve_bind_inv.
  -
    dependent destruction H0.
    dependent destruction H7.
    dependent destruction H1.
    dependent destruction H6.
    clear IHHB1 IHHB2.
    destruct IHHA1 with (B:=T0) (X:=X) (C:=C) (D:=D) (E1:=E1) (E2:=E2) (S:=S)...
    destruct IHHA2 with (B:=T3) (X:=X) (C:=C) (D:=D) (E1:=E1) (E2:=E2) (S:=S)...
  - solve_bind_inv.
  -
    clear H4 H6.
    dependent destruction H8.
    dependent destruction H15.
    dependent destruction H12.
    dependent destruction H15.
    pick fresh Y.
    assert (type (open_tt C X)) by (get_type;auto).
    assert (type (open_tt D X)) by (get_type;auto).
    destruct H0 with (X:=Y) (X0:=X) (B:=open_tt T0 (typ_label Y (open_tt T0 Y))) (C:=C) (D:=D) (E1:=Y~bind_sub typ_top ++E1) (E2:=E2) (S:=S)...
    +
      solve_notin.
    +
      split.
      *
        rewrite_env (Y ~ bind_sub typ_top ++
                     map (subst_tb X (typ_label X (open_tt S X))) E1 ++ (X, bind_sub typ_top) :: E2).
      rewrite subst_tt_open_tt_twice...
      rewrite subst_tt_open_tt_twice...
      *
        rewrite_env (Y ~ bind_sub typ_top ++
                     map (subst_tb X (typ_label X (open_tt S X))) E1 ++ (X, bind_sub typ_top) :: E2).
      rewrite subst_tt_open_tt_twice...
      rewrite subst_tt_open_tt_twice...
    +
      split.
      *
        apply H14...
      *
        apply H17...
    +      
      rewrite_env (Y ~ bind_sub typ_top ++ E1 ++ (X, bind_sub typ_top) :: E2)...
    +
      right.
      apply notin_union in H24.
      destruct_hypos.
      apply notin_fv_open_inv in H24.
      apply notin_fv_open_inv in H25...
  -
    solve_bind_inv.
  -    
    clear H2 IHHB.
    dependent destruction H4.
    dependent destruction H11.
    dependent destruction H5.
    dependent destruction H10.
    destruct IHHA with (B:=T0) (X:=X) (C:=C) (D:=D) (E1:=E1) (E2:= E2) (S:=S)...
    clear IHHA.
    pick fresh Y.
    destruct H0 with (B:=open_tt T3 Y) (X:=Y) (X0:=X) (C:=C) (D:=D) (E1:=Y ~ bind_sub T1 ++E1) (E2:=E2) (S:=S);clear H0...
    +
      solve_notin.
    +
      split.
      *
        rewrite <- subst_tt_open_tt_var...
        rewrite <- subst_tt_open_tt_var...
        rewrite_env (nil ++ Y ~ bind_sub (subst_tt X (typ_label X (open_tt S X)) T1) ++ map (subst_tb X (typ_label X (open_tt S X))) E1 ++ (X, bind_sub typ_top) :: E2).
        apply sub_narrowing with (Q:=subst_tt X (typ_label X (open_tt D X)) T0)...
        --
          clear Fr.
          assert (subst_tt X (typ_label X (open_tt D X)) T0 = subst_tt X (typ_label X (open_tt S X)) T0).
          {
            rewrite <- subst_tt_fresh...
            rewrite <- subst_tt_fresh...
          }
          rewrite H0.
          assert (equiv (X ~ bind_sub typ_top ++ E2) (typ_label X (open_tt S X)) (typ_label X (open_tt S X))).
          {
            apply wf_env_cons in H10.
            unfold equiv;split;constructor;
            apply Reflexivity...
          }
          apply equiv_sub_subst...
        --
          apply H2...
        --
          get_type...
        --
          get_type...
      *
        rewrite <- subst_tt_open_tt_var...
        rewrite <- subst_tt_open_tt_var...
        rewrite_env (nil ++ Y ~ bind_sub (subst_tt X (typ_label X (open_tt S X)) T1) ++ map (subst_tb X (typ_label X (open_tt S X))) E1 ++ (X, bind_sub typ_top) :: E2).
        apply sub_narrowing with (Q:=subst_tt X (typ_label X (open_tt C X)) T1)...
        --
          clear Fr.
          assert (subst_tt X (typ_label X (open_tt C X)) T1 = subst_tt X (typ_label X (open_tt S X)) T1).
          {
            rewrite <- subst_tt_fresh...
            rewrite <- subst_tt_fresh...
          }
          rewrite H0.
          assert (equiv (X ~ bind_sub typ_top ++ E2) (typ_label X (open_tt S X)) (typ_label X (open_tt S X))).
          {
            apply wf_env_cons in H10.
            unfold equiv;split;constructor;
            apply Reflexivity...
          }
          apply equiv_sub_subst_refl...
          get_well_form...
        --
          apply H4...
        --
          get_type...
        --
          get_type...
    +
      split.
      *
        rewrite_env (nil ++ Y ~ bind_sub T1 ++ E1 ++ (X, bind_sub typ_top) :: E2).
        apply sub_narrowing with (Q:=T0)...
        apply H5...
      *
        rewrite_env (Y ~ bind_sub T1 ++ E1 ++ (X, bind_sub typ_top) :: E2).
        apply H6...        
    +
      rewrite_env (Y ~ bind_sub T1 ++ E1 ++ (X, bind_sub typ_top) :: E2)...
      constructor...
      get_well_form...
    +
      right.
      apply notin_union in H12.
      destruct_hypos.
      apply notin_fv_open_inv in H0.
      apply notin_fv_open_inv in H12.
      solve_notin.
  -
    solve_bind_inv.
  -
    clear H2 IHHB.
    dependent destruction H4.
    dependent destruction H11.
    dependent destruction H5.
    dependent destruction H10.
    destruct IHHA with (B:=T0) (X:=X) (C:=C) (D:=D) (E1:=E1) (E2:= E2) (S:=S)...
    clear IHHA.
    pick fresh Y.
    destruct H0 with (B:=open_tt T3 Y) (X:=Y) (X0:=X) (C:=C) (D:=D) (E1:=Y ~ bind_sub_lb T1 ++E1) (E2:=E2) (S:=S);clear H0...
    +
      solve_notin.
    +
      split.
      *
        rewrite <- subst_tt_open_tt_var...
        rewrite <- subst_tt_open_tt_var...
        rewrite_env (nil ++ Y ~ bind_sub_lb (subst_tt X (typ_label X (open_tt S X)) T1) ++ map (subst_tb X (typ_label X (open_tt S X))) E1 ++ (X, bind_sub typ_top) :: E2).
        apply sub_narrowing_lb with (Q:=subst_tt X (typ_label X (open_tt D X)) T0)...
        --
          clear Fr.
          assert (subst_tt X (typ_label X (open_tt D X)) T0 = subst_tt X (typ_label X (open_tt S X)) T0).
          {
            rewrite <- subst_tt_fresh...
            rewrite <- subst_tt_fresh...
          }
          rewrite H0.
          assert (equiv (X ~ bind_sub typ_top ++ E2) (typ_label X (open_tt S X)) (typ_label X (open_tt S X))).
          {
            apply wf_env_cons in H10.
            unfold equiv;split;constructor;
            apply Reflexivity...
          }
          apply equiv_sub_subst...
        --
          apply H2...
        --
          get_type...
        --
          get_type...
      *
        rewrite <- subst_tt_open_tt_var...
        rewrite <- subst_tt_open_tt_var...
        rewrite_env (nil ++ Y ~ bind_sub_lb (subst_tt X (typ_label X (open_tt S X)) T1) ++ map (subst_tb X (typ_label X (open_tt S X))) E1 ++ (X, bind_sub typ_top) :: E2).
        apply sub_narrowing_lb with (Q:=subst_tt X (typ_label X (open_tt C X)) T1)...
        --
          clear Fr.
          assert (subst_tt X (typ_label X (open_tt C X)) T1 = subst_tt X (typ_label X (open_tt S X)) T1).
          {
            rewrite <- subst_tt_fresh...
            rewrite <- subst_tt_fresh...
          }
          rewrite H0.
          assert (equiv (X ~ bind_sub typ_top ++ E2) (typ_label X (open_tt S X)) (typ_label X (open_tt S X))).
          {
            apply wf_env_cons in H10.
            unfold equiv;split;constructor;
            apply Reflexivity...
          }
          apply equiv_sub_subst_refl...
          get_well_form...
        --
          apply H4...
        --
          get_type...
        --
          get_type...
    +
      split.
      *
        rewrite_env (nil ++ Y ~ bind_sub_lb T1 ++ E1 ++ (X, bind_sub typ_top) :: E2).
        apply sub_narrowing_lb with (Q:=T0)...
        apply H5...
      *
        rewrite_env (Y ~ bind_sub_lb T1 ++ E1 ++ (X, bind_sub typ_top) :: E2).
        apply H6...        
    +
      rewrite_env (Y ~ bind_sub_lb T1 ++ E1 ++ (X, bind_sub typ_top) :: E2)...
      constructor...
      get_well_form...
    +
      right.
      apply notin_union in H12.
      destruct_hypos.
      apply notin_fv_open_inv in H0.
      apply notin_fv_open_inv in H12.
      solve_notin.

  -
    solve_bind_inv.
  -
    dependent destruction H0...
    dependent destruction H7...
    dependent destruction H1.
    dependent destruction H6.
    clear IHHB.
    destruct IHHA with (B:=A0) (X:=X) (C:=C) (D:=D) (E1:=E1) (E2:=E2) (S:=S)...   
Qed.

