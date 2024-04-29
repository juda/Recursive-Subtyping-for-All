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


(* Todo: think about a <= X <= b by a <= X, Y <= b, X & Y *)
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

