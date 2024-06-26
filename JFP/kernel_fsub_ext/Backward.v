Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Reflexivity.

Fixpoint subst_label (Z : atom)  (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top             
  | typ_bot => typ_bot
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X =>  (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_label Z  T1) (subst_label Z  T2)
  | typ_mu T => typ_mu (subst_label Z  T)
  | typ_label l T => if (l==Z) then (typ_fvar Z) else typ_label l (subst_label Z  T)
  | typ_all T1 T2 => typ_all (subst_label Z T1) (subst_label Z T2)
  | typ_all_lb T1 T2 => typ_all_lb (subst_label Z T1) (subst_label Z T2)
  | typ_single l T => typ_single l (subst_label Z T)
  | typ_and T1 T2 => typ_and (subst_label Z T1) (subst_label Z T2)
  end.

Lemma subst_label_open_tt_rec : forall T1 T2 X  k,

  subst_label X  (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_label X  T2) (subst_label X  T1).
Proof with auto.
  intros T1. 
  induction T1; intros ; simpl in *; f_equal...

    destruct (k === n); subst...

    destruct (a == X); subst...
    simpl.
    f_equal...    
Qed.

Lemma subst_label_open_tt : forall T1 T2 (X:atom),
  subst_label X  (open_tt T1 T2) = open_tt (subst_label X  T1) (subst_label X  T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_label_open_tt_rec...
Qed.

Lemma subst_label_open_tt_var : forall T1 (Y X:atom),
  subst_label X  (open_tt T1 Y) = open_tt (subst_label X  T1) Y.
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_label_open_tt_rec...
Qed.

Definition drop_label (Z : atom) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_label Z T)
  | bind_sub_lb T => bind_sub_lb (subst_label Z T)
  | bind_typ T => bind_typ (subst_label Z T)
  end.

Lemma label_transform2: forall A X X0,
    X <> X0 ->
    (subst_label X (open_tt A (typ_label X0 (open_tt A X0)))) =
(open_tt (subst_label X A) (typ_label X0 (open_tt (subst_label X A) X0))).
Proof with auto.
  intros.
  rewrite subst_label_open_tt...
  f_equal...
  simpl...
  destruct (X0==X)...
  destruct H...
  f_equal...
  rewrite subst_label_open_tt...
Qed.

Lemma In_drop_label_free:forall E X Y U,
    In (Y, bind_sub U) E ->
    X <> Y ->
    In (Y, bind_sub (subst_label X U)) (map (drop_label X) E).
Proof with auto.
  induction E;intros...
  destruct a.
  apply in_inv in H.
  destruct H...
  -
    inversion H;subst.
    simpl...
  -
    simpl...
Qed.


Lemma In_drop_label_free_lb:forall E X Y U,
    In (Y, bind_sub_lb U) E ->
    X <> Y ->
    In (Y, bind_sub_lb (subst_label X U)) (map (drop_label X) E).
Proof with auto.
  induction E;intros...
  destruct a.
  apply in_inv in H.
  destruct H...
  -
    inversion H;subst.
    simpl...
  -
    simpl...
Qed.


Lemma subst_label_compatible: forall A B X,
  Compatible A B ->
  Compatible (subst_label X A) (subst_label X B).
Proof with auto.
  intros. dependent induction H...
  - simpl. apply Comp_NE...
  - simpl. apply Comp_L...
  - simpl. apply Comp_R...
  (* - simpl. constructor.
  - simpl. constructor... *)
Qed.

Hint Resolve subst_label_compatible : core.

Lemma WF_drop_label : forall E1 X E2 T U,
    WF (E1 ++ (X, bind_sub U) :: E2) T ->
    wf_env (E1 ++ (X, bind_sub U) :: E2) ->
    WF (map (drop_label X) E1++ [(X, bind_sub U)] ++ E2) (subst_label X T).
Proof with auto.
  intros.
  dependent induction H...
  -
    simpl...
    analyze_binds_uniq H...
    +
      apply uniq_from_wf_env...
    +
      apply WF_var with (U:=subst_label X U0)...
      unfold binds.
      apply In_lemmaL.
      apply In_drop_label_free...
    +
      dependent destruction BindsTacVal.
      apply WF_var with (U:=U)...
    +
      apply WF_var with (U:=U0)...
  -
    simpl...
    analyze_binds_uniq H...
    +
      apply uniq_from_wf_env...
    +
      apply WF_var_lb with (U:=subst_label X U0)...
      unfold binds.
      apply In_lemmaL.
      apply In_drop_label_free_lb...
    +
      apply WF_var_lb with (U:=U0)...
  -
    simpl...
    constructor...
    apply IHWF1...
    apply IHWF2...
  -
    simpl...
    apply WF_all with (L:=L \u dom E1 \u dom E2 \u {{X}});intros...
    apply IHWF...
    rewrite_env (map (drop_label X) (X0 ~ bind_sub T1 ++ E1) ++ (X~ bind_sub U) ++ E2).
    rewrite <- subst_label_open_tt_var.
    apply H1...
    rewrite_env (X0 ~ bind_sub T1 ++ E1 ++ (X, bind_sub U) :: E2)...

  -
    simpl...
    apply WF_all_lb with (L:=L \u dom E1 \u dom E2 \u {{X}});intros...
    apply IHWF...
    rewrite_env (map (drop_label X) (X0 ~ bind_sub_lb T1 ++ E1) ++ (X~ bind_sub U) ++ E2).
    rewrite <- subst_label_open_tt_var.
    apply H1...
    rewrite_env (X0 ~ bind_sub_lb T1 ++ E1 ++ (X, bind_sub U) :: E2)...
  -
    simpl.
    apply WF_rec with (L:=L \u {{X}}\u dom E1 \u dom E2);intros...
    +
      rewrite <- subst_label_open_tt_var.
      rewrite_env (map (drop_label X) (X0 ~ bind_sub typ_top ++ E1) ++ (X~ bind_sub U) ++ E2).
      apply H0...
      rewrite_env (X0 ~ bind_sub typ_top ++ E1 ++ (X, bind_sub U) :: E2)...
    +
      rewrite <- label_transform2...
      rewrite_env (map (drop_label X) (X0 ~ bind_sub typ_top ++ E1) ++ (X~ bind_sub U) ++ E2).
      apply H2...
      rewrite_env (X0 ~ bind_sub typ_top ++ E1 ++ (X, bind_sub U) :: E2)...
  -
    simpl...
    destruct (X0==X);subst...
    +
      apply WF_var with (U:=U)...
    +
      constructor...
      apply IHWF...
  -
    simpl.
    apply WF_single... apply IHWF...
  -
    simpl. constructor. apply IHWF1... apply IHWF2... apply subst_label_compatible...
Qed.



Lemma WF_drop_label_lb : forall E1 X E2 T U,
    WF (E1 ++ (X, bind_sub_lb U) :: E2) T ->
    wf_env (E1 ++ (X, bind_sub_lb U) :: E2) ->
    WF (map (drop_label X) E1++ [(X, bind_sub_lb U)] ++ E2) (subst_label X T).
Proof with auto.
  intros.
  dependent induction H...
  -
    simpl...
    analyze_binds_uniq H...
    +
      apply uniq_from_wf_env...
    +
      apply WF_var with (U:=subst_label X U0)...
      unfold binds.
      apply In_lemmaL.
      apply In_drop_label_free...
    +
      apply WF_var with (U:=U0)...
  -
    simpl...
    analyze_binds_uniq H...
    +
      apply uniq_from_wf_env...
    +
      apply WF_var_lb with (U:=subst_label X U0)...
      unfold binds.
      apply In_lemmaL.
      apply In_drop_label_free_lb...
    +
      dependent destruction BindsTacVal.
      apply WF_var_lb with (U:=U)...
    +
      apply WF_var_lb with (U:=U0)...
  -
    simpl...
    constructor...
    apply IHWF1...
    apply IHWF2...
  -
    simpl...
    apply WF_all with (L:=L \u dom E1 \u dom E2 \u {{X}});intros...
    apply IHWF...
    rewrite_env (map (drop_label X) (X0 ~ bind_sub T1 ++ E1) ++ (X~ bind_sub_lb U) ++ E2).
    rewrite <- subst_label_open_tt_var.
    apply H1...
    rewrite_env (X0 ~ bind_sub T1 ++ E1 ++ (X, bind_sub_lb U) :: E2)...

  -
    simpl...
    apply WF_all_lb with (L:=L \u dom E1 \u dom E2 \u {{X}});intros...
    apply IHWF...
    rewrite_env (map (drop_label X) (X0 ~ bind_sub_lb T1 ++ E1) ++ (X~ bind_sub_lb U) ++ E2).
    rewrite <- subst_label_open_tt_var.
    apply H1...
    rewrite_env (X0 ~ bind_sub_lb T1 ++ E1 ++ (X, bind_sub_lb U) :: E2)...
  -
    simpl.
    apply WF_rec with (L:=L \u {{X}}\u dom E1 \u dom E2);intros...
    +
      rewrite <- subst_label_open_tt_var.
      rewrite_env (map (drop_label X) (X0 ~ bind_sub typ_top ++ E1) ++ (X~ bind_sub_lb U) ++ E2).
      apply H0...
      rewrite_env (X0 ~ bind_sub typ_top ++ E1 ++ (X, bind_sub_lb U) :: E2)...
    +
      rewrite <- label_transform2...
      rewrite_env (map (drop_label X) (X0 ~ bind_sub typ_top ++ E1) ++ (X~ bind_sub_lb U) ++ E2).
      apply H2...
      rewrite_env (X0 ~ bind_sub typ_top ++ E1 ++ (X, bind_sub_lb U) :: E2)...
  -
    simpl...
    destruct (X0==X);subst...
    +
      apply WF_var_lb with (U:=U)...
    +
      constructor...
      apply IHWF...
  -
    simpl.
    apply WF_single... apply IHWF...
  -
    simpl. constructor. apply IHWF1... apply IHWF2... apply subst_label_compatible...
Qed.
    

Lemma wf_env_drop_label : forall E1 E2 X,
    wf_env (E1 ++ [(X, bind_sub typ_top)] ++ E2) ->
    wf_env (map (drop_label X) E1++ [(X, bind_sub typ_top)] ++ E2).
Proof with auto.
  induction E1;intros...
  destruct a.
  dependent destruction H...
  -
    simpl...
    constructor...
    apply IHE1...
    apply WF_drop_label...
  -
    simpl...
    constructor...
    apply IHE1...
    apply WF_drop_label...
  -
    simpl...
    constructor...
    apply IHE1...
    apply WF_drop_label...
Qed.


Lemma drop_label_fresh: forall T X,
    X \notin fl_tt T ->
    T = subst_label X T.
Proof with auto.
  induction T;intros;simpl in *;try solve [f_equal;auto]...
  -
    destruct (a==X);subst...
    +
      apply notin_union in H.
      destruct_hypos.
      apply notin_singleton_1 in H...
      destruct H...
    +
      f_equal...
Qed.
    
Lemma maps_drop_label_free: forall E X,
    X \notin fl_env E ->
    map (drop_label X) E = E.
Proof with auto.
  induction E;intros...
  destruct a.
  destruct b.
  -
    simpl in *.
    f_equal...
    f_equal...
    f_equal...
    rewrite <- drop_label_fresh...
  -
    simpl in *.
    f_equal...
    f_equal...
    f_equal...
    rewrite <- drop_label_fresh...
-
    simpl in *.
    f_equal...
    f_equal...
    f_equal...
    rewrite <- drop_label_fresh...
Qed.

Lemma binds_drop_label_free: forall F X  Y U ,
    In (X, bind_sub U) F ->
    X <> Y ->
    In (X, bind_sub (subst_label Y U)) (map (drop_label Y) F).
Proof with auto.
  induction F;intros...
  apply in_inv in H.
  destruct H...
  -
    destruct a.
    inversion H;subst.
    simpl...
  -
    simpl...
Qed.


Lemma binds_drop_label_free_lb: forall F X  Y U ,
    In (X, bind_sub_lb U) F ->
    X <> Y ->
    In (X, bind_sub_lb (subst_label Y U)) (map (drop_label Y) F).
Proof with auto.
  induction F;intros...
  apply in_inv in H.
  destruct H...
  -
    destruct a.
    inversion H;subst.
    simpl...
  -
    simpl...
Qed.

Lemma drop_label_reverse_type: forall A U X,
    X \notin fl_tt A ->
    subst_label X (subst_tt X (typ_label X U) A) = A.
Proof with auto.
  induction A;intros;simpl in *;try solve [f_equal;auto]...
  -
    destruct (a==X);subst...
    simpl...
    destruct (X==X)...
    destruct n...
  -
    destruct (a==X);subst...
    solve_notin_self X.
    f_equal...
Qed.    

Lemma drop_label_reverse_env: forall E X U,
    X \notin fl_env E ->
    map (drop_label X) (map (subst_tb X (typ_label X U)) E) = E.
Proof with auto.
  induction E;intros...
  simpl in *.
  destruct a.
  destruct b.
  - f_equal...
    f_equal...
    simpl;f_equal;
    apply drop_label_reverse_type...
  -
    f_equal...
    f_equal...
    simpl;f_equal;
    apply drop_label_reverse_type...
  -
    f_equal...
    f_equal...
    simpl;f_equal;
    apply drop_label_reverse_type...
Qed.

Lemma open_twice_to_one: forall E1 E2 A B X,
    sub (E1++ [(X, bind_sub typ_top)] ++ E2) A B ->
    X \notin fl_env E2 ->
    sub (map (drop_label X) E1++ [(X, bind_sub typ_top)] ++ E2) (subst_label X A) (subst_label X B).
Proof with eauto. 
  intros.
  assert (wf_env (E1++ [(X, bind_sub typ_top)] ++ E2)) as HE.
  get_well_form...
  dependent induction H;simpl in *...
  -
    constructor...
    apply wf_env_drop_label...
  -
    constructor...
    apply wf_env_drop_label...
    assert (typ_fvar X0 = subst_label X (typ_fvar X0)) by auto.
    rewrite H2.
    apply WF_drop_label...
  -
    constructor...
    apply wf_env_drop_label...
    apply WF_drop_label...    
  -
    constructor...
    apply wf_env_drop_label...
    apply WF_drop_label...
  -
    apply sa_trans_tvar with (U:=subst_label X U)...
    analyze_binds_uniq H.
    +
      get_well_form.
      apply uniq_from_wf_env...
    +
      unfold binds in *.
      apply In_lemmaL.
      apply In_drop_label_free...
    +
      inversion BindsTacVal...
    +
      unfold binds in *.
      apply In_lemmaR.
      apply in_cons.
      apply binds_drop_label_free with (Y:=X) in BindsTac0...
      rewrite <-  maps_drop_label_free with (X:=X)...
  -
    apply sa_trans_tvar_lb with (U:=subst_label X U)...
    analyze_binds_uniq H.
    +
      get_well_form.
      apply uniq_from_wf_env...
    +
      unfold binds in *.
      apply In_lemmaL.
      apply In_drop_label_free_lb...
    +
      unfold binds in *.
      apply In_lemmaR.
      apply in_cons.
      apply binds_drop_label_free_lb with (Y:=X) in BindsTac0...
      rewrite <-  maps_drop_label_free with (X:=X)...      
  -
    apply sa_all with (L:=L \u {{X}} \u dom E1 \u dom E2);intros...
    rewrite_env (map (drop_label X) (X0 ~ bind_sub S2 ++ E1) ++ (X~ bind_sub typ_top) ++ E2).
    rewrite <- subst_label_open_tt_var.
    rewrite <- subst_label_open_tt_var.
    apply H2...
    rewrite_env (X0 ~ bind_sub S2 ++ E1 ++ (X, bind_sub typ_top) :: E2)...
    constructor...
    get_well_form...
  -
    apply sa_all_lb with (L:=L \u {{X}} \u dom E1 \u dom E2);intros...
    rewrite_env (map (drop_label X) (X0 ~ bind_sub_lb S2 ++ E1) ++ (X~ bind_sub typ_top) ++ E2).
    rewrite <- subst_label_open_tt_var.
    rewrite <- subst_label_open_tt_var.
    apply H2...
    rewrite_env (X0 ~ bind_sub_lb S2 ++ E1 ++ (X, bind_sub typ_top) :: E2)...
    constructor...
    get_well_form...
  -
    apply sa_rec with (L:=L \u {{X}}\u dom E1 \u dom E2);intros...
    +
      rewrite <- subst_label_open_tt_var.
      rewrite_env (map (drop_label X) (X0 ~ bind_sub typ_top ++ E1) ++ (X~ bind_sub typ_top) ++ E2).
      apply WF_drop_label...
      apply H...
      rewrite_env (X0 ~ bind_sub typ_top ++ E1 ++ (X, bind_sub typ_top) :: E2)...
    +
      rewrite <- subst_label_open_tt_var.
      rewrite_env (map (drop_label X) (X0 ~ bind_sub typ_top ++ E1) ++ (X~ bind_sub typ_top) ++ E2).
      apply WF_drop_label...
      apply H0...
      rewrite_env (X0 ~ bind_sub typ_top ++ E1 ++ (X, bind_sub typ_top) :: E2)...
    +
      rewrite <- label_transform2...
      rewrite <- label_transform2...
      rewrite_env (map (drop_label X) (X0 ~ bind_sub typ_top ++ E1) ++ (X~ bind_sub typ_top) ++ E2).
      apply H2...
      rewrite_env  (X0 ~ bind_sub typ_top ++ E1 ++ (X, bind_sub typ_top) :: E2)...
  -
    destruct (X0==X);subst...
    constructor...
    apply wf_env_drop_label...
  - apply sa_and_a... apply WF_drop_label...
  - apply sa_and_b... apply WF_drop_label...
Qed.


Lemma label_transform: forall A X B ,
    X \notin fl_tt A ->
    subst_label X (open_tt A (typ_label X B) ) = open_tt A X .
Proof with auto.
  intro A.
  unfold open_tt.
  generalize 0.
  induction A;intros;simpl in *;try solve [f_equal;auto]...
  -
    destruct (n0==n)...
    simpl...
    destruct (X==X)...
    destruct n1...
  -
    destruct (a==X)...
    subst.
    apply notin_union in H.
    destruct H.
    apply notin_singleton_1 in H.
    destruct H...
    f_equal...
Qed.

Lemma sub_nominal_inversion: forall E X A B,
    sub (X~bind_sub typ_top ++ E) (open_tt A (typ_label X (open_tt A X))) (open_tt B (typ_label X (open_tt B X))) ->
    X \notin  fl_tt A \u fl_tt B \u fl_env E ->
    sub (X~bind_sub typ_top ++ E) (open_tt A X) (open_tt B X).
Proof with auto.
  intros.
  rewrite_env (nil ++ X~bind_sub typ_top ++ E) in H.
  apply open_twice_to_one in H...
  rewrite label_transform in H...
  rewrite label_transform in H...
Qed.  


Lemma WF_strengthening: forall E1 E2 X A  U,
    WF (E1 ++ X ~ U ++ E2) A  ->
    X \notin fv_env E1 \u fv_tt A  ->
    (* wf_env (E1++E2) -> *)
    WF (E1 ++ E2) A .
Proof with eauto.
  intros.
  dependent induction H;simpl in *...
  -
    apply WF_var with (U:=U0)...
    analyze_binds H...
  -
    apply WF_var_lb with (U:=U0)...
    analyze_binds H...
  -
    apply WF_all with (L:=L \u {{X}} \u dom E1 \u dom E2);intros...
    rewrite_env ((X0 ~ bind_sub T1 ++ E1) ++ E2).
    apply H1 with (X1:=X) (U0:=U)...
    solve_notin.
  -
    apply WF_all_lb with (L:=L \u {{X}} \u dom E1 \u dom E2);intros...
    rewrite_env ((X0 ~ bind_sub_lb T1 ++ E1) ++ E2).
    apply H1 with (X1:=X) (U0:=U)...
    solve_notin.
  -
    apply WF_rec with (L:=L \u {{X}} \u dom E1 \u dom E2);intros...
    rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ E2).
    apply H0 with (X1:=X) (U0:=U)...
    solve_notin.
    rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ E2).
    apply H2 with (X1:=X) (U0:=U)...
    solve_notin.
Qed.

Lemma notin_fv_tt_fv_env: forall E T X Y,
    binds Y (bind_sub T) E ->
    X \notin fv_env E ->
    X \notin fv_tt T.
Proof with auto.
  induction E;intros...
  simpl in *...
  destruct a.
  analyze_binds H...
  destruct b...  
  apply IHE with (Y:=Y)...
  apply IHE with (Y:=Y)...
  apply IHE with (Y:=Y)...
Qed.


Lemma notin_fv_tt_fv_env_lb: forall E T X Y,
    binds Y (bind_sub_lb T) E ->
    X \notin fv_env E ->
    X \notin fv_tt T.
Proof with auto.
  induction E;intros...
  simpl in *...
  destruct a.
  analyze_binds H...
  destruct b...  
  apply IHE with (Y:=Y)...
  apply IHE with (Y:=Y)...
  apply IHE with (Y:=Y)...
Qed.


Lemma notin_from_wf_env_spec: forall E1 X T E2,
    wf_env (E1 ++ (X,  T) :: E2) ->
    X \notin dom E2 \u fv_env E2.
Proof with auto.
  induction E1;intros...
  -
    dependent destruction H...
    apply fv_env_ls_dom in H...
    apply fv_env_ls_dom in H...
    apply fv_env_ls_dom in H...
  -
    dependent destruction H...
    simpl in *...
    apply IHE1 in H...
    simpl in *...
    apply IHE1 in H...
    simpl in *...
    apply IHE1 in H...
Qed.

Lemma notin_fv_tt_binds: forall X U Y T E1 E2,
    binds Y (bind_sub T) (E1 ++ (X, U) :: E2) ->
    wf_env (E1 ++ (X, U) :: E2) ->
    X \notin fv_env E1 \u {{Y}} ->
    X \notin fv_tt T.
Proof with auto.
  intros.
  analyze_binds_uniq H...
  -
    apply uniq_from_wf_env...
  -
    apply notin_fv_tt_fv_env with (X:=X) in BindsTac...
  -
    apply notin_fv_tt_fv_env with (X:=X) in BindsTac0...
    apply notin_from_wf_env_spec in H0...
Qed.    


Lemma notin_fv_tt_binds_lb: forall X U Y T E1 E2,
    binds Y (bind_sub_lb T) (E1 ++ (X, U) :: E2) ->
    wf_env (E1 ++ (X, U) :: E2) ->
    X \notin fv_env E1 \u {{Y}} ->
    X \notin fv_tt T.
Proof with auto.
  intros.
  analyze_binds_uniq H...
  -
    apply uniq_from_wf_env...
  -
    apply notin_fv_tt_fv_env_lb with (X:=X) in BindsTac...
  -
    apply notin_fv_tt_fv_env_lb with (X:=X) in BindsTac0...
    apply notin_from_wf_env_spec in H0...
Qed.    
  
Lemma sub_strengthening: forall E1 E2 X A B U,
    sub (E1 ++ X ~ U ++ E2) A B ->
    X \notin fv_env E1 \u fv_tt A \u fv_tt B ->
    wf_env (E1++E2) ->
    sub (E1 ++ E2) A B.
Proof with eauto.
  intros.
  dependent induction H;simpl in *...
  -
    constructor...
    dependent destruction H0.
    + apply WF_var with (U:=U0)...
      analyze_binds H0...
    + apply WF_var_lb with (U:=U0)...
      analyze_binds H0...
  -
    constructor...
    apply WF_strengthening in H0...
  -
    constructor...
    apply WF_strengthening in H0...
  -
    apply sa_trans_tvar with (U:=U0)...
    analyze_binds H...
    apply IHsub with (X0:=X) (U1:=U)...
    solve_notin.
    apply notin_fv_tt_binds in H...
    get_well_form...
  -
    apply sa_trans_tvar_lb with (U:=U0)...
    analyze_binds H...
    apply IHsub with (X0:=X) (U1:=U)...
    solve_notin.
    apply notin_fv_tt_binds_lb in H...
    get_well_form...
  -
    apply sa_all with (L:=L \u {{X}} \u dom E1 \u dom E2);intros...
    rewrite_env ((X0 ~ bind_sub S2 ++ E1) ++ E2).
    apply H2 with (X1:=X) (U0:=U)...
    solve_notin.
    rewrite_env (X0 ~ bind_sub S2 ++ E1 ++ E2)...
    constructor...
    get_well_form.
    apply WF_strengthening in H6...
  -
    apply sa_all_lb with (L:=L \u {{X}} \u dom E1 \u dom E2);intros...
    rewrite_env ((X0 ~ bind_sub_lb S2 ++ E1) ++ E2).
    apply H2 with (X1:=X) (U0:=U)...
    solve_notin.
    rewrite_env (X0 ~ bind_sub_lb S2 ++ E1 ++ E2)...
    constructor...
    get_well_form.
    apply WF_strengthening in H6...
  -
    apply sa_rec with (L:=L \u {{X}} \u dom E1 \u dom E2);intros...
    +
      specialize_x_and_L X0 L.
      rewrite_env (((X0, bind_sub typ_top) :: E1) ++ (X, U) :: E2) in H.
      apply WF_strengthening in H...
      solve_notin.
    +
      specialize_x_and_L X0 L.
      rewrite_env (((X0, bind_sub typ_top) :: E1) ++ (X, U) :: E2) in H0.
      apply WF_strengthening in H0...
      solve_notin.
    +
      rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ E2)...
      apply H2 with (X1:=X) (U0:=U)...
      solve_notin.
      rewrite_env (X0 ~ bind_sub typ_top ++ E1 ++ E2)...
  - apply sa_and_a... eapply WF_strengthening.
    -- apply H.
    -- fsetdec.
  - apply sa_and_b... eapply WF_strengthening... apply H.
Qed.

Lemma sub_strengthening_env: forall E1 E2 A B,
    sub (E1 ++ E2) A B ->
    wf_env E2 ->
    WF E2 A ->
    WF E2 B ->
    sub E2 A B.
Proof with auto.
  induction E1;intros...
  destruct a.
  rewrite_env (nil ++ a ~ b ++ E1 ++ E2) in H.
  apply sub_strengthening in H...
  get_well_form.
  apply notin_from_wf_env_spec in H...
  apply WF_imply_dom in H1.
  apply WF_imply_dom in H2...
  solve_notin.
  apply notin_partial with (E2:=dom E2)...
  apply notin_partial with (E2:=dom E2)...
  get_well_form...
  simpl in *...
  dependent destruction H...
Qed.
