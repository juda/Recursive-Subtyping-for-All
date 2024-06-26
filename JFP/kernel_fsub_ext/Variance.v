Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Backward.

Lemma maps_subst_tb_free: forall E X U,
    X \notin fv_env E ->
    map (subst_tb X U) E = E.
Proof with auto.
  induction E;intros...
  destruct a.
  destruct b.
  -
    simpl in *.
    f_equal...
    f_equal...
    f_equal...
    rewrite <- subst_tt_fresh...
  -
    simpl in *.
    f_equal...
    f_equal...
    f_equal...
    rewrite <- subst_tt_fresh...
  -
    simpl in *.
    f_equal...
    f_equal...
    f_equal...
    rewrite <- subst_tt_fresh...
Qed.

Lemma binds_map_free_sub: forall E1 E2 X Y U S Q,
    Y \notin {{X}}  ->
    wf_env (E1 ++ (Y, bind_sub Q) :: E2) ->
    binds X (bind_sub U) (E1 ++ (Y, bind_sub Q) :: E2) ->
    binds X (bind_sub (subst_tt Y S U)) (map (subst_tb Y S) E1 ++  E2).
Proof with auto.
  intros.
  analyze_binds H1...
  -
    unfold binds in *.
    apply In_lemmaL.
    apply binds_map_free...
  -
    unfold binds in *.
    apply In_lemmaR.
    rewrite <- maps_subst_tb_free with (X:=Y) (U:=S)...
    apply binds_map_free...
    apply notin_from_wf_env in H0...
Qed.


Lemma binds_map_free_sub2: forall E1 E2 X Y U S Q,
    Y \notin {{X}}  ->
    wf_env (E1 ++ (Y, bind_sub Q) :: E2) ->
    binds X (bind_sub_lb U) (E1 ++ (Y, bind_sub Q) :: E2) ->
    binds X (bind_sub_lb (subst_tt Y S U)) (map (subst_tb Y S) E1 ++  E2).
Proof with auto.
  intros.
  analyze_binds H1...
  -
    unfold binds in *.
    apply In_lemmaL.
    apply binds_map_free_lb...
  -
    unfold binds in *.
    apply In_lemmaR.
    rewrite <- maps_subst_tb_free with (X:=Y) (U:=S)...
    apply binds_map_free_lb...
    apply notin_from_wf_env in H0...
Qed.


Lemma binds_map_free_sub_lb: forall E1 E2 X Y U S Q,
    Y \notin {{X}}  ->
    wf_env (E1 ++ (Y, bind_sub_lb Q) :: E2) ->
    binds X (bind_sub_lb U) (E1 ++ (Y, bind_sub_lb Q) :: E2) ->
    binds X (bind_sub_lb (subst_tt Y S U)) (map (subst_tb Y S) E1 ++  E2).
Proof with auto.
  intros.
  analyze_binds H1...
  -
    unfold binds in *.
    apply In_lemmaL.
    apply binds_map_free_lb...
  -
    unfold binds in *.
    apply In_lemmaR.
    rewrite <- maps_subst_tb_free with (X:=Y) (U:=S)...
    apply binds_map_free_lb...
    apply notin_from_wf_env_lb in H0...
Qed.


Lemma binds_map_free_sub_lb2: forall E1 E2 X Y U S Q,
    Y \notin {{X}}  ->
    wf_env (E1 ++ (Y, bind_sub_lb Q) :: E2) ->
    binds X (bind_sub U) (E1 ++ (Y, bind_sub_lb Q) :: E2) ->
    binds X (bind_sub (subst_tt Y S U)) (map (subst_tb Y S) E1 ++  E2).
Proof with auto.
  intros.
  analyze_binds H1...
  -
    unfold binds in *.
    apply In_lemmaL.
    apply binds_map_free...
  -
    unfold binds in *.
    apply In_lemmaR.
    rewrite <- maps_subst_tb_free with (X:=Y) (U:=S)...
    apply binds_map_free...
    apply notin_from_wf_env_lb in H0...
Qed.


Fixpoint subst_tl (Z X: atom)  (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top             
  | typ_bot => typ_bot
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X =>  (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tl Z X T1) (subst_tl Z X T2)
  | typ_mu T => typ_mu (subst_tl Z X T)
  | typ_label l T => if (l==Z) then typ_label X (subst_tl Z X T) else typ_label l (subst_tl Z  X T)
  | typ_all T1 T2 => typ_all (subst_tl Z X T1) (subst_tl Z X T2)
  | typ_all_lb T1 T2 => typ_all_lb (subst_tl Z X T1) (subst_tl Z X T2)
  | typ_single l T => typ_single l (subst_tl Z X T)
  | typ_and T1 T2 => typ_and (subst_tl Z X T1) (subst_tl Z X T2)
  end.

Lemma subst_tl_open_tt_var: forall T X X0 Y,
    X0 \notin {{X}} ->
    (open_tt (subst_tl X Y T) X0) = subst_tl X Y (open_tt T X0).
Proof with auto.
  unfold open_tt.
  intro T.
  generalize 0.
  induction T;intros;simpl in *;try f_equal...
  -
    destruct (n0==n)...
  -
    destruct (a==X);subst...
    simpl...
    f_equal...
    simpl...
    f_equal...
Qed.

Lemma subst_tl_open_tt: forall T X U Y,
    (open_tt (subst_tl X Y T) (subst_tl X Y U)) = subst_tl X Y (open_tt T U).
Proof with auto.
  unfold open_tt.
  intro T.
  generalize 0.
  induction T;intros;simpl in *;try f_equal...
  -
    destruct (n0==n)...
  -
    destruct (a==X);subst...
    simpl...
    f_equal...
    simpl...
    f_equal...
Qed.    


Lemma subst_tl_open_tt_twice: forall  X X0 Y A,
    X0 \notin {{X}} ->
    open_tt (subst_tl X Y A) (typ_label X0 (open_tt (subst_tl X Y A) X0))
= subst_tl X Y (open_tt A (typ_label X0 (open_tt A X0))).
Proof with auto.
  intros.
  rewrite <- subst_tl_open_tt.
  f_equal...
  simpl...
  destruct (X0==X);subst...
  apply test_solve_notin_7 in H...
  destruct H.
  f_equal.
  rewrite subst_tl_open_tt_var...
Qed.


Lemma subst_tl_compatible: forall A B X Y,
  Compatible A B ->
  Compatible (subst_tl X Y A) (subst_tl X Y B).
Proof with auto.
  intros. dependent induction H...
  - simpl. apply Comp_NE...
  - simpl. apply Comp_L...
  - simpl. apply Comp_R...
  (* - simpl. constructor.
  - simpl. constructor... *)
Qed.

Hint Resolve subst_tl_compatible : core.


Lemma WF_renaming_tl: forall E A  X Y,
    WF E A ->
    WF E (subst_tl X Y A).
Proof with eauto.
  intros.
  induction H;simpl...
  -
    apply WF_all with (L:=L \u {{X}});intros...
    rewrite subst_tl_open_tt_var...
    add_nil.
    apply WF_narrowing with (V:=T1)...
  -
    apply WF_all_lb with (L:=L \u {{X}});intros...
    rewrite subst_tl_open_tt_var...
    add_nil.
    apply WF_narrowing_lb with (V:=T1)...
  -
    apply WF_rec with (L:=L \u {{X}});intros...
    rewrite subst_tl_open_tt_var...
    rewrite subst_tl_open_tt_twice...
  -
    destruct (X0==X)...
Qed.

Lemma subst_tl_fresh: forall A X Y,
    X \notin fl_tt A ->
    subst_tl X Y A = A.
Proof with auto.
  induction A;intros;simpl in *;try f_equal...
  destruct (a==X);subst...
  apply notin_union in H.
  destruct H.
  apply test_solve_notin_7 in H.
  destruct H.
  f_equal...
Qed.  

Lemma label_transform: forall A B X Y,
    X \notin fl_tt A \u fl_tt B ->
    subst_tl X Y (open_tt A (typ_label X B)) = open_tt A (typ_label Y B).
Proof with auto.
  intros.
  rewrite <- subst_tl_open_tt...
  rewrite subst_tl_fresh...
  f_equal...
  simpl...
  destruct (X==X)...
  f_equal...
  rewrite subst_tl_fresh...
  destruct n...
Qed.  

Lemma WF_renaming_unfolding: forall  E2 X Y Q A,
    WF ( X ~ bind_sub Q ++ E2) (open_tt A (typ_label X (open_tt A X))) ->
    Y \notin {{X}} \u fv_tt A \u fl_tt A ->
    X \notin fv_tt A \u fl_tt A ->
    WF ( Y ~ bind_sub Q ++ E2) (open_tt A (typ_label Y (open_tt A Y))).
Proof with auto.
  intros.
  rewrite_env (nil ++ X ~ bind_sub Q ++ E2) in H.
  apply WF_renaming with (Y:=Y) in H...
  simpl in H.
  rewrite subst_tt_open_tt in H...
  rewrite <- subst_tt_fresh in H...
  simpl in H.
  rewrite <- subst_tt_intro in H...
  apply WF_renaming_tl with (X:=X) (Y:=Y) in H...
  rewrite label_transform in H...
  solve_notin.
  solve_notin.
Qed.

Lemma label_transform3: forall A (X X0 Y : atom),
    X <> X0 ->
    (subst_tt X Y (open_tt A (typ_label X0 (open_tt A X0)))) =
(open_tt (subst_tt X Y A) (typ_label X0 (open_tt (subst_tt X Y A) X0))).
Proof with auto.
  intros.
  rewrite  subst_tt_open_tt...
  f_equal...
  simpl.
  f_equal...
  rewrite  subst_tt_open_tt_var...
Qed.
                                     
Lemma WF_replacing: forall E1 E2 T U (X Y:atom),
    WF ( E1 ++ X ~ bind_sub U ++E2) T ->
    Y <> X ->
    WF (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++E2) (subst_tt X Y T).
Proof with auto.
  intros.
  dependent induction H;intros;simpl;try solve [rewrite_alist (map (subst_tb X Y) E1  ++ Y ~ bind_sub U ++ E2);constructor;auto]...
  -
    destruct (X0==X)...
    { subst. apply WF_var with (U:=U)... }
    { apply binds_app_iff in H. destruct H.
      + apply WF_var with (U:=(subst_tt X Y U0))...
        apply binds_app_iff. left.
        apply binds_map_free...
      + apply WF_var with (U:=U0)...
        simpl. analyze_binds H. }
  -
    destruct (X0==X)...
    { subst. apply WF_var with (U:=U)... }
    { apply binds_app_iff in H. destruct H.
      + apply WF_var_lb with (U:=(subst_tt X Y U0))...
        apply binds_app_iff. left.
        apply binds_map_free_lb...
      + apply WF_var_lb with (U:=U0)...
        simpl. analyze_binds H. }
  - apply WF_all with (L:= L \u {{X}});intros...
    + apply IHWF...
    + rewrite_alist ((map (subst_tb X Y) ((X0 ~ bind_sub T1) ++ E1)) ++ Y ~ bind_sub U ++ E2).
      rewrite  subst_tt_open_tt_var...
  - apply WF_all_lb with (L:= L \u {{X}});intros...
    + apply IHWF...
    + rewrite_alist ((map (subst_tb X Y) ((X0 ~ bind_sub_lb T1) ++ E1)) ++ Y ~ bind_sub U ++ E2).
      rewrite  subst_tt_open_tt_var...
  -
    apply WF_rec with (L:=L \u {{X}});intros.
    rewrite_alist ((map (subst_tb X Y) ((X0 ~ bind_sub typ_top) ++ E1)) ++ Y ~ bind_sub U ++ E2).
    rewrite  subst_tt_open_tt_var...
    rewrite_alist ((map (subst_tb X Y) ((X0 ~ bind_sub typ_top) ++ E1)) ++ Y ~ bind_sub U ++ E2).
    rewrite <- label_transform3...
Qed.


Lemma WF_replacing_lb: forall E1 E2 T U (X Y:atom),
    WF ( E1 ++ X ~ bind_sub_lb U ++E2) T ->
    Y <> X ->
    WF (map (subst_tb X Y) E1 ++ Y ~ bind_sub_lb U ++E2) (subst_tt X Y T).
Proof with auto.
  intros.
  dependent induction H;intros;simpl;try solve [rewrite_alist (map (subst_tb X Y) E1  ++ Y ~ bind_sub_lb U ++ E2);constructor;auto]...
  -
    destruct (X0==X)...
    { subst. apply WF_var_lb with (U:=U)... }
    { apply binds_app_iff in H. destruct H.
      + apply WF_var with (U:=(subst_tt X Y U0))...
        apply binds_app_iff. left.
        apply binds_map_free...
      + apply WF_var with (U:=U0)...
        simpl. analyze_binds H. }
  -
    destruct (X0==X)...
    { subst. apply WF_var_lb with (U:=U)... }
    { apply binds_app_iff in H. destruct H.
      + apply WF_var_lb with (U:=(subst_tt X Y U0))...
        apply binds_app_iff. left.
        apply binds_map_free_lb...
      + apply WF_var_lb with (U:=U0)...
        simpl. analyze_binds H. }
  - apply WF_all with (L:= L \u {{X}});intros...
    + apply IHWF...
    + rewrite_alist ((map (subst_tb X Y) ((X0 ~ bind_sub T1) ++ E1)) ++ Y ~ bind_sub_lb U ++ E2).
      rewrite  subst_tt_open_tt_var...
  - apply WF_all_lb with (L:= L \u {{X}});intros...
    + apply IHWF...
    + rewrite_alist ((map (subst_tb X Y) ((X0 ~ bind_sub_lb T1) ++ E1)) ++ Y ~ bind_sub_lb U ++ E2).
      rewrite  subst_tt_open_tt_var...
  -
    apply WF_rec with (L:=L \u {{X}});intros.
    rewrite_alist ((map (subst_tb X Y) ((X0 ~ bind_sub typ_top) ++ E1)) ++ Y ~ bind_sub_lb U ++ E2).
    rewrite  subst_tt_open_tt_var...
    rewrite_alist ((map (subst_tb X Y) ((X0 ~ bind_sub typ_top) ++ E1)) ++ Y ~ bind_sub_lb U ++ E2).
    rewrite <- label_transform3...
Qed.

Lemma WF_replacing': forall E T U (X Y:atom),
    WF ( X ~ bind_sub U ++E) T ->
    Y <> X ->
    WF ( Y ~ bind_sub U ++E) (subst_tt X Y T).
Proof with auto.
  intros.
  rewrite_alist (map (subst_tb X Y) nil ++ [(Y, bind_sub U)] ++ E).
  apply WF_replacing...
Qed.


Lemma WF_replacing_var: forall E U T X Y,
    WF (X ~ bind_sub U ++E) (open_tt T X) ->
    X \notin fv_tt T \u {{Y}} ->
    WF (Y ~ bind_sub U ++E) (open_tt T Y).
Proof with auto.
  intros.
  rewrite_alist (map (subst_tb X Y) nil ++ [(Y, bind_sub U)] ++ E).
  rewrite subst_tt_intro with (X:=X)...
  apply WF_replacing...
Qed.


Lemma WF_replacing_lb': forall E T U (X Y:atom),
    WF ( X ~ bind_sub_lb U ++E) T ->
    Y <> X ->
    WF ( Y ~ bind_sub_lb U ++E) (subst_tt X Y T).
Proof with auto.
  intros.
  rewrite_alist (map (subst_tb X Y) nil ++ [(Y, bind_sub_lb U)] ++ E).
  apply WF_replacing_lb...
Qed.


Lemma WF_replacing_var_lb: forall E U T X Y,
    WF (X ~ bind_sub_lb U ++E) (open_tt T X) ->
    X \notin fv_tt T \u {{Y}} ->
    WF (Y ~ bind_sub_lb U ++E) (open_tt T Y).
Proof with auto.
  intros.
  rewrite_alist (map (subst_tb X Y) nil ++ [(Y, bind_sub_lb U)] ++ E).
  rewrite subst_tt_intro with (X:=X)...
  apply WF_replacing_lb...
Qed.


Lemma sub_replacing: forall E1 E2 A B U X Y,
    sub (E1++ X ~ bind_sub U ++E2) A B ->
    X <> Y ->
    wf_env (map (subst_tb X Y)  E1 ++ Y ~ bind_sub U ++ E2) ->
    sub (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros;simpl;try solve [rewrite_alist (map (subst_tb X Y) E1 ++ [(Y, bind_sub U)] ++ E2);constructor;auto;apply WF_replacing;auto]...
  -
    destruct (X0==X)...
    constructor... apply WF_var with (U:=U)...
    constructor...
    dependent destruction H0.
    { apply binds_map_free_sub with (S:=Y) in H0...
      apply WF_var with (U:=(subst_tt X Y U0))...
      analyze_binds H0. }
    { apply binds_map_free_sub2 with (S:=Y) in H0... 
      apply WF_var_lb with (U:=(subst_tt X Y U0))...
      analyze_binds H0. }
  -
    destruct (X0==X);subst...
    +
      apply sa_trans_tvar with (U:=subst_tt X Y U0)...
      analyze_binds_uniq H...
      apply uniq_from_wf_env...
      get_well_form...
      inversion BindsTacVal;subst.
      get_well_form.
      apply notin_from_wf_env in H0.
      rewrite <- subst_tt_fresh...
      apply IHsub...
    +
      apply sa_trans_tvar with (U:=subst_tt X Y U0)...
      analyze_binds H.
      *
        unfold binds in *.
        apply In_lemmaL.
        apply binds_map_free...
      *
        assert (Ht:=BindsTac0).
        apply WF_from_binds_typ in Ht...
        apply WF_imply_dom in Ht.
        get_well_form.
        apply notin_from_wf_env in H.
        rewrite <- subst_tt_fresh...
        apply notin_partial with (E2:=dom E2)...
        apply wf_env_cons in H2.
        apply wf_env_cons in H2...
      *
        apply IHsub...

  -
    destruct (X0==X);subst...
    +
      apply sa_trans_tvar_lb with (U:=subst_tt X Y U0)...
      analyze_binds_uniq H...
      apply uniq_from_wf_env...
      get_well_form...
      (* inversion BindsTacVal;subst.
      get_well_form.
      apply notin_from_wf_env in H0.
      rewrite <- subst_tt_fresh... *)
      apply IHsub...
    +
      apply sa_trans_tvar_lb with (U:=subst_tt X Y U0)...
      analyze_binds H.
      *
        unfold binds in *.
        apply In_lemmaL.
        apply binds_map_free_lb...
      *
        assert (Ht:=BindsTac0).
        apply WF_from_binds_typ_lb in Ht...
        apply WF_imply_dom in Ht.
        get_well_form.
        apply notin_from_wf_env in H.
        rewrite <- subst_tt_fresh...
        apply notin_partial with (E2:=dom E2)...
        apply wf_env_cons in H2.
        apply wf_env_cons in H2...
      *
        apply IHsub...
  -
    apply sa_all with (L:=L \u {{X}} \u dom (map (subst_tb X Y) E1 ++ (Y, bind_sub U) :: E2));intros...
    apply IHsub1...
    apply IHsub2...
    rewrite_env (map (subst_tb X Y) (X0~bind_sub S2 ++ E1) ++ (Y, bind_sub U) :: E2).
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    apply H2...
    simpl...
    constructor...
    apply WF_replacing...
    get_well_form...

  -
    apply sa_all_lb with (L:=L \u {{X}} \u dom (map (subst_tb X Y) E1 ++ (Y, bind_sub U) :: E2));intros...
    apply IHsub1...
    apply IHsub2...
    rewrite_env (map (subst_tb X Y) (X0~bind_sub_lb S2 ++ E1) ++ (Y, bind_sub U) :: E2).
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    apply H2...
    simpl...
    constructor...
    apply WF_replacing...
    get_well_form...
  -
    apply sa_rec with (L:=L \u {{X}} \u dom (map (subst_tb X Y) E1 ++ (Y, bind_sub U) :: E2));intros...
    +
      rewrite_env (map (subst_tb X Y) (X0~bind_sub typ_top ++ E1) ++ (Y, bind_sub U) :: E2).
      rewrite subst_tt_open_tt_var...
      apply WF_replacing...
      simpl...
      apply H...
    +
      rewrite_env (map (subst_tb X Y) (X0~bind_sub typ_top ++ E1) ++ (Y, bind_sub U) :: E2).
      rewrite subst_tt_open_tt_var...
      apply WF_replacing...
      simpl...
      apply H0...
    +
      rewrite_env (map (subst_tb X Y) (X0~bind_sub typ_top ++ E1) ++ (Y, bind_sub U) :: E2).
      rewrite <- subst_tt_open_tt_twice...
      rewrite <- subst_tt_open_tt_twice...
      apply H2...
      simpl...
      constructor...
Qed.



Lemma sub_replacing_lb: forall E1 E2 A B U X Y,
    sub (E1++ X ~ bind_sub_lb U ++E2) A B ->
    X <> Y ->
    wf_env (map (subst_tb X Y)  E1 ++ Y ~ bind_sub_lb U ++ E2) ->
    sub (map (subst_tb X Y) E1 ++ Y ~ bind_sub_lb U ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros;simpl;try solve [rewrite_alist (map (subst_tb X Y) E1 ++ [(Y, bind_sub_lb U)] ++ E2);constructor;auto;apply WF_replacing_lb;auto]...
  -
    destruct (X0==X)...
    constructor... apply WF_var_lb with (U:=U)...
    constructor...
    dependent destruction H0.
    { apply binds_map_free_sub_lb2 with (S:=Y) in H0...
      apply WF_var with (U:=(subst_tt X Y U0))...
      analyze_binds H0. }
    { apply binds_map_free_sub_lb with (S:=Y) in H0... 
      apply WF_var_lb with (U:=(subst_tt X Y U0))...
      analyze_binds H0. }
  -
    destruct (X0==X);subst...
    +
      apply sa_trans_tvar with (U:=subst_tt X Y U0)...
      analyze_binds_uniq H...
      apply uniq_from_wf_env...
      get_well_form...
      (* inversion BindsTacVal;subst.
      get_well_form.
      apply notin_from_wf_env in H0.
      rewrite <- subst_tt_fresh... *)
      apply IHsub...
    +
      apply sa_trans_tvar with (U:=subst_tt X Y U0)...
      analyze_binds H.
      *
        unfold binds in *.
        apply In_lemmaL.
        apply binds_map_free...
      *
        assert (Ht:=BindsTac0).
        apply WF_from_binds_typ in Ht...
        apply WF_imply_dom in Ht.
        get_well_form.
        apply notin_from_wf_env_lb in H.
        rewrite <- subst_tt_fresh...
        apply notin_partial with (E2:=dom E2)...
        apply wf_env_cons in H2.
        apply wf_env_cons in H2...
      *
        apply IHsub...


  -
    destruct (X0==X);subst...
    +
      apply sa_trans_tvar_lb with (U:=subst_tt X Y U0)...
      analyze_binds_uniq H...
      apply uniq_from_wf_env...
      get_well_form...
      inversion BindsTacVal;subst.
      get_well_form.
      apply notin_from_wf_env_lb in H0.
      rewrite <- subst_tt_fresh...
      apply IHsub...
    +
      apply sa_trans_tvar_lb with (U:=subst_tt X Y U0)...
      analyze_binds H.
      *
        unfold binds in *.
        apply In_lemmaL.
        apply binds_map_free_lb...
      *
        assert (Ht:=BindsTac0).
        apply WF_from_binds_typ_lb in Ht...
        apply WF_imply_dom in Ht.
        get_well_form.
        apply notin_from_wf_env_lb in H.
        rewrite <- subst_tt_fresh...
        apply notin_partial with (E2:=dom E2)...
        apply wf_env_cons in H2.
        apply wf_env_cons in H2...
      *
        apply IHsub...
  -
    apply sa_all with (L:=L \u {{X}} \u dom (map (subst_tb X Y) E1 ++ (Y, bind_sub U) :: E2));intros...
    apply IHsub1...
    apply IHsub2...
    rewrite_env (map (subst_tb X Y) (X0~bind_sub S2 ++ E1) ++ (Y, bind_sub_lb U) :: E2).
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    apply H2...
    simpl...
    constructor...
    apply WF_replacing_lb...
    get_well_form...

  -
    apply sa_all_lb with (L:=L \u {{X}} \u dom (map (subst_tb X Y) E1 ++ (Y, bind_sub_lb U) :: E2));intros...
    apply IHsub1...
    apply IHsub2...
    rewrite_env (map (subst_tb X Y) (X0~bind_sub_lb S2 ++ E1) ++ (Y, bind_sub_lb U) :: E2).
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    apply H2...
    simpl...
    constructor...
    apply WF_replacing_lb...
    get_well_form...
  -
    apply sa_rec with (L:=L \u {{X}} \u dom (map (subst_tb X Y) E1 ++ (Y, bind_sub_lb U) :: E2));intros...
    +
      rewrite_env (map (subst_tb X Y) (X0~bind_sub typ_top ++ E1) ++ (Y, bind_sub_lb U) :: E2).
      rewrite subst_tt_open_tt_var...
      apply WF_replacing_lb...
      simpl...
      apply H...
    +
      rewrite_env (map (subst_tb X Y) (X0~bind_sub typ_top ++ E1) ++ (Y, bind_sub_lb U) :: E2).
      rewrite subst_tt_open_tt_var...
      apply WF_replacing_lb...
      simpl...
      apply H0...
    +
      rewrite_env (map (subst_tb X Y) (X0~bind_sub typ_top ++ E1) ++ (Y, bind_sub_lb U) :: E2).
      rewrite <- subst_tt_open_tt_twice...
      rewrite <- subst_tt_open_tt_twice...
      apply H2...
      simpl...
      constructor...
Qed.




Lemma sub_replacing': forall E T1 T2 U (X Y:atom),
    sub ( X ~ bind_sub U ++E) T1 T2 ->
    Y <> X ->
    wf_env (Y ~ bind_sub U ++ E) ->
    sub ( Y ~ bind_sub U ++E) (subst_tt X Y T1) (subst_tt X Y T2).
Proof with auto.
  intros.
  rewrite_alist (map (subst_tb X Y) nil ++ [(Y, bind_sub U)] ++ E).
  apply sub_replacing...
Qed.


Lemma sub_replacing_var: forall E2 A B U X Y,
    sub (X ~ bind_sub U ++E2) (open_tt A X) (open_tt B X) ->
    X \notin fv_tt A \u fv_tt B \u {{Y}} ->
    wf_env (Y ~ bind_sub U ++ E2) ->
    sub (Y ~ bind_sub U ++E2) (open_tt A Y) (open_tt B Y).
Proof with auto.
  intros.
  rewrite_alist (map (subst_tb X Y) nil ++ [(Y, bind_sub U)] ++ E2).
  rewrite subst_tt_intro with (X:=X) (T2:=A)...
  rewrite subst_tt_intro with (X:=X) (T2:=B)...
  apply sub_replacing...
Qed.


Lemma sub_replacing_lb': forall E T1 T2 U (X Y:atom),
    sub ( X ~ bind_sub_lb U ++E) T1 T2 ->
    Y <> X ->
    wf_env (Y ~ bind_sub_lb U ++ E) ->
    sub ( Y ~ bind_sub_lb U ++E) (subst_tt X Y T1) (subst_tt X Y T2).
Proof with auto.
  intros.
  rewrite_alist (map (subst_tb X Y) nil ++ [(Y, bind_sub_lb U)] ++ E).
  apply sub_replacing_lb...
Qed.


Lemma sub_replacing_var_lb: forall E2 A B U X Y,
    sub (X ~ bind_sub_lb U ++E2) (open_tt A X) (open_tt B X) ->
    X \notin fv_tt A \u fv_tt B \u {{Y}} ->
    wf_env (Y ~ bind_sub_lb U ++ E2) ->
    sub (Y ~ bind_sub_lb U ++E2) (open_tt A Y) (open_tt B Y).
Proof with auto.
  intros.
  rewrite_alist (map (subst_tb X Y) nil ++ [(Y, bind_sub_lb U)] ++ E2).
  rewrite subst_tt_intro with (X:=X) (T2:=A)...
  rewrite subst_tt_intro with (X:=X) (T2:=B)...
  apply sub_replacing_lb...
Qed.

Lemma label_transform1 : forall X (Y:atom) A Z,
    X \notin fv_tt A ->
    (subst_tt X Y (open_tt A (typ_label Z (open_tt A X)))) =
    (open_tt A (typ_label Z (open_tt A Y))).
Proof with auto.
  intros.
  rewrite  subst_tt_open_tt...
  f_equal...
  rewrite <- subst_tt_fresh...
  simpl.
  f_equal...
  rewrite <- subst_tt_intro...
Qed.

Definition subst_tlb (Z P : atom)  (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_tl Z P T)
  | bind_typ T => bind_typ (subst_tl Z P T)
  | bind_sub_lb T => bind_sub_lb (subst_tl Z P T)
  end.

Lemma WF_from_binds: forall E U X0 X Y,
    binds X0 (bind_sub U) E ->
    WF (map (subst_tlb X Y) E) X0.
Proof with auto.
  induction E;intros...
  analyze_binds H.
  simpl in *.
  destruct a.
  analyze_binds H...
  simpl...
  apply WF_var with (U:=(subst_tl X Y U))...
  rewrite_env (nil ++(a~ subst_tlb X Y b) ++ map (subst_tlb X Y) E).
  apply WF_weakening...
  apply IHE with (U:=U)...
Qed.


Lemma WF_from_binds_lb: forall E U X0 X Y,
    binds X0 (bind_sub_lb U) E ->
    WF (map (subst_tlb X Y) E) X0.
Proof with auto.
  induction E;intros...
  analyze_binds H.
  simpl in *.
  destruct a.
  analyze_binds H...
  simpl...
  apply WF_var_lb with (U:=(subst_tl X Y U))...
  rewrite_env (nil ++(a~ subst_tlb X Y b) ++ map (subst_tlb X Y) E).
  apply WF_weakening...
  apply IHE with (U:=U)...
Qed.

Lemma WF_renaming_tlb: forall E A  X Y,
    WF E A ->
    WF (map (subst_tlb X Y) E) (subst_tl X Y A).
Proof with eauto.
  intros.
  induction H;simpl...
  -
    apply WF_from_binds with (U:=U)...
  -
    apply WF_from_binds_lb with (U:=U)...
  -
    apply WF_all with (L:=L \u {{X}});intros...
    rewrite subst_tl_open_tt_var...
    apply H1...
  -
    apply WF_all_lb with (L:=L \u {{X}});intros...
    rewrite subst_tl_open_tt_var...
    apply H1...
  -
    apply WF_rec with (L:=L \u {{X}});intros...
    rewrite subst_tl_open_tt_var...
    apply H0...
    rewrite subst_tl_open_tt_twice...
    apply H2...
  -
    destruct (X0==X)...
Qed.

Lemma wf_env_tlb: forall E X Y,
    wf_env E ->
    wf_env (map (subst_tlb X Y) E).
Proof with auto.
  induction E;intros...
  destruct a.
  simpl in *...
  destruct b.
  -
    dependent destruction H.
    constructor...
    apply WF_renaming_tlb...
  -
    dependent destruction H.
    constructor...
    apply WF_renaming_tlb...
  -
    dependent destruction H.
    constructor...
    apply WF_renaming_tlb...
Qed.

Lemma binds_map_free_fl_env: forall E X0 U X Y,
    binds X0 (bind_sub U) E ->
    binds X0 (bind_sub (subst_tl X Y U)) (map (subst_tlb X Y) E).
Proof with auto.
  induction E;intros...
  destruct a.
  simpl in *.
  analyze_binds H...
Qed.


Lemma binds_map_free_fl_env_lb: forall E X0 U X Y,
    binds X0 (bind_sub_lb U) E ->
    binds X0 (bind_sub_lb (subst_tl X Y U)) (map (subst_tlb X Y) E).
Proof with auto.
  induction E;intros...
  destruct a.
  simpl in *.
  analyze_binds H...
Qed.

Lemma sub_renaming_tl: forall E A B X Y,
    sub E A B ->
    sub (map (subst_tlb X Y) E) (subst_tl X Y A) (subst_tl X Y B).
Proof with eauto.
  intros.
  dependent induction H;simpl in *...
  -
    constructor...
    apply wf_env_tlb...
  -
    constructor...
    apply wf_env_tlb...
    dependent destruction H0.
    apply WF_from_binds with (U:=U)...
    apply WF_from_binds_lb with (U:=U)...
  -
    constructor...
    apply wf_env_tlb...
    apply WF_renaming_tlb...
  -
    constructor...
    apply wf_env_tlb...
    apply WF_renaming_tlb...
  -    
    apply sa_trans_tvar with (U:=subst_tl X Y U)...
    apply binds_map_free_fl_env...
  -    
    apply sa_trans_tvar_lb with (U:=subst_tl X Y U)...
    apply binds_map_free_fl_env_lb...
  -
    apply sa_all with (L:=L \u {{X}});intros...
    rewrite subst_tl_open_tt_var...
    rewrite subst_tl_open_tt_var...
    apply H2...
  -
    apply sa_all_lb with (L:=L \u {{X}});intros...
    rewrite subst_tl_open_tt_var...
    rewrite subst_tl_open_tt_var...
    apply H2...
  -
    apply sa_rec with (L:=L \u {{X}});intros...
    +
      rewrite subst_tl_open_tt_var...
      rewrite_env (map (subst_tlb X Y) (X0 ~ bind_sub typ_top ++ E)).
      apply WF_renaming_tlb...
      apply H...
    +
      rewrite subst_tl_open_tt_var...
      rewrite_env (map (subst_tlb X Y) (X0 ~ bind_sub typ_top ++ E)).
      apply WF_renaming_tlb...
      apply H0...
    +
      rewrite subst_tl_open_tt_twice...
      rewrite subst_tl_open_tt_twice...
      rewrite_env (map (subst_tlb X Y) (X0 ~ bind_sub typ_top ++ E)).
      apply H2...
  -
    destruct (X0==X);subst...
  -
    apply sa_and_a... eapply WF_renaming_tlb...
  -
    apply sa_and_b... eapply WF_renaming_tlb...
Qed.    


Lemma label_transform4: forall X Y A U,
    X \notin fl_tt A \u fl_tt U ->
    (subst_tl X Y (open_tt A (typ_label X U))) =
    (open_tt A (typ_label Y U)).
Proof with auto.
  intros.
  rewrite <- subst_tl_open_tt...
  f_equal...
  rewrite  subst_tl_fresh...
  simpl.
  destruct (X==X)...
  f_equal.
  rewrite  subst_tl_fresh...
  destruct n...
Qed.

Lemma subst_tlb_fresh : forall E X Y,
    X \notin fl_env E ->
    E = map (subst_tlb X Y) E.
Proof with auto.
  induction E;intros...
  simpl in *.
  destruct a.
  f_equal...
  f_equal...
  destruct b;simpl;f_equal;
  rewrite subst_tl_fresh...
  apply IHE...
  destruct b...
Qed.

Lemma sub_renaming_unfolding: forall  E2 X Y Q A B,
    sub ( X ~ bind_sub Q ++ E2) (open_tt A (typ_label X (open_tt A X))) (open_tt B (typ_label X (open_tt B X))) ->
    Y \notin {{X}} \u fv_tt A \u fl_tt A \u fv_tt B \u fl_tt B ->
    X \notin fv_tt A \u fl_tt A \u fv_tt B \u fl_tt B \u fl_tt Q \u fl_env E2 ->
    wf_env (Y ~ bind_sub Q ++ E2) ->
    sub ( Y ~ bind_sub Q ++ E2) (open_tt A (typ_label Y (open_tt A Y))) (open_tt B (typ_label Y (open_tt B Y))).
Proof with auto.
  intros.
  apply sub_replacing' with (Y:=Y) in H...
  rewrite label_transform1 in H...
  rewrite label_transform1 in H...
  apply sub_renaming_tl with (X:=X) (Y:=Y) in H...
  assert (Q = subst_tl X Y Q).
  rewrite subst_tl_fresh...
  rewrite H3.
  rewrite subst_tlb_fresh with (X:=X) (Y:=Y) (E:=E2)...
  rewrite label_transform4 in H...
  rewrite label_transform4 in H...
  solve_notin.
  solve_notin.
Qed.  
