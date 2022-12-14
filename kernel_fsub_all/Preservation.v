Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export UnfoldingEquiv.

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  WF E U.
Proof with auto.
  induction 1; intros J; analyze_binds J...
  -
    apply IHwf_env in BindsTac...
    add_nil.
    apply WF_weakening...
  -
    apply IHwf_env in BindsTac...
    add_nil.
    apply WF_weakening...
  -
    inversion BindsTacVal;subst.
    add_nil.
    apply WF_weakening...
  -
    apply IHwf_env in BindsTac...
    add_nil.
    apply WF_weakening...
Qed.

Lemma wf_typ_strengthening : forall E F x U T,
 WF (F ++ x ~ bind_typ U ++ E) T ->
 WF (F ++ E) T.
Proof with eauto.
  intros. 
  dependent induction H...
  -
    analyze_binds H...
  -
    analyze_binds H...
  -
    apply WF_all with (L:=L);intros...
    rewrite_env (((X~ bind_sub T1) ++ F) ++ E)...
    apply H1 with (x0:=x) (U0:=U)...
  -
    apply WF_all_lb with (L:=L);intros...
    rewrite_env (((X~ bind_sub_lb T1) ++ F) ++ E)...
    apply H1 with (x0:=x) (U0:=U)...
  -
    apply WF_rec with (L:=L);intros...
    rewrite_alist (([(X, bind_sub typ_top)] ++ F) ++ E).
    apply H0 with (x0:=x) (U0:=U)...
    rewrite_alist (([(X, bind_sub typ_top)] ++ F) ++ E).
    apply H2 with (x0:=x) (U0:=U)...
Qed.

Lemma wf_open_rec: forall A G,
    WF G (typ_mu A) -> WF G (open_tt A (typ_mu A)).
Proof with auto.
  intros.
  dependent destruction H.
  pick fresh X.
  rewrite subst_tt_intro with (X:=X)...
  rewrite_env (map (subst_tb X (typ_mu A)) nil ++ E).
  apply subst_tb_wf with (Q:=bind_sub typ_top)...
  apply H...
  apply WF_rec with (L:=L)...
Qed.

Lemma wf_open_rec2: forall A G T,
    WF G T ->
    WF G (typ_mu A) -> WF G (open_tt A T).
Proof with auto.
  intros.
  dependent destruction H0.
  pick fresh X.
  rewrite subst_tt_intro with (X:=X)...
  rewrite_env (map (subst_tb X T) nil ++ E).
  apply subst_tb_wf with (Q:=bind_sub typ_top)...
  apply H0...
Qed.


Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ expr e /\ WF E T.
Proof with auto.
  intros.
  induction H;destruct_hypos...
  -
    repeat split...
    apply wf_typ_from_binds_typ with (x:=x)...
  -
    pick fresh Y.
    assert (wf_env (Y ~ bind_typ V ++ E)).
    specialize_x_and_L Y L...
    destruct_hypos...
    dependent destruction H1...
    repeat split...
    +
      apply expr_abs with (L:=L)...
      apply WF_type with (E:=E) ...
      intros.
      apply H0...
    +
      constructor...
      specialize_x_and_L Y L...
      destruct_hypos.
      add_nil.
      apply wf_typ_strengthening with (x:=Y) (U:=V)...
  -
    dependent destruction H6.
    repeat split...
  -
    pick fresh Y.
    assert (wf_env (Y ~ bind_sub V ++ E)).
    specialize_x_and_L Y L...
    destruct_hypos...
    dependent destruction H1...
    repeat split...
    +
      apply expr_tabs with (L:=L)...
      apply WF_type with (E:=E) ...
      intros.
      apply H0...
    +
      apply WF_all with (L:=L)...
      intros.
      eapply H0...
  -
    pick fresh Y.
    assert (wf_env (Y ~ bind_sub_lb V ++ E)).
    specialize_x_and_L Y L...
    destruct_hypos...
    dependent destruction H1...
    repeat split...
    +
      apply expr_tabs_lb with (L:=L)...
      apply WF_type with (E:=E) ...
      intros.
      apply H0...
    +
      apply WF_all_lb with (L:=L)...
      intros.
      eapply H0...
  -
    dependent destruction H3.
    repeat split...
    constructor...
    get_type...
    pick fresh X.
    rewrite subst_tt_intro with (X:=X)...
    rewrite_env (map (subst_tb X  T) nil ++ E).
    apply subst_tb_wf with (Q:=bind_sub T1)...
    apply H4...
    get_well_form...
  -
    dependent destruction H3.
    repeat split...
    constructor...
    get_type...
    pick fresh X.
    rewrite subst_tt_intro with (X:=X)...
    rewrite_env (map (subst_tb X  T) nil ++ E).
    apply subst_tb_wf with (Q:=bind_sub_lb T1)...
    apply H4...
    get_well_form...
  -
    get_well_form...
    repeat split...
    constructor...
    apply WF_type with (E:=G)...
  -
    repeat split...
    constructor...
    apply WF_type with (E:=G)...
    apply sub_regular in H0. destruct_hypos.
    apply wf_open_rec2...
  -
    get_well_form.
    repeat split...
Qed.


Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ x ~ bind_typ T ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.


Lemma typing_weakening: forall E1 E2 E3 e T,
    typing (E1 ++ E3) e T ->
    wf_env (E1 ++ E2 ++ E3) ->
    typing (E1 ++ E2 ++ E3) e T.
Proof with simpl_env; eauto.
  intros.
  generalize dependent E2.
  dependent induction H;intros...
  -
    apply typing_abs with (L:=L \u dom E1 \u dom E2 \u dom E3).
    intros.
    rewrite_alist (([(x, bind_typ V)] ++ E1) ++ E2 ++ E3).
    apply H0...
    rewrite_alist ([(x, bind_typ V)] ++ E1 ++ E2 ++ E3).
    constructor...
    specialize_x_and_L x L.
    apply typing_regular in H.
    destruct_hypos.
    apply WF_weakening...
    dependent destruction H...
  -
    apply typing_tabs with (L:=L \u dom E1 \u dom E2 \u dom E3).
    intros.
    rewrite_env ((X ~ bind_sub V ++ E1) ++ E2 ++ E3).
    apply H0...
    rewrite_env (X ~ bind_sub V ++ E1 ++ E2 ++ E3).
    constructor...
    specialize_x_and_L X L.
    apply typing_regular in H.
    destruct_hypos.
    apply WF_weakening...
    dependent destruction H...
  -
    apply typing_tabs_lb with (L:=L \u dom E1 \u dom E2 \u dom E3).
    intros.
    rewrite_env ((X ~ bind_sub_lb V ++ E1) ++ E2 ++ E3).
    apply H0...
    rewrite_env (X ~ bind_sub_lb V ++ E1 ++ E2 ++ E3).
    constructor...
    specialize_x_and_L X L.
    apply typing_regular in H.
    destruct_hypos.
    apply WF_weakening...
    dependent destruction H...
  -
    apply typing_tapp with (T1:=T1)...
    apply Sub_weakening...
  -
    apply typing_tapp_lb with (T1:=T1)...
    apply Sub_weakening...
  -
    apply typing_fold with (A:=A)...
    apply Sub_weakening...
  -
    apply typing_unfold...
    apply Sub_weakening...
  -
    apply typing_sub with (S:=S).
    apply IHtyping...
    apply Sub_weakening...
Qed.

Lemma Sub_typ_strengthening : forall E F x U A B,
 sub (F ++ x ~ bind_typ U ++ E) A B ->
 sub (F ++ E) A B.
Proof with eauto using wf_env_strengthening, wf_typ_strengthening.
  intros. 
  dependent induction H...
  -
    apply sa_trans_tvar with (U:=U0)...
    analyze_binds H...
  -
    apply sa_trans_tvar_lb with (U:=U0)...
    analyze_binds H...
  -
    apply sa_all with (L:=L);intros...
    rewrite_env (((X~ bind_sub S2) ++ F) ++ E)...
    apply H2 with (x0:=x) (U0:=U)...
  -
    apply sa_all_lb with (L:=L);intros...
    rewrite_env (((X~ bind_sub_lb S2) ++ F) ++ E)...
    apply H2 with (x0:=x) (U0:=U)...
  -
    apply sa_rec with (L:=L \u {});intros...
    rewrite_alist (([(X, bind_sub typ_top)] ++ F) ++ E).
    specialize_x_and_L X L.
    eapply wf_typ_strengthening with (x:=x) (U:=U)...
    rewrite_alist (([(X, bind_sub typ_top)] ++ F) ++ E).
    specialize_x_and_L X L.
    eapply wf_typ_strengthening with (x:=x) (U:=U)...
    rewrite_alist (([(X, bind_sub typ_top)] ++ F) ++ E).
    apply H2 with (x0:=x) (U0:=U)...
Qed.


Lemma typing_through_subst_ee : forall F U E x T e u,
  typing (F ++ x ~ bind_typ U ++ E) e T ->
  typing E u U ->
  typing (F ++ E) (subst_ee x u e) T.
Proof with eauto.
  intros.
  generalize dependent u.
  dependent induction H;intros;simpl in *...
  -
    constructor...
    apply wf_env_strengthening in H...
  -
    destruct (x0==x);subst...
    +
      analyze_binds_uniq H0...
      apply uniq_from_wf_env...
      inversion BindsTacVal; subst.
      rewrite_alist (nil ++ F ++ E).
      apply typing_weakening...
      apply wf_env_strengthening in H...
    +
      analyze_binds H0...
      constructor...
      apply wf_env_strengthening in H...
      constructor...
      apply wf_env_strengthening in H...
  -
    apply typing_abs with (L:=L \u {{x}})...
    intros.
    rewrite subst_ee_open_ee_var...
    rewrite_alist (([(x0, bind_typ V)] ++ F) ++ E).
    apply H0 with (U0:=U)...
    apply typing_regular in H1...
    destruct_hypos...
  -
    apply typing_tabs with (L:=L \u {{x}})...
    intros.
    rewrite subst_ee_open_te_var...
    rewrite_alist (([(X, bind_sub V)] ++ F) ++ E).
    apply H0 with (U0:=U)...
    apply typing_regular in H1...
    destruct_hypos...
  -
    apply typing_tabs_lb with (L:=L \u {{x}})...
    intros.
    rewrite subst_ee_open_te_var...
    rewrite_alist (([(X, bind_sub_lb V)] ++ F) ++ E).
    apply H0 with (U0:=U)...
    apply typing_regular in H1...
    destruct_hypos...
  -
    apply typing_tapp with (T1:=T1)...
    eapply Sub_typ_strengthening with (x:=x) (U:=U)...
  -
    apply typing_tapp_lb with (T1:=T1)...
    eapply Sub_typ_strengthening with (x:=x) (U:=U)...
  -
    apply typing_fold with (A:=A)...
    apply Sub_typ_strengthening in H...
  -
    apply typing_unfold...
    apply Sub_typ_strengthening in H0...
  -
    apply typing_sub with (S:=S)...
    apply Sub_typ_strengthening in H0...
Qed.
    

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing (x ~ bind_typ S1 ++ E) (open_ee e1 x) S2 /\ sub E S2 U2.
Proof with auto.
  intros E S1 e1 T Typ.
  dependent induction Typ;intros...
  -
    dependent destruction H1.
    +
      split...
      exists T1. exists L...
  -
    assert (sub E S (typ_arrow U1 U2)).
    apply sub_transitivity with (Q:=T)...
    assert (typing E (exp_abs S1 e1) (typ_arrow U1 U2)).
    apply typing_sub with (S:=S)...
    dependent destruction H2...
Qed.




(* Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (exp_tabs S1 e1) T ->
  forall U1 U2, sub E T (typ_all U1 U2) ->
    sub E U1 S1 /\ sub E S1 U1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing (X ~ bind_sub U1 ++ E) (open_te e1 X) (open_tt S2 X)
     /\ sub (X ~ bind_sub U1 ++ E) (open_tt S2 X) (open_tt U2 X).
Proof with simpl_env; auto.
  intros.
  generalize dependent U1.
  generalize dependent U2.
  dependent induction H;intros...
  -
    dependent destruction H1.
    repeat split...
    exists T1.
    exists (L \u L0)...
    intros. split...

    Search sub.

    Search 
  -
    destruct IHtyping with (U2:=U2) (U1:=U1) (S2:=S1) (e2:=e1)...
    apply sub_transitivity with (Q:=T)...
Qed. *)

Lemma binds_map_free_in_typ: forall F X  Y U  P,
    In (X, bind_typ U) F ->
    X <> Y ->
    In (X, bind_typ (subst_tt Y P U)) (map (subst_tb Y P) F).
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


Lemma binds_map_free_typ: forall E1 E2 X Y U S Q,
    Y \notin {{X}}  ->
    wf_env (E1 ++ (Y, bind_sub Q) :: E2) ->
    binds X (bind_typ U) (E1 ++ (Y, bind_sub Q) :: E2) ->
    binds X (bind_typ (subst_tt Y S U)) (map (subst_tb Y S) E1 ++  E2).
Proof with auto.
  intros.
  analyze_binds H1...
  -
    unfold binds in *.
    apply In_lemmaL.
    apply binds_map_free_in_typ...
  -
    unfold binds in *.
    apply In_lemmaR.
    rewrite <- maps_subst_tb_free with (X:=Y) (U:=S)...
    apply binds_map_free_in_typ...
    apply notin_from_wf_env in H0...
Qed.


Lemma binds_map_free_typ_lb: forall E1 E2 X Y U S Q,
    Y \notin {{X}}  ->
    wf_env (E1 ++ (Y, bind_sub_lb Q) :: E2) ->
    binds X (bind_typ U) (E1 ++ (Y, bind_sub_lb Q) :: E2) ->
    binds X (bind_typ (subst_tt Y S U)) (map (subst_tb Y S) E1 ++  E2).
Proof with auto.
  intros.
  analyze_binds H1...
  -
    unfold binds in *.
    apply In_lemmaL.
    apply binds_map_free_in_typ...
  -
    unfold binds in *.
    apply In_lemmaR.
    rewrite <- maps_subst_tb_free with (X:=Y) (U:=S)...
    apply binds_map_free_in_typ...
    apply notin_from_wf_env_lb in H0...
Qed.


Lemma wf_env_binds_not_fv_tt_lb: forall F Z E Q,
    wf_env (F ++ Z ~ bind_sub_lb Q ++ E) ->
    Z \notin fv_tt Q.
Proof with auto.
  intros.
  apply wf_env_cons in H.
  dependent destruction H...
  apply WF_imply_dom in H0...
Qed. 


Lemma sub_through_subst_tt_lb: forall Z Q T S F E P,
    sub (F ++ Z ~ bind_sub_lb Q ++ E) T S ->
    sub E Q P ->
    sub (map (subst_tb Z P) F ++ E) (subst_tt Z P T) (subst_tt Z P S).
Proof with auto.
  intros.
  assert (WF E P) as Hq.
    get_well_form...
  dependent induction H;simpl...
  -
    constructor...
    apply wf_env_subst_tb_lb with (Q:=Q)...
  -
    destruct (X==Z);subst...
    + apply Reflexivity...
      add_nil.
      apply WF_weakening...
      apply wf_env_subst_tb_lb with (Q:=Q)...
    + dependent destruction H0.
      { constructor...
        apply wf_env_subst_tb_lb with (Q:=Q)...
        apply WF_var with (U:=subst_tt Z P U)...
        apply binds_map_free_sub_lb2 with (Q:=Q)... }
      { constructor...
        apply wf_env_subst_tb_lb with (Q:=Q)...
        apply WF_var_lb with (U:=subst_tt Z P U)...
        apply binds_map_free_sub_lb with (Q:=Q)... }
  -
    constructor...
    apply wf_env_subst_tb_lb with (Q:=Q)...
    apply subst_tb_wf with (Q:=bind_sub_lb Q)...
  -
    constructor...
    apply wf_env_subst_tb_lb with (Q:=Q)...
    apply subst_tb_wf with (Q:=bind_sub_lb Q)...
  -
    destruct (X==Z);subst...
    + apply binds_mid_eq in H...
      inversion H. apply uniq_from_wf_env.
      get_well_form...
    +
      apply sa_trans_tvar with (U:=subst_tt Z P U)...
      apply binds_map_free_sub_lb2 with (Q:=Q)...
      get_well_form...
      apply IHsub with (Q0:=Q)...
  -
    destruct (X==Z);subst...
    +
      apply sub_transitivity with (Q:=Q).
      *
        assert (Q = subst_tt Z P Q).
        rewrite <- subst_tt_fresh ...
        get_well_form.
        apply wf_env_binds_not_fv_tt_lb in H0...
        rewrite H2.
        analyze_binds_uniq H...
        apply uniq_from_wf_env...
        get_well_form...
        inversion BindsTacVal;subst.
        apply IHsub with (Q0:=Q)...
      *
        add_nil.
        apply Sub_weakening...
        apply wf_env_subst_tb_lb with (Q:=Q)...
        get_well_form...
    +
      apply sa_trans_tvar_lb with (U:=subst_tt Z P U)...
      apply binds_map_free_sub_lb with (Q:=Q)...
      get_well_form...
      apply IHsub with (Q0:=Q)...
  -
    constructor...
    apply IHsub1 with (Q0:=Q)...
    apply IHsub2 with (Q0:=Q)...
  -
    assert (type P). get_type...
    apply sa_all with (L:=L \u {{Z}});intros...
    + apply IHsub1 with (Q0:=Q)...
    + apply IHsub2 with (Q0:=Q)...
    (* + apply subst_tb_wf with (Q:=bind_sub Q)... *)
    + rewrite_env ( map (subst_tb Z P) (X~bind_sub S2 ++ F) ++ E).
      rewrite subst_tt_open_tt_var...
      rewrite subst_tt_open_tt_var...
      apply H2 with (Q0:=Q)...
  -
    assert (type P). get_type...
    apply sa_all_lb with (L:=L \u {{Z}});intros...
    + apply IHsub1 with (Q0:=Q)...
    + apply IHsub2 with (Q0:=Q)...
    (* + apply subst_tb_wf with (Q:=bind_sub Q)... *)
    + rewrite_env ( map (subst_tb Z P) (X~bind_sub_lb S2 ++ F) ++ E).
      rewrite subst_tt_open_tt_var...
      rewrite subst_tt_open_tt_var...
      apply H2 with (Q0:=Q)...
  -
    assert (type P). get_type...
    apply sa_rec with (L:=L \u {{Z}});intros...
    +
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) (X~bind_sub typ_top ++ F) ++ E).
      apply subst_tb_wf with (Q:=bind_sub_lb Q)...
      apply H...
    +
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) (X~bind_sub typ_top ++ F) ++ E).
      apply subst_tb_wf with (Q:=bind_sub_lb Q)...
      apply H0...
    +
      rewrite <- subst_tt_open_tt_twice...
      rewrite <- subst_tt_open_tt_twice...
      rewrite_env (map (subst_tb Z P) (X~bind_sub typ_top ++ F) ++ E).
      apply H2 with (Q0:=Q)...
  -
    constructor...
    apply IHsub with (Q0:=Q)...
  (* -
    apply sa_rcd...
    +
      apply wf_env_subst_tb with (Q:=Q)...
    +
      apply subst_tt_rt_type with (E:=F ++ Z ~ bind_sub Q ++ E)...
      add_nil. apply WF_weakening... apply WF_weakening...
    +
      apply subst_tt_rt_type with (E:=F ++ Z ~ bind_sub Q ++ E)...
      add_nil. apply WF_weakening... apply WF_weakening...
    +
      apply label_equiv_reserve with (E:=F ++ Z ~ bind_sub Q ++ E)...
      reflexivity.
    +
      apply subst_tb_wf with (Q:=bind_sub Q)...
    +
      apply subst_tb_wf with (Q:=bind_sub Q)...
    +
      intros. apply Tlookup_subst with (E:=(F ++ Z ~ bind_sub Q ++ E) )in H8 ...
      apply Tlookup_subst with (E:=(F ++ Z ~ bind_sub Q ++ E) )in H9...
      destruct_hypos. subst.
      apply H6 with (i:=i) (Q0:=Q)... *)
Qed.



Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (F ++ Z ~ bind_sub Q ++ E) e T ->
  sub E P Q ->
  typing (map (subst_tb Z P) F ++ E) (subst_te Z P e) (subst_tt Z P T).
Proof with eauto.
  intros.
  generalize dependent P.
  dependent induction H;intros;simpl...
  -
    constructor...
    apply wf_env_subst_tb with (Q:=Q)...
    get_well_form...
  -
    constructor...
    apply wf_env_subst_tb with (Q:=Q)...
    get_well_form...
    apply binds_map_free_typ with (Q:=Q)...
    analyze_binds_uniq  H0...
    apply uniq_from_wf_env...
  -
    apply typing_abs with (L:=L)...
    intros.
    rewrite subst_te_open_ee_var...
    rewrite_env ( map (subst_tb Z P) (x~bind_typ V ++ F) ++ E).
    apply H0 with (Q0:=Q)...
  (* - econstructor. 2:{ eapply IHtyping2 in H1. apply H1. auto. }
    { eapply IHtyping1 in H1. apply H1. auto. } *)
  -
    apply typing_tabs with (L:=L \u {{Z}})...
    intros.
    assert (type P). get_type...
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env ( map (subst_tb Z P) (X~bind_sub V ++ F) ++ E).
    apply H0 with (Q0:=Q)...
  -
    apply typing_tabs_lb with (L:=L \u {{Z}})...
    intros.
    assert (type P). get_type...
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env ( map (subst_tb Z P) (X~bind_sub_lb V ++ F) ++ E).
    apply H0 with (Q0:=Q)...
  -
    rewrite subst_tt_open_tt...
    apply typing_tapp with (T1:=subst_tt Z P T1)...
    apply sub_through_subst_tt with (Q:=Q)...
    get_type...
  -
    rewrite subst_tt_open_tt...
    apply typing_tapp_lb with (T1:=subst_tt Z P T1)...
    apply sub_through_subst_tt with (Q:=Q)...
    get_type...
  -
    assert (typ_mu (subst_tt Z P A) = subst_tt Z P (typ_mu A)).
    simpl...
    apply typing_fold with (A:=(subst_tt Z P A) )...
    + rewrite H2. apply sub_through_subst_tt with (Q:=Q)...
    + rewrite <- subst_tt_open_tt... get_type...
  -
    rewrite subst_tt_open_tt...
    apply typing_unfold...
    2:{ get_type... }
    assert (typ_mu (subst_tt Z P T) = subst_tt Z P (typ_mu T))...
    rewrite H2.
    apply sub_through_subst_tt with (Q:=Q)...
  -
    apply typing_sub with (S:=subst_tt Z P S)...
    apply sub_through_subst_tt with (Q:=Q)...
Qed.



Lemma structural_unfolding_lemma_general: forall A B C D,
  sub empty (typ_mu A) (typ_mu B) ->
  sub empty (typ_mu B) (typ_mu C) ->
  sub empty (typ_mu C) (typ_mu D) ->
  sub empty (open_tt A (typ_mu B)) (open_tt D (typ_mu C)).
Proof with auto.
  intros.
  apply sub_transitivity with (Q:=open_tt B (typ_mu B))...
  2:{ apply sub_transitivity with (Q:=open_tt C (typ_mu C))...
      { apply unfolding_lemma... }
        inversion H1;subst.
        assert ( forall X : atom,
          X `notin` L \u (fv_tt C)->
          sub (X ~ bind_sub typ_top ++ empty) (open_tt C X)
            (open_tt D X)
        ).
        { intros. pick_fresh X0. specialize_x_and_L X0 L.
          apply sub_nominal_inversion in H7...
          rewrite_env (empty ++ X ~ bind_sub typ_top ++ empty).
          apply sub_replacing_var with (X:=X0)... }
        pick_fresh X0.
        replace ((open_tt C (typ_mu C))) with
        (subst_tt X0 (typ_mu C) (open_tt C X0)).
        2:{ rewrite subst_tt_open_tt...
            simpl. rewrite eq_dec_refl.
            f_equal...  rewrite <- subst_tt_fresh...
            apply WF_type with (E:=nil).
            get_well_form... }
        replace ((open_tt D (typ_mu C))) with
        (subst_tt X0 (typ_mu C) (open_tt D X0)).
        2:{ rewrite subst_tt_open_tt...
            simpl. rewrite eq_dec_refl.
            f_equal...  rewrite <- subst_tt_fresh... 
            apply WF_type with (E:=nil).
            get_well_form... }
        rewrite_env (map (subst_tb X0 (typ_mu C)) nil ++ empty).
        apply sub_through_subst_tt with (Q:= typ_top)...
        { apply H2... }
        apply sub_regular in H0. destruct_hypos.
        apply sa_top...
  }
  inversion H;subst.
  assert ( forall X : atom,
    X `notin` L \u (fv_tt A)->
    sub (X ~ bind_sub typ_top ++ empty) (open_tt A X)
      (open_tt B X)
  ).
  { intros. pick_fresh X0. specialize_x_and_L X0 L.
    apply sub_nominal_inversion in H7...
    rewrite_env (empty ++ X ~ bind_sub typ_top ++ empty).
    apply sub_replacing_var with (X:=X0)... }
  pick_fresh X0.
  replace ((open_tt A (typ_mu B))) with
  (subst_tt X0 (typ_mu B) (open_tt A X0)).
  2:{ rewrite subst_tt_open_tt...
      simpl. rewrite eq_dec_refl.
      f_equal...  rewrite <- subst_tt_fresh...
      apply WF_type with (E:=nil).
      get_well_form... }
  replace ((open_tt B (typ_mu B))) with
  (subst_tt X0 (typ_mu B) (open_tt B X0)).
  2:{ rewrite subst_tt_open_tt...
      simpl. rewrite eq_dec_refl.
      f_equal...  rewrite <- subst_tt_fresh... 
      apply WF_type with (E:=nil).
      get_well_form... }
  rewrite_env (map (subst_tb X0 (typ_mu B)) nil ++ empty).
  apply sub_through_subst_tt with (Q:= typ_top)...
  { apply H2... }
  apply sub_regular in H0. destruct_hypos.
  apply sa_top...
Qed.




Lemma typing_inv_fold0: forall T v C B',
typing empty (exp_fold T v) B' ->
forall B, sub empty B' B ->
sub empty B (typ_mu C) ->
exists A, sub empty (typ_mu A) B' /\
(typing empty v 
(* (open_tt A B') 
  /\ sub empty (open_tt A B')  *)
  (open_tt C B)).
Proof with auto.
  intros.
  generalize dependent B.
  dependent induction H;intros...
  -
    clear IHtyping.
    exists A... repeat split...
    eapply typing_sub with (S:= open_tt A T)...
    inversion H;subst. 
    { inversion H1;subst. inversion H2. inversion H5... }
    { inversion H3. }
    inversion H2;subst.
    { inversion H1. }
    { inversion H3. }
    apply structural_unfolding_lemma_general...
  -
    specialize (IHtyping T v JMeq_refl eq_refl).
    destruct (IHtyping B) as [A [? ?]]...
    { apply sub_transitivity with (Q:=T0)... }
    destruct_hypos. exists A. repeat split...
    apply sub_transitivity with (Q:=S)...
Qed.

Lemma typing_through_subst_te_lb : forall Q E F Z e T P,
  typing (F ++ Z ~ bind_sub_lb Q ++ E) e T ->
  sub E Q P ->
  typing (map (subst_tb Z P) F ++ E) (subst_te Z P e) (subst_tt Z P T).
Proof with eauto.
  intros.
  generalize dependent P.
  dependent induction H;intros;simpl...
  -
    constructor...
    apply wf_env_subst_tb_lb with (Q:=Q)...
    get_well_form...
  -
    constructor...
    apply wf_env_subst_tb_lb with (Q:=Q)...
    get_well_form...
    apply binds_map_free_typ_lb with (Q:=Q)...
    analyze_binds_uniq  H0...
    apply uniq_from_wf_env...
  -
    apply typing_abs with (L:=L)...
    intros.
    rewrite subst_te_open_ee_var...
    rewrite_env ( map (subst_tb Z P) (x~bind_typ V ++ F) ++ E).
    apply H0 with (Q0:=Q)...
  (* - econstructor. 2:{ eapply IHtyping2 in H1. apply H1. auto. }
    { eapply IHtyping1 in H1. apply H1. auto. } *)
  -
    apply typing_tabs with (L:=L \u {{Z}})...
    intros.
    assert (type P). get_type...
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env ( map (subst_tb Z P) (X~bind_sub V ++ F) ++ E).
    apply H0 with (Q0:=Q)...
  -
    apply typing_tabs_lb with (L:=L \u {{Z}})...
    intros.
    assert (type P). get_type...
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env ( map (subst_tb Z P) (X~bind_sub_lb V ++ F) ++ E).
    apply H0 with (Q0:=Q)...
  -
    rewrite subst_tt_open_tt...
    apply typing_tapp with (T1:=subst_tt Z P T1)...
    apply sub_through_subst_tt_lb with (Q:=Q)...
    get_type...
  -
    rewrite subst_tt_open_tt...
    apply typing_tapp_lb with (T1:=subst_tt Z P T1)...
    apply sub_through_subst_tt_lb with (Q:=Q)...
    get_type...
  -
    assert (typ_mu (subst_tt Z P A) = subst_tt Z P (typ_mu A)).
    simpl...
    apply typing_fold with (A:=(subst_tt Z P A) )...
    + rewrite H2. apply sub_through_subst_tt_lb with (Q:=Q)...
    + rewrite <- subst_tt_open_tt... get_type...

  -
    rewrite subst_tt_open_tt...
    apply typing_unfold...
    2:{ get_type... }
    assert (typ_mu (subst_tt Z P T) = subst_tt Z P (typ_mu T))...
    rewrite H2.
    apply sub_through_subst_tt_lb with (Q:=Q)...
  -
    apply typing_sub with (S:=subst_tt Z P S)...
    apply sub_through_subst_tt_lb with (Q:=Q)...
Qed.


Lemma typing_inv_tabs : forall E S1 e1 T,
typing E (exp_tabs S1 e1) T ->
forall U1 U2 S, sub E T (typ_all U1 U2) -> sub E S U1 ->
(* exists L, forall X, X `notin` L -> *)
  typing (E) (open_te e1 S) (open_tt U2 S).
Proof with auto.
  intros E S1 e1 T H.
  dependent induction H.
  - intros.
   dependent destruction H1.
   pick_fresh X.
     (* exists (L \u L0 \u fv_te e1 \u fv_tt U2). intros. *)
    (* specialize (H X). *)
    rewrite_env (map (subst_tb X S) nil ++ E).
    rewrite subst_te_intro with (X:= X)...
    rewrite subst_tt_intro with (X:= X)...
    apply typing_through_subst_te with (Q:=S1)...
    { specialize_x_and_L X L.
      apply typing_sub with (open_tt T1 X)...
      apply sub_narrowing with (Q:= U1)...
      apply H1... }
    { apply sub_transitivity with (Q:= U1)... }
  - intros.
    pose proof sub_transitivity H0 H1.
    specialize (IHtyping _ _ eq_refl _ _ _ H3 H2)...
Qed.

Lemma typing_inv_tabs_lb : forall E S1 e1 T,
typing E (exp_tabs_lb S1 e1) T ->
forall U1 U2 S, sub E T (typ_all_lb U1 U2) -> sub E U1 S ->
(* exists L, forall X, X `notin` L -> *)
  typing (E) (open_te e1 S) (open_tt U2 S).
Proof with auto.
  intros E S1 e1 T H.
  dependent induction H.
  - intros.
   dependent destruction H1.
   pick_fresh X.
     (* exists (L \u L0 \u fv_te e1 \u fv_tt U2). intros. *)
    (* specialize (H X). *)
    rewrite_env (map (subst_tb X S) nil ++ E).
    rewrite subst_te_intro with (X:= X)...
    rewrite subst_tt_intro with (X:= X)...
    apply typing_through_subst_te_lb with (Q:=S1)...
    { specialize_x_and_L X L.
      apply typing_sub with (open_tt T1 X)...
      apply sub_narrowing_lb with (Q:= U1)...
      apply H1... }
    { apply sub_transitivity with (Q:= U1)... }
  - intros.
    pose proof sub_transitivity H0 H1.
    specialize (IHtyping _ _ eq_refl _ _ _ H3 H2)...
Qed.



Lemma bot_uninhabited: forall v,
  value v -> 
  ~ typing empty v typ_bot.
Proof with auto.
  intros.
  intros C. dependent induction C;try solve [inversion H0];
    try solve [inversion H;subst;auto]...
  inversion H0;subst...
Qed.

Lemma typing_tapp_ub_lb_false: forall e T0 T1 T2,
  typing empty (exp_tabs_lb T0 e) (typ_all T1 T2) -> False.
Proof with auto.
  intros.
  dependent induction H...
  dependent induction H0... 
  { apply bot_uninhabited in H... constructor... apply typing_regular in H. destruct_hypos... }
  apply IHtyping with (e0:=e) (T1:=T0) (T2:=S1) (T4:=T3)...
Qed.


Lemma typing_tapp_lb_ub_false: forall e T0 T1 T2,
  typing empty (exp_tabs T0 e) (typ_all_lb T1 T2) -> False.
Proof with auto.
  intros.
  dependent induction H...
  dependent induction H0...
  { apply bot_uninhabited in H... constructor... apply typing_regular in H. destruct_hypos... }
  apply IHtyping with (e0:=e) (T1:=T0) (T2:=S1) (T4:=T3)...
Qed.



Lemma preservation : forall e e' T,
    typing nil e T ->
    step e e' ->
    typing nil e' T.
Proof with auto.
  intros.
  generalize dependent e'.
  dependent induction H;intros;try solve [dependent destruction H1;auto|inversion H0]...
  -
    dependent destruction H1...
    +
      dependent destruction H.
      *
        pick fresh Y.
        rewrite subst_ee_intro with (x:=Y)...
        rewrite_env (empty ++ empty).
        apply typing_through_subst_ee with (U:=T1)...
        apply H...
      *
        apply typing_inv_abs with (U1:=T1) (U2:=T2) in H...
        destruct_hypos.
        pick fresh Y.
        rewrite subst_ee_intro with (x:=Y)...
        rewrite_env (empty ++ empty).
        apply typing_through_subst_ee with (U:=T)...
        specialize_x_and_L Y x0.
        destruct_hypos.
        apply typing_sub with (S:=x)...
        apply Sub_weakening...
        constructor...
        get_well_form...
        (* apply typing_regular in H4... *)
        destruct_hypos...
        (* dependent destruction H4... *)
        apply typing_sub with (S:=T1)...
    +
      apply typing_app with (T1:=T1)...
    +
      apply typing_app with (T1:=T1)...
  -
    dependent destruction H1...
    +
      apply typing_tapp with (T1:=T1)...
    +
      dependent destruction H...
      *
        pick fresh X.
        rewrite subst_te_intro with (X:=X)...
        rewrite subst_tt_intro with (X:=X)...
        rewrite_alist (map (subst_tb X T) nil ++ empty).
        apply typing_through_subst_te with (Q:=T1)...
        apply H...
      *


      (* 

      
      /\X<:S1. e1 <: T <: ALL U1. U2
      T0 <: U1

      e1 [X |-> T0] : U2 [X |-> T0]
      
      *)
        apply typing_inv_tabs with (U1:=T1) (U2:=T2) (S:=T) in H...
        (* destruct H as [L ?]. pick_fresh X. 
        destruct_hypos.
        pick fresh X.
        rewrite subst_te_intro with (X:=X)...
        rewrite subst_tt_intro with (X:=X)...
        rewrite_alist (map (subst_tb X T) nil ++ empty).
        apply typing_through_subst_te with (Q:=T1)...
        specialize_x_and_L X x0.
        destruct_hypos.
        apply typing_sub with (S:=open_tt x X)... *)
    +
      apply typing_tapp_ub_lb_false in H. destruct H.
  -
    dependent destruction H1...
    +
      apply typing_tapp_lb with (T1:=T1)...
    +
      apply typing_tapp_lb_ub_false in H. destruct H.
    +
      dependent destruction H...
      *
        pick fresh X.
        rewrite subst_te_intro with (X:=X)...
        rewrite subst_tt_intro with (X:=X)...
        rewrite_alist (map (subst_tb X T) nil ++ empty).
        apply typing_through_subst_te_lb with (Q:=T1)...
        apply H...
      *
        apply typing_inv_tabs_lb with (U1:=T1) (U2:=T2) (S:=T) in H...

  -
    dependent destruction H1...
    apply typing_fold with (A:=A)...
  -

    dependent destruction H1...
    eapply typing_inv_fold0 with (C:=T) (B:=A) in H...
    destruct_hypos...
    apply Reflexivity... get_well_form...


  -
    apply typing_sub with (S:=S)...

Qed.

    
    