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
    apply WF_all with (L:=L);intros...
    rewrite_env (((X~ bind_sub T1) ++ F) ++ E)...
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


Lemma wf_rcd_lookup : forall E i T Ti,
  WF E T ->
  Tlookup i T = Some Ti ->
  WF E Ti.
Proof with eauto.
  intros E i T.
  dependent induction T; intros; try solve [inversion H0]...
  - (* RCons *)
    dependent destruction H.
    simpl in *.
    destruct (a==i)...
    inversion H3; subst...
Qed.


Lemma typing_rt_expr_novar : forall E e (X:atom),
  typing E e X -> rt_expr e -> False.
Proof with auto.
  intros.
  dependent induction H;
  try match goal with
  | [H : rt_expr _ |- _] => inversion H
  end.
  - apply sub_tvar_inv in H0. destruct H0. subst.
    apply IHtyping with (X:=x)...
  - subst. apply sub_tvar_inv in H0. destruct H0. subst.
    apply IHtyping with (X:=x)...
Qed.


Lemma typing_collectLabel_inclusion : forall E e T,
  typing E e T -> rt_type T -> rt_expr e ->
  collectLabel T [<=]
  collectLabele e.
Proof with auto.
  intros. induction H;inv_rt;try solve [inversion H1].
  - (* subsumption *)
    destruct H0.
    + simpl. apply AtomSetProperties.subset_empty.
    + dependent destruction H2;inv_rt.
      { apply typing_rt_expr_novar in H... destruct H. }
      rewrite <- IHtyping...
  - (* nil *)
    reflexivity.
  - (* cons *)
    simpl. rewrite IHtyping2... reflexivity.
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
  -
    repeat split...
    apply wf_rcd_lookup with (i:=i) (T:=T)...
  -
    repeat split...
    constructor...
    rewrite typing_collectLabel_inclusion...
    apply H0.
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
    apply typing_tapp with (T1:=T1)...
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
    apply sa_all with (L:=L);intros...
    rewrite_env (((X~ bind_sub S2) ++ F) ++ E)...
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
  -
    apply sa_rcd...
Qed.


Lemma  subst_tt_rt_expr : forall   A B X,
    rt_expr  B ->
    expr A  ->
    expr B ->
    rt_expr  (subst_ee X A B).
Proof with auto.
  intros.
  induction H...
  dependent destruction H1...
  simpl...
Qed.

Ltac get_expr :=
    repeat match goal with
    | [ H : typing _ _ _ |- _ ] => apply typing_regular in H;destruct_hypos   
           end.

Lemma label_choose_reserve_e:
  forall (X : atom) (u : exp) [e : exp],
  expr e -> rt_expr e -> collectLabele e [=] collectLabele (subst_ee X u e).
Proof with auto.
  intros.
  induction H;simpl;try reflexivity...
  + inversion H0.
  + rewrite IHexpr2... reflexivity.
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
    apply typing_tapp with (T1:=T1)...
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
  -
    apply typing_rcd_nil.
    apply wf_env_strengthening in H...
  -
    apply typing_rcd_cons...
    apply subst_tt_rt_expr;get_expr;auto...
    rewrite <- label_choose_reserve_e...
    { apply typing_regular in H0. destruct_hypos... }
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
    +
      inv_rt.
  -
    assert (sub E S (typ_arrow U1 U2)).
    apply sub_transitivity with (Q:=T)...
    assert (typing E (exp_abs S1 e1) (typ_arrow U1 U2)).
    apply typing_sub with (S:=S)...
    dependent destruction H2...
Qed.



Lemma wf_env_subst_tb : forall F Q Z P E,
  wf_env (F ++ Z ~ bind_sub Q ++ E) ->
  WF E P ->
  wf_env (map (subst_tb Z P) F ++ E).
Proof with eauto.
  induction F; intros ;simpl in *...
  -
    dependent destruction H...
  -
    destruct a.
    dependent destruction H;simpl in *.
    +
      constructor...
      apply subst_tb_wf with (Q:=bind_sub Q)...
    +
      constructor...
      apply subst_tb_wf with (Q:=bind_sub Q)...
Qed.      
      


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

      



Lemma rt_expr_step: forall e1 e2,
    rt_expr e1 ->
    step e1 e2 ->
    rt_expr e2.
Proof with auto.
  intros.
  induction H...
  dependent destruction H0...
  dependent destruction H0...
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



Lemma wf_env_binds_not_fv_tt: forall F Z E Q,
    wf_env (F ++ Z ~ bind_sub Q ++ E) ->
    Z \notin fv_tt Q.
Proof with auto.
  intros.
  apply wf_env_cons in H.
  dependent destruction H...
  apply WF_imply_dom in H0...
Qed.  



Lemma union_split: forall A B C,
    union A B [<=] C -> A [<=] C /\ B [<=] C.
Proof with auto.
  intros.
  unfold "[<=]" in *.
  split;intros.
  apply H.
  apply D.F.union_iff...
  apply H.
  apply D.F.union_iff...
Qed.


Lemma label_choose_reserve : forall X A B E,
    WF E B ->
    rt_type B ->
    collectLabel B [=] collectLabel (subst_tt X A B).
Proof with auto.
  intros.
  induction B;simpl;try solve [apply AtomSetProperties.equal_refl]...
  inversion H0.
  dependent destruction H.
  apply KeySetProperties.union_equal_2...
Qed.


Lemma label_equiv_reserve : forall X E A B C D ,
    rt_type A -> rt_type B ->
    collectLabel A [<=] collectLabel B ->
    collectLabel C [=] collectLabel D ->
    WF E A -> WF E B ->
    collectLabel (subst_tt X D A) [<=] collectLabel (subst_tt X C B).
Proof with auto.
  intros.
  induction A; try solve [inversion H].
  -
    induction B; try solve [inversion H0].
    simpl...
    simpl...
    apply KeySetProperties.subset_empty...
  -
    induction B; try solve [inversion H0].
    +
      simpl in *.
      apply union_empty in H1.
      destruct H1.
    +
      simpl in *...
      apply union_split in H1.
      destruct H1.
      apply AtomSetProperties.union_subset_3...
      *
        dependent destruction H4.
        rewrite <- label_choose_reserve with (E:=E)...
      *
        dependent destruction H3.
        apply IHA2...
Qed.



Lemma sub_through_subst_tt: forall Z Q T S F E P,
    sub (F ++ Z ~ bind_sub Q ++ E) T S ->
    sub E P Q ->
    sub (map (subst_tb Z P) F ++ E) (subst_tt Z P T) (subst_tt Z P S).
Proof with auto.
  intros.
  assert (WF E P) as Hq.
    get_well_form...
  dependent induction H;simpl...
  -
    constructor...
    apply wf_env_subst_tb with (Q:=Q)...
  -
    destruct (X==Z);subst...
    apply Reflexivity...
    add_nil.
    apply WF_weakening...
    apply wf_env_subst_tb with (Q:=Q)...
    dependent destruction H0.
    constructor...
    apply wf_env_subst_tb with (Q:=Q)...
    apply WF_var with (U:=subst_tt Z P U)...
    apply binds_map_free_sub with (Q:=Q)...
  -
    constructor...
    apply wf_env_subst_tb with (Q:=Q)...
    apply subst_tb_wf with (Q:=bind_sub Q)...
  -
    destruct (X==Z);subst...
    +
      apply sub_transitivity with (Q:=Q).
      *
        add_nil.
        apply Sub_weakening...
        apply wf_env_subst_tb with (Q:=Q)...
        get_well_form...
      *
        assert (Q = subst_tt Z P Q).
        rewrite <- subst_tt_fresh ...
        get_well_form.
        apply wf_env_binds_not_fv_tt in H0...
        rewrite H2.
        analyze_binds_uniq H...
        apply uniq_from_wf_env...
        get_well_form...
        inversion BindsTacVal;subst.
        apply IHsub with (Q0:=Q)...
    +
      apply sa_trans_tvar with (U:=subst_tt Z P U)...
      apply binds_map_free_sub with (Q:=Q)...
      get_well_form...
      apply IHsub with (Q0:=Q)...
  -
    constructor...
    apply IHsub1 with (Q0:=Q)...
    apply IHsub2 with (Q0:=Q)...
  -
    assert (type P). get_type...
    apply sa_all with (L:=L \u {{Z}});intros...
    { apply IHsub1 with (Q0:=Q)... }
    { apply IHsub2 with (Q0:=Q)... }
    (* apply subst_tb_wf with (Q:=bind_sub Q)... *)
    rewrite_env ( map (subst_tb Z P) (X~bind_sub S2 ++ F) ++ E).
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...    
    apply H2 with (Q0:=Q)...
  -
    assert (type P). get_type...
    apply sa_rec with (L:=L \u {{Z}});intros...
    +
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) (X~bind_sub typ_top ++ F) ++ E).
      apply subst_tb_wf with (Q:=bind_sub Q)...
      apply H...
    +
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) (X~bind_sub typ_top ++ F) ++ E).
      apply subst_tb_wf with (Q:=bind_sub Q)...
      apply H0...
    +
      rewrite <- subst_tt_open_tt_twice...
      rewrite <- subst_tt_open_tt_twice...
      rewrite_env (map (subst_tb Z P) (X~bind_sub typ_top ++ F) ++ E).
      apply H2 with (Q0:=Q)...
  -
    constructor...
    apply IHsub with (Q0:=Q)...
  -
    apply sa_rcd...
    + apply wf_env_subst_tb with (Q:=Q)...
    + apply Infrastructure.subst_tt_rt_type...
      apply WF_type with (E:=E)...
    + apply Infrastructure.subst_tt_rt_type...
      apply WF_type with (E:=E)...
    + apply label_equiv_reserve with (E:=F ++ Z ~ bind_sub Q ++ E)...
      reflexivity.
    + apply subst_tb_wf with (Q:=bind_sub Q)...
    + apply subst_tb_wf with (Q:=bind_sub Q)...
    + intros.
      apply Tlookup_subst in H8...
      2:{ get_type... }
      apply Tlookup_subst in H9...
      2:{ get_type... }
      destruct_hypos. subst.
      apply H6 with (i:=i) (Q0:=Q)... 
Qed.




Lemma subst_te_rt_expr:
  forall A B X,
  rt_expr B -> type A -> expr B -> rt_expr (subst_te X A B).
Proof.
  intros. induction H;simpl...
  + constructor.
  + constructor.
Qed.


Lemma subst_te_collect: forall i X A e,
    i `notin` collectLabele e ->
    rt_expr e ->
    expr e ->
    i `notin` collectLabele (subst_te X A e).
Proof with auto.
  intros.
  induction H1;try solve [inversion H0]...
  simpl in *.
  apply notin_union in H.
  destruct H.
  apply notin_union.
  split...
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
  -
    apply typing_tabs with (L:=L \u {{Z}})...
    intros.
    assert (type P). get_type...
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env ( map (subst_tb Z P) (X~bind_sub V ++ F) ++ E).
    apply H0 with (Q0:=Q)...
  -
    rewrite subst_tt_open_tt...
    apply typing_tapp with (T1:=subst_tt Z P T1)...
    apply sub_through_subst_tt with (Q:=Q)...
    get_type...
  -
    assert (typ_mu (subst_tt Z P A) = subst_tt Z P (typ_mu A)).
    simpl...
    apply typing_fold with (A:=(subst_tt Z P A) )...
    + rewrite H2. apply sub_through_subst_tt with (Q:=Q)...
    + rewrite <- subst_tt_open_tt... get_type...
    (* + rewrite H3.
      apply subst_tb_wf with (Q:=bind_sub Q)...
      get_well_form... *)
  - rewrite subst_tt_open_tt... 2:{ get_type... }
    apply typing_unfold...
    assert (typ_mu (subst_tt Z P T) = subst_tt Z P (typ_mu T))...
    rewrite H2.
    apply sub_through_subst_tt with (Q:=Q)...
  -
    apply typing_sub with (S:=subst_tt Z P S)...
    apply sub_through_subst_tt with (Q:=Q)...
  -
    apply typing_proj with (T:=subst_tt Z P T)...
    apply lookup_some_subst... 
    + apply typing_regular in H. destruct_hypos... get_type...
    + destruct T; try solve[inversion H0]. constructor.
  -
    apply typing_rcd_nil.
    apply wf_env_subst_tb with (Q:=Q)...
    get_well_form...
  -
    apply typing_rcd_cons...
    + apply typing_regular in H0. get_well_form.
      apply subst_tt_rt_type with (E:=F++Z~bind_sub Q ++ E)...
      add_nil. apply WF_weakening. apply WF_weakening...
    + apply subst_te_rt_expr... get_type... get_expr...
    + apply subst_te_collect...
      get_expr...
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
        inversion H1;subst;inv_rt.
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
  inversion H;subst;inv_rt.
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
    inversion H;inv_rt;subst. 
    { inversion H1;inv_rt;subst. inversion H2;inv_rt.  }
    (*  RISK in lower bound? *)
    inversion H2;inv_rt;subst. { inversion H3. }
    apply structural_unfolding_lemma_general...
  -
    specialize (IHtyping T v JMeq_refl eq_refl).
    destruct (IHtyping B) as [A [? ?]]...
    { apply sub_transitivity with (Q:=T0)... }
    destruct_hypos. exists A. repeat split...
    apply sub_transitivity with (Q:=S)...
Qed.

(* Lemma typing_inv_fold: forall S G T v,
    typing G (exp_fold T v) S ->
    forall U, sub G S (typ_mu U) ->
    (exists T', typing G v (open_tt T' (typ_mu T')) /\ sub G (open_tt T' (typ_mu T')) (open_tt U (typ_mu U))).
Proof with auto.
  intros.
  generalize dependent U.
  dependent induction H;intros...
  -
    exists A...
    split...
    apply unfolding_lemma...
  -
    specialize (IHtyping T v).
    assert (exp_fold T v = exp_fold T v) by auto.
    apply IHtyping with (U:=U) in H2...
    apply sub_transitivity with (Q:=T0)...
Qed. *)


(* Lemma typing_inv_fold': forall S G T v,
    typing G (exp_fold T v) S ->
    forall U, sub G S (typ_mu U) ->
    (exists T', typing G v (open_tt T' (typ_mu T')) 
          /\ sub G (open_tt T' (typ_mu T')) (open_tt U (typ_mu U))).
Proof with auto.
  intros.
  generalize dependent U.
  dependent induction H;intros...
  -
    exists A...
    split...
    apply unfolding_lemma...
  -
    specialize (IHtyping T v).
    assert (exp_fold T v = exp_fold T v) by auto.
    apply IHtyping with (U:=U) in H2...
    apply sub_transitivity with (Q:=T0)...
Qed. *)


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
   + pick_fresh X.
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
  + inv_rt.
  - intros.
    pose proof sub_transitivity H0 H1.
    specialize (IHtyping _ _ eq_refl _ _ _ H3 H2)...
Qed.


Lemma rcd_types_match : forall S T E i Ti,
  sub E S T ->
  Tlookup i T = Some Ti ->
  (exists Si, Tlookup i S = Some Si /\ sub E Si Ti) \/
  (exists (X:atom), S = X).
Proof with auto.
  intros. revert Ti H0.
  dependent induction H;intros;simpl in *;try solve [inversion H1|inversion H0|inversion H3]...
  -
    right. exists X...
  -
    induction H1...
    + inversion H7.
    + induction H0...
      * simpl in H2. apply union_empty in H2. exfalso...
      * 
        assert (Ht:=H7).
        apply label_belong in Ht.
        apply label_trans with (B:=collectLabel (typ_rcd_cons i1 T0 T3)) in Ht...
        apply lookup_some in Ht.
        destruct Ht.
        specialize (H5 i x Ti H0 H7)...
        left.
        exists x...
Qed.



Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  typing empty v T ->
  Tlookup i T = Some Ti ->
  exists vi, tlookup i v = Some vi /\ typing empty vi Ti.
Proof with auto.
  intros.
  generalize dependent  Ti.
  dependent induction H0;intros;simpl in *; try solve [inversion H1|inversion H2|inversion H]...
  -
    inversion H0;subst;inversion H2. inv_rt.
  -
    apply rcd_types_match with (i:=i) (Ti:=Ti) in H1...
    destruct H1.
    2:{
      destruct H1. subst. apply typing_regular in H0.
      destruct_hypos. dependent destruction H3. inversion H2. }
    destruct H1.
    destruct H1.
    apply IHtyping with (Ti:= x) in H...
    destruct H.
    destruct H.
    exists x0...
    split...
    apply typing_sub with (S:=x)...
  -
    destruct (i0==i)...
    +
      inversion H3...
      subst...
      exists e1...
    +
      dependent destruction H.
      apply IHtyping2  with (Ti:= Ti) in H0...
Qed. 


Lemma rt_expr_collectLabele: forall e1 e2,
    step e1 e2 -> rt_expr e1 -> expr e1 ->
    collectLabele e2 [<=] collectLabele e1.
Proof with auto.
  intros.
  induction H;simpl;try reflexivity; try apply AtomSetProperties.subset_empty;
  try solve [match goal with
  | [H : rt_expr _ |- _] => inversion H
  end].
  - inversion H1;subst. rewrite IHstep... reflexivity.
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
  
  -
    dependent destruction H1.
    +
      apply lookup_field_in_value with (T:=T) (Ti:=Ti) (i:=i) in H1...
      destruct H1.
      destruct H1.
      rewrite H1 in H2...
      inversion H2...
      subst...
    +
      apply IHtyping in H1...
      apply typing_proj with (T:=T)...

  -
    dependent destruction H4...
    constructor...
    apply rt_expr_step with (e1:=e2)...
    rewrite rt_expr_collectLabele... get_expr...
Qed.
    
    