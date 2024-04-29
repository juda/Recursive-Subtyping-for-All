Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Backward.

Lemma open_tt_var_rev: forall A B (X:atom),
    X \notin fv_tt A \u fv_tt B ->
    open_tt A X = open_tt B X ->
    A = B.
Proof with auto.
  unfold open_tt.
  generalize 0.
  intros n A B.
  generalize dependent n.
  generalize dependent B.
  induction A;induction B;intros;simpl in *;try solve [inversion H0|destruct (n0==n);subst;inversion H0]...
  -
    destruct (n1==n);destruct (n1==n0);subst...
    inversion H0.
    inversion H0.
  -
    destruct (n0==n);subst...
    inversion H0.
    rewrite <- H2 in H.
    solve_notin_self X.
  -
    destruct (n0==n);subst...
    inversion H0.
    rewrite  H2 in H.
    solve_notin_self X.
  -
    inversion H0.
    apply IHA1 in H2...
    apply IHA2 in H3...
    subst...
  -
    inversion H0.
    apply IHA1 in H2...
    apply IHA2 in H3...
    subst...
  -
    inversion H0.
    apply IHA in H2...
    subst...
  -
    inversion H0.
    apply IHA in H3...
    subst...
Qed.

Lemma binds_split: forall E X U,
    binds X (bind_sub U) E ->
    exists E1 E2,
      E = E1 ++ X~(bind_sub U) ++ E2.
Proof with auto.
  induction E;intros...
  analyze_binds H.
  destruct a.
  analyze_binds H.
  -
    exists nil.
    exists E...
  -
    apply IHE in BindsTac...
    destruct_hypos.
    rewrite H.
    exists ((a,b)::x).
    exists x0...
Qed.

Inductive sub_tvar_chain : env -> env -> atom -> atom -> Prop :=
| sub_tvar_refl: forall E U X, 
    wf_env E -> binds X (bind_sub U) E ->
    sub_tvar_chain E (X ~ bind_sub U) X X
| sub_tvar_cons: forall E1 E2 W (X1 X2 X3:atom),
    wf_env (E1 ++ X1 ~ bind_sub X2 ++ E2) ->
    sub_tvar_chain (E1 ++ X1 ~ bind_sub X2 ++ E2) W X2 X3 ->
    sub_tvar_chain 
      (E1 ++ X1 ~ bind_sub X2 ++ E2) 
      (X1 ~ bind_sub X2 ++ W) X1 X3.

Lemma sub_tvar_chain_subset: forall E W X Y,
  sub_tvar_chain E W X Y ->
  forall K V, binds K V W -> binds K V E.
Proof with auto.
  intros. induction H.
  - inversion H0. { inversion H2;subst... }
    inversion H2.
  - destruct H0...
    inversion H0...
Qed.

Lemma sub_tvar_chain_strengthening: forall Z U W E2 X Y,
  sub_tvar_chain (Z ~ U ++ E2) W X Y ->
  Z \notin dom W ->
  sub_tvar_chain (E2) W X Y.
Proof with auto.
  intros. dependent induction H.
  - apply sub_tvar_refl with (U:=U0)... 
    { apply wf_env_cons in H... }
    { destruct H0... inversion H0. subst.
      exfalso. apply H1. simpl... }
  - destruct E1.
    { inversion x;subst. exfalso.
      apply H1. simpl... }
    { inversion x;subst.
      specialize (IHsub_tvar_chain Z U (E1 ++ X1 ~ bind_sub X2 ++ E0) JMeq_refl).
      eapply sub_tvar_cons...
      rewrite <- app_comm_cons  in H.
      rewrite cons_app_one in H. apply wf_env_cons in H...
    } 
Qed.
Lemma binds_uniq: forall E X A B,
    wf_env E ->
    binds X (bind_sub A) E ->
    binds X (bind_sub B) E ->
    A = B.
Proof with auto.
  induction E;intros...
  analyze_binds H0.
  destruct a.
  analyze_binds_uniq H0.
  -
    apply uniq_from_wf_env...
  -
    analyze_binds_uniq H1...
    inversion BindsTacVal...
  -
    analyze_binds_uniq H1...
    apply IHE with (X:=X)...
    dependent destruction H...
Qed.
Lemma sub_tvar_inv:forall E U (X:atom),
    sub E U X ->
    exists Y, U = typ_fvar Y.
Proof with auto.
  intros.
  dependent induction H...
  exists X...
  exists X0...
Qed.
Lemma sub_tvar_next_fvar: forall (X X0:atom) E1 E2 U,
   wf_env (E1 ++ [(X, bind_sub U)] ++ E2) ->
   sub (E1 ++ [(X, bind_sub U)] ++ E2) X X0 ->
   X <> X0 ->
   exists Y, U = typ_fvar Y.
Proof with auto.
  intros. dependent destruction H0.
  - exfalso...
  - destruct (sub_tvar_inv H1) as [X' Et]. subst U0.
    assert (binds X (bind_sub U) (E1 ++ [(X, bind_sub U)] ++ E2)) by auto. pose proof binds_uniq _ _ _ H H0 H3. subst U.
    exists X'...
Qed.
  
Lemma suba_sub_tvar_chain: forall E (X1 X2:atom),
    sub E X1 X2 ->
    exists W, sub_tvar_chain E W X1 X2.
Proof with auto.
  intros.
  dependent induction H.
  - inversion H0;subst.
    exists (X2 ~ bind_sub U).
    apply sub_tvar_refl with (U:=U)...
  - pose proof sub_regular H0. destruct_hypos.
    pose proof binds_split _ _ _ H.
    destruct H4 as [E1 [E2 H4]].
    pose proof sub_tvar_inv  H0. destruct H5 as [X' H5]. subst U.
    specialize (IHsub X' X2 eq_refl eq_refl).
    destruct IHsub as [W IHsub].
    subst E. exists (X1 ~ bind_sub X' ++ W).
    eapply sub_tvar_cons with (E2:=E2) (X2:=X')...
Qed.


Inductive sub_env: env -> env -> Prop :=
| sub_env_nil : forall E, sub_env E empty
| sub_env_cons_some : forall E W K V,
    sub_env E W ->
    sub_env (K ~ V ++ E) (K ~ V ++ W)
| sub_env_cons_none : forall E W K V,
    sub_env E W ->
    sub_env (K ~ V ++ E) W.

Lemma sub_env_app: forall E1 E2 W,
    sub_env E2 W ->
    sub_env (E1 ++ E2) W.
Proof. intros E1.
  induction E1;intros...
  - apply H.
  - simpl. rewrite cons_app_one.
    destruct a. apply sub_env_cons_none.
    apply IHE1. auto.
Qed.

Lemma WF_from_binds_typ_strong: 
forall (x : atom) (U : typ) (E1 E2 : env),
  wf_env (E1 ++ [(x, bind_sub U)] ++ E2) -> 
  WF E2 U.
Proof with auto.
intros.
dependent induction H.
-
  destruct E1;inversion x.
-
  destruct E1;inversion x;subst...
  specialize (IHwf_env _ _ _ _ JMeq_refl)...
-
  destruct E1;inversion x;subst...
  specialize (IHwf_env _ _ _ _ JMeq_refl)...
Qed.

Lemma sub_env_clos: forall E W,
  sub_env E W ->
  forall X, X `in` dom W -> X `in` dom E.
Proof with auto.
  intros E W H.
  induction H;intros;simpl in*...
  - apply empty_iff in H. exfalso...
  - rewrite KeySetProperties.add_union_singleton in *.
    apply union_iff. apply union_iff in H0.
    destruct H0...
Qed.


Lemma sub_env_cut_head:
  forall  E2 X1 X2 T1 T2 W, 
  X1 <> X2 ->
  sub_env (X1 ~ T1 ++ E2) (X2 ~ T2 ++ W) ->
  sub_env E2 (X2 ~ T2 ++ W).
Proof with auto.
  intros.
  inversion H0;subst...
  exfalso...
Qed.

Lemma sub_env_cut_heads:
  forall E1 E2 X T W, uniq (E1 ++ X ~ T ++ E2) ->
  sub_env (E1 ++ X ~ T ++ E2) (X ~ T ++ W) ->
  sub_env E2 W.
Proof with auto.
  intros E1. induction E1...
  - intros. inversion H0;subst...
    pose proof sub_env_clos H5.
    apply uniq_cons_2 in H.
    exfalso. apply H. simpl. apply H1. simpl...
  - intros.  destruct a as [X' T'].
    simpl in H0. rewrite cons_app_one in H0.
    apply sub_env_cut_head in H0.
    2:{ apply uniq_cons_2 in H... }
    inversion H;subst.
    apply IHE1 with (X:=X) (T:=T)...
Qed.

Lemma uniq_split_eq: forall (E1 E2 E1' E2':env) (X:atom) (T T':binding),
  uniq (E1 ++ X ~ T ++ E2) ->
  E1 ++ X ~ T ++ E2 = E1' ++ X ~ T' ++ E2' ->
  E1 = E1' /\ T = T' /\ E2 = E2'.
Proof with auto.
  intros E1.
  induction E1;intros.
  - destruct E1'.
    { inversion H0... }
    destruct p. inversion H0;subst.
    apply uniq_cons_2 in H. exfalso...
    rewrite dom_app in H. simpl in H...
  - destruct E1'.
    { inversion H0. destruct a. inversion H2;subst.
      apply uniq_cons_2 in H. exfalso...
      rewrite dom_app in H. simpl in H... }
    inversion H0;subst.
    inversion H;subst.
    specialize (IHE1 _ _ _ _ _ _ H4 H3).
    destruct_hypos;subst...
Qed.

Lemma binds_uniq': forall X U T E1 E2,
  wf_env (E1 ++ [(X, bind_sub T)] ++ E2) ->
  binds X (bind_sub U) (E1 ++ [(X, bind_sub T)] ++ E2) ->
  U = T.
Proof.
  intros.
  assert (binds X (bind_sub T) (E1 ++ [(X, bind_sub T)] ++ E2)) by auto.
  pose proof binds_uniq _ _ _ H H0 H1...
  auto.
Qed.

Lemma sub_tvar_chain_sub_env: forall E W X Y,
  sub_tvar_chain E W X Y -> 
  sub_env E W.
Proof with auto.
  intros. dependent induction H;intros...
  - apply binds_split in H0. destruct H0 as [E1 [E2 H0]].
    rewrite H0. apply sub_env_app.
    apply sub_env_cons_some. apply sub_env_nil.
  - pose proof WF_from_binds_typ_strong _ _ _ _ H.
    inversion H1;subst. apply binds_split in H4.
    destruct H4 as [E3 [E4 H5]]. subst E2.
    apply sub_env_app.
    apply sub_env_cons_some.
    apply sub_env_app.
    inversion H0;subst.
    { rewrite <- app_assoc in H3.
      rewrite <- app_assoc in H3. apply binds_uniq' in H3.
      2:{ rewrite !app_assoc... }
      subst U0. apply sub_env_cons_some. apply sub_env_nil. }
    { rewrite <- app_assoc in IHsub_tvar_chain.
      rewrite <- app_assoc in IHsub_tvar_chain.
      replace (E1 ++ (X1, bind_sub X2) :: E3 ++ (X2, bind_sub U) :: E4)
      with ((E1 ++ (X1, bind_sub X2) :: E3) ++ [(X2, bind_sub U)] ++ E4) in H2.
      2:{ rewrite !app_assoc... }
      replace (E0 ++ (X2, bind_sub X4) :: E2) with
      (E0 ++ [(X2, bind_sub X4)] ++ E2) in H2...
      pose proof uniq_from_wf_env H3.
      pose proof uniq_split_eq _ _ _ _ _ _ _ H5 H2.
      destruct_hypos. inversion H7. subst.
      apply sub_env_cons_some.
      apply sub_env_cut_heads in IHsub_tvar_chain...
      apply uniq_from_wf_env... rewrite !app_assoc...
    }
Qed.

Lemma sub_tvar_chain_tail_in: forall E W X Y,
  sub_tvar_chain E W X Y ->
  exists W' T, W = W' ++ Y ~ bind_sub T.
Proof with auto.
  intros.
  induction H...
  - exists nil, ( U)...
  - destruct IHsub_tvar_chain as [W' [T IH]].
    exists (X1 ~ bind_sub X2 ++ W'), T.
    rewrite IH...
Qed.

Lemma sub_env_binds: forall E W X T,
  sub_env E W ->
  binds X T W ->
  binds X T E.
Proof with auto.
  intros.
  induction H...
  - inversion H0.
  - destruct H0... inversion H0...
Qed.

Lemma sub_tvar_chain_antisym: forall E W1 W2 X Y,
  sub_tvar_chain E W1 X Y -> 
  sub_tvar_chain E W2 Y X -> 
  X = Y.
Proof with auto.
  intros.
  inversion H;subst...
  inversion H0;subst...
  destruct (X == Y)...

  assert (exists T, binds Y (bind_sub T) E2).
  {
    pose proof sub_tvar_chain_sub_env H.
    apply sub_env_cut_heads in H6.
    2:{ apply uniq_from_wf_env... }
    pose proof sub_tvar_chain_tail_in H.
    destruct H7 as [W' [T H7]].
    destruct W';inversion H7;subst...
    { exfalso... }
    exists T.
    apply sub_env_binds with (X:=Y) (T:=bind_sub T) in H6...
  }

  assert (exists T, binds X (bind_sub T) E3).
  {
    rewrite !cons_app_one in H3. rewrite <- H3 in H0.
    pose proof sub_tvar_chain_sub_env H0.
    apply sub_env_cut_heads in H7.
    2:{ apply uniq_from_wf_env... }
    pose proof sub_tvar_chain_tail_in H0.
    destruct H8 as [W' [T H8]].
    destruct W';inversion H8;subst...
    { exfalso... }
    exists T. 
    apply sub_env_binds with (X:=X) (T:=bind_sub T) in H7...
  }

  destruct H6. destruct H7.
  apply binds_split in H6.
  apply binds_split in H7.
  destruct H6 as [E1a [E1b H6]], H7 as [E2a [E2b H7]].
  rewrite H6, H7 in H3.
  rewrite !cons_app_one in H3. rewrite <-app_assoc in H3.
  rewrite <- app_assoc in H3.
  apply uniq_split_eq in H3.
  2:{ apply uniq_from_wf_env. rewrite !app_assoc.
      rewrite H7 in H4... }
  destruct_hypos. subst.
  apply uniq_from_wf_env in H1.
  rewrite !app_assoc in H1.
  apply uniq_app_2 in H1.
  apply uniq_cons_2 in H1.
  rewrite !dom_app in H1...
  exfalso. apply H1. apply union_iff. right.
  apply union_iff. right. apply union_iff. right.
  apply union_iff. left. apply KeySetFacts.add_iff...
Qed.


Lemma sub_antisymmetry: forall (X Y :typ) E,
    WF E X ->
    WF E Y ->
    sub E X Y ->
    sub E Y X ->
    X = Y.
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros...
  -
    dependent destruction H1...
  -
    dependent induction H0;try solve [inversion H1|inversion H2]...
    inversion H3.
  -
    dependent induction H0;try solve [inversion H2|inversion H3|inversion H4|inversion H5|inversion H6]...
    destruct (X==X0);subst...
    assert (Ht:=H).
    apply binds_split in Ht.
    destruct_hypos.
    rename x into E1.
    rename x0 into E2.
    rewrite H3 in H.

    apply suba_sub_tvar_chain in H1. destruct H1 as [W1 H1].
    apply suba_sub_tvar_chain in H2. destruct H2 as [W2 H2].
    pose proof sub_tvar_chain_antisym H1 H2.
    rewrite H4...

  -
    dependent induction H1;try solve [inversion H2|inversion H3|inversion H4|inversion H5]...
    dependent destruction H2.
    dependent destruction H3...
    f_equal...
  -
    dependent induction H2;try solve [inversion H2|inversion H3|inversion H4|inversion H5|inversion H6]...
    dependent destruction H5.
    dependent destruction H7...
    f_equal...
    pick fresh X.
    specialize_x_and_L X L1.
    specialize_x_and_L X L2.
    apply open_tt_var_rev with (X:=X)...
  -
    dependent induction H3;try solve [inversion H2|inversion H3|inversion H4|inversion H5|inversion H6]...
    dependent destruction H7.
    dependent destruction H10...
    f_equal...
    pick fresh X.
    specialize_x_and_L X L1.
    specialize_x_and_L X L2.
    clear H6 H4.
    apply sub_nominal_inversion in H12...
    apply sub_nominal_inversion in H9...
    apply open_tt_var_rev with (X:=X)... 
  -
    dependent induction H0;try solve [inversion H2|inversion H3|inversion H4|inversion H5|inversion H1]...
    dependent destruction H2.
    dependent destruction H1...
    f_equal...
    
Qed.
