Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Preservation.


Lemma sub_and_arrow_absurd: forall i T0 T1 T2 T3,
  Compatible (typ_single i T0) T1 ->
  sub empty T1 (typ_arrow T2 T3) ->
  False.
Proof with auto.
  intros.
  dependent induction H0...
  - inversion H.
  - eapply Compatible_arr_absurd. apply Compatible_symm. apply H.
  - eapply IHsub... dependent destruction H...
  - eapply IHsub... dependent destruction H...
Qed.


Lemma sub_and_all_absurd: forall i T0 T1 T2 T3,
  Compatible (typ_single i T0) T1 ->
  sub empty T1 (typ_all T2 T3) ->
  False.
Proof with auto.
  intros.
  dependent induction H0...
  - inversion H.
  - eapply Compatible_all_absurd. apply Compatible_symm. apply H.
  - eapply IHsub... dependent destruction H...
  - eapply IHsub... dependent destruction H...
Qed.


Lemma sub_and_all_lb_absurd: forall i T0 T1 T2 T3,
  Compatible (typ_single i T0) T1 ->
  sub empty T1 (typ_all_lb T2 T3) ->
  False.
Proof with auto.
  intros.
  dependent induction H0...
  - inversion H.
  - eapply Compatible_all_lb_absurd. apply Compatible_symm. apply H.
  - eapply IHsub... dependent destruction H...
  - eapply IHsub... dependent destruction H...
Qed.


Lemma sub_and_mu_absurd: forall i T0 T1 T2,
  Compatible (typ_single i T0) T1 ->
  sub empty T1 (typ_mu T2) ->
  False.
Proof with auto.
  intros.
  dependent induction H0...
  - inversion H.
  - eapply Compatible_mu_absurd. apply Compatible_symm. apply H.
  - eapply IHsub... dependent destruction H...
  - eapply IHsub... dependent destruction H...
Qed.


Lemma canonical_form_abs : forall e U1 U2 S,
  value e ->
  typing empty e S ->
  sub empty S (typ_arrow U1 U2) ->
  exists V, exists e1, e = exp_abs V e1.
Proof with auto.
  intros.
  generalize dependent U1.
  generalize dependent U2.
  dependent induction H0;intros;try solve [inversion H|inversion H1|inversion H2]...
  -
    exists V.
    exists e1...
  - 
    pose proof sub_transitivity H0 H2.
    inversion H3;subst.
  -
    apply IHtyping with (U1:=U1) (U2:=U2)...
    apply sub_transitivity with (Q:=T)...
  -
    inversion H3;subst.
    + inversion H8.
    + exfalso.
      eapply sub_and_arrow_absurd. apply H10. apply H8.
Qed.


Lemma canonical_form_tabs : forall e U1 U2 S,
  value e ->
  typing empty e S ->
  sub empty S (typ_all U1 U2) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof with auto.
  intros.
  generalize dependent U1.
  generalize dependent U2.
  dependent induction H0;intros;try solve [inversion H|inversion H1|inversion H2]...
  -
    exists V.
    exists e1...
  -
    pose proof sub_transitivity H0 H2.
    inversion H3;subst.
  -
    apply IHtyping with (U1:=U1) (U2:=U2)...
    apply sub_transitivity with (Q:=T)...
  -
    inversion H3; subst.
    + inversion H8.
    + exfalso.
      eapply sub_and_all_absurd. apply H10. apply H8.
Qed.


Lemma canonical_form_tabs_lb : forall e U1 U2 S,
  value e ->
  typing empty e S ->
  sub empty S (typ_all_lb U1 U2) ->
  exists V, exists e1, e = exp_tabs_lb V e1.
Proof with auto.
  intros.
  generalize dependent U1.
  generalize dependent U2.
  dependent induction H0;intros;try solve [inversion H|inversion H1|inversion H2]...
  -
    exists V.
    exists e1...
  -
    pose proof sub_transitivity H0 H2.
    inversion H3;subst.
  -
    apply IHtyping with (U1:=U1) (U2:=U2)...
    apply sub_transitivity with (Q:=T)...
  -
    inversion H3; subst.
    + inversion H8.
    + exfalso.
      eapply sub_and_all_lb_absurd. apply H10. apply H8.
Qed.


Lemma canonical_form_fold : forall e U S,
  value e ->
  typing empty e S ->
  sub empty S (typ_mu U) ->
  exists V, exists e1, exists T, 
   (sub empty (typ_mu V) (typ_mu U) /\ value e1 /\ e = exp_fold T e1 /\
   WF empty T).
Proof with auto.
  intros.
  generalize dependent U.
  dependent induction H0;intros;
  try solve [inversion H|inversion H1|inversion H2|inversion H3]...
  -
    dependent destruction H.
    exists A...
    exists e...
    exists T... repeat split...
    apply sub_transitivity with (Q:=T)... get_well_form...
  -
    apply IHtyping with (U:=U)...
    apply sub_transitivity with (Q:=T)...
  - inversion H3; subst.
    + inversion H8.
    + exfalso.
      eapply sub_and_mu_absurd. apply H10. apply H8.
Qed.


Lemma value_expr: forall e,
    value e -> expr e.
Proof with auto.
  intros.
  induction H...
Qed.


Lemma value_stop: forall v1 v2,
  value v1 ->
  step v1 v2 ->
  False.
Proof with auto.
  intros. generalize dependent v2. dependent induction H; intros; try solve [inversion H0].
  - dependent destruction H1. apply IHvalue with e'...
  - dependent destruction H2.
    + apply IHvalue1 with e3...
    + apply IHvalue2 with e3...
Qed.


Lemma step_proj_ne: forall i0 i e1 e2 x,
  i0 <> i ->
  value (exp_rcd_cons i0 e1 e2) ->
  step (exp_rcd_proj e2 i) x ->
  step (exp_rcd_proj (exp_rcd_cons i0 e1 e2) i) x.
Proof with auto.
  intros. dependent induction H1.
  - apply step_projrcd...
    rewrite <- H2. unfold tlookup.
    destruct (i0==i)... exfalso. apply H...
  - exfalso. apply value_stop with e2 e3... inversion H0...
Qed.


Lemma proj_step_subgeneralize: forall e T i Ti,
  value e ->
  typing empty e T ->
  sub empty T (typ_single i Ti) ->
  exists e' : exp, step (exp_rcd_proj e i) e'.
Proof with auto.
  intros. dependent induction H0; try solve [inversion H; inversion H1].
  - inversion H2.
  - inversion H2.
  - inversion H2.
  - pose proof sub_transitivity H0 H2. inversion H3.
  - apply IHtyping... apply sub_transitivity with T...
  - inversion H1;subst...
    inversion H;subst...
    exists e. constructor...
    simpl. rewrite eq_dec_refl...
  - destruct (i == i1); subst.
    + exists e1. apply step_projrcd...
      unfold tlookup. rewrite eq_dec_refl...
    + dependent destruction H3.
      * exfalso. apply n. inversion H4; subst...
      * destruct IHtyping2... inversion H...
        exists x. apply step_proj_ne...
Qed.

Lemma proj_step: forall e i Ti,
  value e ->
  typing empty e (typ_single i Ti) ->
  exists e' : exp, step (exp_rcd_proj e i) e'.
Proof with auto.
  intros. apply proj_step_subgeneralize with (T:=typ_single i Ti) (Ti:=Ti)...
  apply sa_single; apply Reflexivity...
  apply typing_regular in H0; destruct_hypos. inversion H2...
Qed.

Lemma progress : forall e T,
  typing empty e T ->
  value e \/ exists e', step e e'.
Proof with eauto.
  intros.
  dependent induction H...
  -
    inversion H0...
  - (* abs *)
    left.
    constructor.
    apply expr_abs with (L:=L).
    pick fresh Y.
    specialize_x_and_L Y L.
    apply typing_regular in H.
    destruct_hypos.
    dependent destruction H...
    apply WF_type in H0...
    intros.
    apply H in H1.
    apply typing_regular in H1.
    destruct_hypos...
  - (* app *)
    right.
    destruct IHtyping1;destruct IHtyping2...
    +
      apply canonical_form_abs with (S:=typ_arrow T1 T2) (U1:=T1) (U2:=T2) in H...
      destruct_hypos.
      exists (open_ee x0 e2).
      subst.
      apply step_beta...
      apply value_expr...
      apply Reflexivity...
      apply typing_regular in H.
      destruct_hypos...
    +
      destruct_hypos.
      exists (exp_app e1 x).
      apply step_app2...
    +
      destruct_hypos.
      exists (exp_app x e2).
      apply step_app1...
      apply value_expr...
    +
      destruct_hypos.
      exists (exp_app x0 e2).
      apply step_app1...
      apply typing_regular in H0.
      destruct_hypos...
  - (* tabs *)
    left.
    constructor.
    apply expr_tabs with (L:=L).
    pick fresh Y.
    specialize_x_and_L Y L.
    apply typing_regular in H.
    destruct_hypos.
    dependent destruction H...
    apply WF_type in H0...
    intros.
    apply H in H1.
    apply typing_regular in H1.
    destruct_hypos...
  - (* tabs_lb *)
    left.
    constructor.
    apply expr_tabs_lb with (L:=L).
    pick fresh Y.
    specialize_x_and_L Y L.
    apply typing_regular in H.
    destruct_hypos.
    dependent destruction H...
    apply WF_type in H0...
    intros.
    apply H in H1.
    apply typing_regular in H1.
    destruct_hypos...
  - (* tapp *)
    right.
    destruct IHtyping...
    +
      apply canonical_form_tabs with (U1:=T1) (U2:=T2) in H...
      destruct_hypos.
      exists (open_te x0 T).
      subst.
      apply step_tabs...
      apply value_expr...
      get_type...
      apply Reflexivity...
      apply typing_regular in H.
      destruct_hypos...
    +
      destruct_hypos.
      exists (exp_tapp x T).
      apply step_tapp...
      get_type...
  - (* tapp_lb *)
    right.
    destruct IHtyping...
    +
      apply canonical_form_tabs_lb with (U1:=T1) (U2:=T2) in H...
      destruct_hypos.
      exists (open_te x0 T).
      subst.
      apply step_tabs_lb...
      apply value_expr...
      get_type...
      apply Reflexivity...
      apply typing_regular in H.
      destruct_hypos...
    +
      destruct_hypos.
      exists (exp_tapp x T).
      apply step_tapp...
      get_type...
  - (* fold *)
    assert (empty ~= empty) by auto.
    apply IHtyping in H1.
    destruct H1.
    left.
    constructor...
    { get_well_form. apply WF_type in H3... }
    right.
    destruct H1.
    exists (exp_fold T x).
    constructor...
    { get_well_form. apply WF_type in H3... }

  - (* unfold *)
    right.
    destruct IHtyping...
    +
      apply canonical_form_fold with (e:=e) (S:=A) (U:=T) in H0...
      destruct_hypos.
      exists x0...
      rewrite H3.
      get_well_form...
      apply step_fld...
      apply WF_type in H4...
      apply typing_regular in H...
      destruct_hypos...
      apply WF_type in H8...
    +
      destruct_hypos.
      exists (exp_unfold A x).
      (* apply canonical_form_fold with (e:=e) (S:=A) (U:=T) in H0... *)
      apply step_unfold...
      apply typing_regular in H...
      destruct_hypos.
      apply WF_type in H3...
  -
    right.
    assert (empty ~= empty) by auto.
    apply IHtyping in H0. destruct H0.
    +
      apply proj_step with Ti...
    +
      destruct H0.
      exists ((exp_rcd_proj x i)).
      apply step_proj...
  -
    destruct IHtyping...
    + left. constructor... constructor...
    + destruct H0 as [e' ?]. right.
      exists (exp_rcd_cons i e' exp_rcd_nil)...
  -
    assert (empty ~= empty) by auto.
    assert (empty ~= empty) by auto.
    apply IHtyping1 in H4.
    apply IHtyping2 in H5.
    clear IHtyping1; clear IHtyping2.
    destruct H4; destruct H5.
    +
      left.
      constructor... constructor...
    +
      right.
      destruct H5.
      exists (exp_rcd_cons i1 e1 x)...
      (* apply step_rcd_cons... *)
    +
      right.
      destruct H4.
      exists (exp_rcd_cons i1 x (exp_rcd_cons i2 e2 e3))...
      (* apply step_rcd_head... *)
    +
      right.
      destruct H4.
      exists (exp_rcd_cons i1 x (exp_rcd_cons i2 e2 e3))...
      (* apply step_rcd_head... *)
Qed.