Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Preservation.

Lemma canonical_form_abs : forall e U1 U2 S,
  value e ->
  typing empty e S ->
  sub empty S (typ_arrow U1 U2) ->
  exists V, exists e1, e = exp_abs V e1.
Proof with auto.
  intros.
  generalize dependent U1.
  generalize dependent U2.
  dependent induction H0;intros;
    try solve [inversion H;inv_rt|inversion H1;inv_rt|inversion H2;inv_rt
    |inversion H3;inv_rt]...
  -
    exists V.
    exists e1...
  -
    inversion H0;subst;inv_rt. inversion H2;inv_rt. inversion H2;inv_rt.
  -
    apply IHtyping with (U1:=U1) (U2:=U2)...
    apply sub_transitivity with (Q:=T)...
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
  dependent induction H0;intros;
  try solve [inversion H;inv_rt|inversion H1;inv_rt|inversion H2;inv_rt
  |inversion H3;inv_rt]...
  -
    exists V.
    exists e1...
  -
    inversion H0;subst;inv_rt. inversion H2;inv_rt. inversion H2;inv_rt.
  -
    apply IHtyping with (U1:=U1) (U2:=U2)...
    apply sub_transitivity with (Q:=T)...
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
  try solve [inversion H;inv_rt|inversion H1;inv_rt|inversion H2;inv_rt
  |inversion H3;inv_rt]...
  -
    dependent destruction H.
    exists A...
    exists e...
    exists T... repeat split...
    apply sub_transitivity with (Q:=T)... get_well_form...
  -
    apply IHtyping with (U:=U)...
    apply sub_transitivity with (Q:=T)...
Qed.

(* 
Lemma canonical_form_fold' : forall e U S,
  typing empty e S ->
  sub empty S (typ_mu U) ->
  exists V, exists e1, (sub empty (typ_mu V) (typ_mu U) /\ value e1 /\ e = exp_fold (typ_mu V) e1).
Proof with auto.
  intros.
  generalize dependent U.
  dependent induction H;intros;try solve [inversion H0|inversion H1].
  
  |inversion H2]...
  -
    dependent destruction H.
    exists A...
    exists e...
  -
    apply IHtyping with (U:=U)...
    apply sub_transitivity with (Q:=T)...
Qed. *)


Lemma value_expr: forall e,
    value e -> expr e.
Proof with auto.
  intros.
  induction H...
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
    (* apply typing_regular in H0.
    destruct_hypos...
    apply WF_type in H1... *)
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
      apply typing_regular in H.
      destruct_hypos.
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
    destruct IHtyping...
    +
      right. assert (Ht:=H1).
      apply lookup_field_in_value with (T:=T) (i:=i) (Ti:=Ti) in H1...
      destruct H1.
      destruct H1.
      exists x...
    +
      right. destruct H1...
  -
    destruct IHtyping1;destruct IHtyping2...
    +
      destruct H5...
    +
      destruct H4...
    +
      destruct H4;destruct H5...
Qed.
