Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Decidability.
Require Export AlgoTyping.
Require Export Coq.micromega.Lia.


Lemma exposure_uniq: forall E T T1 T2,
  wf_env E ->
  Algo.exposure E T T1 -> Algo.exposure E T T2 -> T1 = T2.
Proof with auto.
  intros E T T1 T2 Hwf Hexp1 Hexp2.
  generalize dependent T2.
  induction Hexp1;intros;try solve [inversion Hexp2;subst;auto].
  -
    inversion Hexp2;subst.
    + get_same_bind...
    + get_same_bind...
  -
    inversion Hexp2;subst.
    + get_same_bind...
    + get_same_bind...
Qed.


Lemma exposure_uniq2: forall E T T1 T2,
  wf_env E ->
  Algo.exposure2 E T1 T -> Algo.exposure2 E T2 T -> T1 = T2.
Proof with auto.
  intros E T T1 T2 Hwf Hexp1 Hexp2.
  generalize dependent T2.
  induction Hexp1;intros;try solve [inversion Hexp2;subst;auto].
  -
    inversion Hexp2;subst.
    + get_same_bind...
    + get_same_bind...
  -
    inversion Hexp2;subst.
    + get_same_bind...
    + get_same_bind...
Qed.

Lemma Compatible_exposure_i_absurd:
  forall E A B l T1 T2,
  Compatible A B ->
  Algo.exposure_i E A l T1 ->
  Algo.exposure_i E B l T2 ->
  False.
Proof with auto.
  intros.
  induction H.
  - inv H0. inv H1. exfalso...
  - inv H0...
  - inv H1...
Qed.

Lemma exposurei_uniq: forall E T i T1 T2,
  wf_env E -> WF E T ->
  Algo.exposure_i E T i T1 -> Algo.exposure_i E T i T2 -> T1 = T2.
Proof with auto.
  intros E T i T1 T2 Hwf Hwft Hexp1 Hexp2.
  generalize dependent T2.
  induction Hexp1;intros;try solve [inversion Hexp2;subst;auto].
  -
    inversion Hwft;subst.
    inversion Hexp2;subst...
    + exfalso. eapply Compatible_exposure_i_absurd;eassumption.
  -
    inversion Hwft;subst.
    inversion Hexp2;subst...
    + exfalso. eapply Compatible_exposure_i_absurd;eassumption.
  -
    inversion Hexp2;subst.
    + get_same_bind...
      apply IHHexp1 in H3...
      eapply WF_from_binds_typ with (x:=X)...
Qed.

Lemma open_tt_var_inv: forall T1 T2 x,
  x `notin` fv_tt T1 -> x `notin` fv_tt T2 ->
  open_tt T1 (typ_fvar x) = open_tt T2 (typ_fvar x) ->
  T1 = T2.
Proof with auto.
  unfold open_tt in *.
  generalize 0.
  intros. generalize dependent n.
  generalize dependent T2.
  induction T1;intros.
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1.
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1.
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1.
  - simpl in H1. destruct (n0 == n).
    + induction T2;simpl in H1; try solve [inversion H1]...
      destruct (n0 == n1);inversion H1.
      subst... simpl in H0. inv H1. fsetdec.
    + induction T2;simpl in H1; try solve [inversion H1]...
      destruct (n0 == n2);inversion H1...
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1. inv H1.
    simpl in H. fsetdec.
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1. simpl in H, H0.
    inv H1. apply IHT1_1 in H3...
    apply IHT1_2 in H4... subst...
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1. simpl in H, H0.
    inv H1. apply IHT1_1 in H3...
    apply IHT1_2 in H4... subst...
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1. simpl in H, H0.
    inv H1. apply IHT1_1 in H3...
    apply IHT1_2 in H4... subst...
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1. simpl in H, H0.
    inv H1. apply IHT1 in H3... subst...
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1. simpl in H, H0.
    inv H1. apply IHT1 in H4... subst...
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1. simpl in H, H0.
    inv H1. apply IHT1 in H4... subst...
  - induction T2;simpl in H1; try solve [inversion H1]...
    destruct (n == n0);inversion H1. simpl in H, H0.
    inv H1. apply IHT1_1 in H3...
    apply IHT1_2 in H4... subst...
Qed.


Lemma algotyping_uniq: forall E e A B,
  Algo.typing E e A -> Algo.typing E e B -> A = B.
Proof with auto.
  intros E e A B Hty1 Hty2.
  generalize dependent B.
  induction Hty1;intros;try solve [inversion Hty2;subst;auto].
  -
    inversion Hty2;subst.
    get_same_bind...
  -
    inversion Hty2;subst.
    f_equal. pick_fresh x.
    specialize_x_and_L x L.
    apply H0...
  -
    inversion Hty2;subst.
    2:{ specialize (IHHty1_1 _ H3).
        subst.
        epose proof exposure_uniq _ H5 H.
        Unshelve. 2:{ get_well_form... }
        inversion H1.
    }
    specialize (IHHty1_1 _ H3). subst.
    epose proof exposure_uniq _ H4 H.
    Unshelve. 2:{ get_well_form... }
    inversion H1...
  -
    inversion Hty2;subst...
    { specialize (IHHty1_1 _ H2).
      subst.
      epose proof exposure_uniq _ H3 H.
      Unshelve. 2:{ get_well_form... }
      inversion H0.
    }
  -
    inversion Hty2;subst... f_equal.
    pick_fresh x.
    specialize_x_and_L x L.
    specialize_x_and_L x L0.
    apply H0 in H5.
    apply open_tt_var_inv in H5...
  -
    inversion Hty2;subst... f_equal.
    pick_fresh x.
    specialize_x_and_L x L.
    specialize_x_and_L x L0.
    apply H0 in H5.
    apply open_tt_var_inv in H5...
  -
    inversion Hty2;subst...
    { specialize (IHHty1 _ H3).
      subst.
      epose proof exposure_uniq _ H5 H.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
    { specialize (IHHty1 _ H3).
      subst.
      epose proof exposure_uniq _ H5 H.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
    { specialize (IHHty1 _ H3).
      subst.
      epose proof exposure_uniq _ H5 H.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
  -
    inversion Hty2;subst...
    { specialize (IHHty1 _ H3).
      subst.
      epose proof exposure_uniq _ H5 H.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
    { specialize (IHHty1 _ H3).
      subst.
      epose proof exposure_uniq _ H5 H.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
    { specialize (IHHty1 _ H3).
      subst.
      epose proof exposure_uniq _ H5 H.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
  -
    inversion Hty2;subst...
    { specialize (IHHty1 _ H3).
      subst.
      epose proof exposure_uniq _ H5 H.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
    { specialize (IHHty1 _ H3).
      subst.
      epose proof exposure_uniq _ H5 H.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
  -
    inversion Hty2;subst...
    { pose proof IHHty1 _ H4. subst.
      epose proof exposure_uniq2 _ H6 H0.
      Unshelve. 2:{ get_well_form... }
      inversion H2;subst...
    }
  -
    inversion Hty2;subst...
    { pose proof IHHty1 _ H3. subst.
      epose proof exposure_uniq2 _ H6 H.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
  -
    inversion Hty2;subst...
    { pose proof IHHty1 _ H3. subst.
      epose proof exposure_uniq _ H7 H0.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
    { pose proof IHHty1 _ H3. subst.
      epose proof exposure_uniq _ H7 H0.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
  -
    inversion Hty2;subst...
    { pose proof IHHty1 _ H3. subst.
      epose proof exposure_uniq _ H7 H0.
      Unshelve. 2:{ get_well_form... }
      inversion H1;subst...
    }
  -
    inversion Hty2;subst...
    { pose proof IHHty1 _ H3. subst.
      epose proof exposurei_uniq _ _ H5 H.
      Unshelve. 
      2:{ apply Algo.typing_regular in Hty1. destruct_hypos... }
      2:{ apply Algo.typing_regular in Hty1. destruct_hypos... }
      subst...
    }
  -
    inversion Hty2;subst... f_equal.
    apply IHHty1...
  -
    inversion Hty2;subst... f_equal.
    + f_equal.
      apply IHHty1_1...
    + f_equal.
      apply IHHty1_2...
Qed.




Fixpoint size_exp (e: exp) : nat :=
  match e with
  | exp_bvar _ => 1
  | exp_fvar _ => 1
  | exp_abs _ e1 => S (size_exp e1)
  | exp_app e1 e2 => S (size_exp e1 + size_exp e2) 
  | exp_tabs _ e1 => S (size_exp e1)
  | exp_tabs_lb _ e1 => S (size_exp e1)
  | exp_tapp e1 _ => S (size_exp e1)
  | exp_nat => 1
  | exp_unfold _ e1 => S (size_exp e1)
  | exp_fold _ e1 => S (size_exp e1)
  | exp_rcd_nil => 1
  | exp_rcd_cons _ e1 e2 => S (size_exp e1 + size_exp e2)
  | exp_rcd_proj e1 _ => S (size_exp e1)
  end.

Lemma binds_In': forall {A:Type} x (a:A) E,
  binds x a E -> In (x, a) E.
Proof with auto.
  intros. generalize dependent x.
  generalize dependent a.
  induction E;intros.
  - inversion H.
  - inversion H;subst.
    + simpl. left...
    + simpl. right. apply IHE...
Qed.

Lemma binds_In_inv': forall {A:Type} x (a:A) E,
  In (x, a) E -> binds x a E.
Proof with auto.
  intros. generalize dependent x.
  generalize dependent a.
  induction E;intros.
  - inversion H.
  - destruct a. simpl in H. destruct H.
    + inversion H;subst. simpl. left...
    + simpl. right. apply IHE...
Qed.


Lemma in_split': forall {A:Type} (x:A) E,
  In x E -> (forall x y : A, {x = y} + {x <> y}) ->
  {E1 : list A & {E2 : list A | E = E1 ++ x :: E2} }.
Proof with auto.
  intros.
  induction E.
  - inversion H.
  - simpl in H.
    destruct (X a x).
    + subst. exists nil. exists E. reflexivity.
    + assert (In x E).
      { destruct H... exfalso... }
      destruct (IHE H0) as [E1' [E2' ?]].
      exists (a :: E1').
      exists E2'. subst.
      simpl. reflexivity.
Qed.

Lemma EqDec_ab_eq: forall x y : atom * binding,
  {x = y} + {x <> y}.
Proof with auto. 
  intros. destruct x, y.
  destruct (Atom.eq_dec a a0).
  2:{ right. intros C. inversion C;subst... }
  subst.
  decide equality.
  destruct b1, b2; try solve [right;intros C;inversion C].
  + destruct (EqDec_eq t t0).
    * left. subst...
    * right. intros C. inversion C...
  + destruct (EqDec_eq t t0).
    * left. subst...
    * right. intros C. inversion C...
  + destruct (EqDec_eq t t0).
    * left. subst...
    * right. intros C. inversion C...
Qed.

Lemma exposure_strengthening: forall E1 E2 A B,
  Algo.exposure (E1 ++ E2) A B ->
  wf_env (E1 ++ E2) -> WF E2 A ->
  Algo.exposure E2 A B.
Proof with auto.
  intros.
  dependent induction H...
  - analyze_binds_uniq H.
    { apply uniq_from_wf_env... }
    { inversion H2;subst. 
      + apply binds_In in H5. fsetdec.
      + apply binds_In in H5. fsetdec. }
    { apply Algo.exposure_trans_tvar with (U:=U)...
      eapply IHexposure...
      apply WF_from_binds_typ in BindsTac...
      apply wf_env_cons in H1... }
  - apply Algo.exposure_trans_tvar_lb with (U:=U)...
    analyze_binds_uniq H.
    { apply uniq_from_wf_env... }
    { inversion H1;subst.
      + apply binds_In in H4. fsetdec.
      + apply binds_In in H4. fsetdec.
    }
Qed.

Lemma exposurei_strengthening: forall E1 E2 l A B,
  Algo.exposure_i (E1 ++ E2) A l B ->
  wf_env (E1 ++ E2) -> WF E2 A ->
  Algo.exposure_i E2 A l B.
Proof with auto.
  intros.
  dependent induction H...
  -
   apply Algo.exposurei_and1. inv H1.
   eapply IHexposure_i;eauto.
  -
   apply Algo.exposurei_and2. inv H1.
   eapply IHexposure_i;eauto.
  - analyze_binds_uniq H.
    { apply uniq_from_wf_env... }
    { inversion H2;subst. 
      + apply binds_In in H5. fsetdec.
      + apply binds_In in H5. fsetdec. }
    { apply Algo.exposurei_trans_tvar with (U:=U)...
      eapply IHexposure_i...
      apply WF_from_binds_typ in BindsTac...
      apply wf_env_cons in H1... }
Qed.


Lemma exposure2_strengthening: forall E1 E2 A B,
  Algo.exposure2 (E1 ++ E2) B A ->
  wf_env (E1 ++ E2) -> WF E2 A ->
  Algo.exposure2 E2 B A.
Proof with auto.
  intros.
  dependent induction H...
  - analyze_binds_uniq H.
    { apply uniq_from_wf_env... }
    { inversion H1;subst. 
      + apply binds_In in H4. fsetdec.
      + apply binds_In in H4. fsetdec. }
    { apply Algo.exposure2_trans_tvar with (U:=U)... }
  - analyze_binds_uniq H.
    { apply uniq_from_wf_env... }
    { inversion H2;subst.
      + apply binds_In in H5. fsetdec.
      + apply binds_In in H5. fsetdec.
    }
    { 
      apply Algo.exposure2_trans_tvar_lb with (U:=U)...
      eapply IHexposure2 with (E3:=E1)...
      apply WF_from_binds_typ_lb in BindsTac...
      apply wf_env_cons in H1...
    }
Qed.


Lemma exposure_bot_dec_aux: forall k E A,
  List.length E <= k ->
  wf_env E -> WF E A ->
  { Algo.exposure E A typ_bot } + { ~ Algo.exposure E A typ_bot }.
Proof with auto.
  intros k. induction k;intros.
  {
    destruct A; 
    simpl in *; try solve [right; intros C; inversion C].
    - left. constructor...
    - destruct E; simpl in H; try lia.
      right. intros C. inversion C;subst.
      inversion H3.
  }
  destruct A; simpl in H0; try solve [right; intros C; inversion C].
  - left. constructor...
  - destruct (binds_key_dec E a).
    2:{ right. intros C. inversion C;subst.
        apply n in H3...
    }
    destruct s. destruct x.
    {
      apply binds_In' in b.
      pose proof in_split' _ _ b EqDec_ab_eq.
      destruct H2 as [E1 [E2 ?]]. subst.
      destruct (IHk E2 t)...
      { rewrite app_length in H. simpl in H. lia. }
      { apply wf_env_cons in H0. inversion H0;subst... }
      { apply wf_env_cons in H0. inversion H0;subst... }
      + left. apply Algo.exposure_trans_tvar with (U:=t)...
        rewrite_alist (nil ++ (E1 ++ (a~ bind_sub t)) ++ E2).
        apply Algo.exposure_weakening_bind2...
      + right. intros C. inversion C;subst.
        apply binds_mid_eq in H3.
        2:{ apply uniq_from_wf_env... }
        inversion H3;subst. apply n.
        rewrite_alist ((E1 ++ a ~ bind_sub t) ++ E2) in H5.
        apply exposure_strengthening in H5...
        { rewrite app_assoc... }
        { apply wf_env_cons in H0. inversion H0... }
    }
    { right. intros C. inversion C;subst.
      get_same_bind... }
    { right. intros C. inversion C;subst.
      get_same_bind... }
Qed.

Lemma exposure_bot_dec: forall E A,
  wf_env E -> WF E A ->
  { Algo.exposure E A typ_bot } + { ~ Algo.exposure E A typ_bot }.
Proof with auto.
  intros. apply exposure_bot_dec_aux with (k:=List.length E)...
Qed.




Lemma exposure2_top_dec_aux: forall k E A,
  List.length E <= k ->
  wf_env E -> WF E A ->
  { Algo.exposure2 E typ_top A } + { ~ Algo.exposure2 E typ_top A }.
Proof with auto.
  intros k. induction k;intros.
  {
    destruct A; 
    simpl in *; try solve [right; intros C; inversion C].
    - left. constructor...
    - destruct E; simpl in H; try lia.
      right. intros C. inversion C;subst.
      inversion H3.
  }
  destruct A; simpl in H0; try solve [right; intros C; inversion C].
  - left. constructor...
  - destruct (binds_key_dec E a).
    2:{ right. intros C. inversion C;subst.
        apply n in H3...
    }
    destruct s. destruct x.
    { right. intros C. inversion C;subst.
      get_same_bind... }
    {
      apply binds_In' in b.
      pose proof in_split' _ _ b EqDec_ab_eq.
      destruct H2 as [E1 [E2 ?]]. subst.
      destruct (IHk E2 t)...
      { rewrite app_length in H. simpl in H. lia. }
      { apply wf_env_cons in H0. inversion H0;subst... }
      { apply wf_env_cons in H0. inversion H0;subst... }
      + left. apply Algo.exposure2_trans_tvar_lb with (U:=t)...
        rewrite_alist (nil ++ (E1 ++ (a~ bind_sub_lb t)) ++ E2).
        apply Algo.exposure2_weakening_bind2...
      + right. intros C. inversion C;subst.
        apply binds_mid_eq in H3.
        2:{ apply uniq_from_wf_env... }
        inversion H3;subst. apply n.
        rewrite_alist ((E1 ++ a ~ bind_sub_lb t) ++ E2) in H6.
        apply exposure2_strengthening in H6...
        { rewrite app_assoc... }
        { apply wf_env_cons in H0. inversion H0... }
    }
    { right. intros C. inversion C;subst.
      get_same_bind... }
Qed.

Lemma exposure2_top_dec: forall E A,
  wf_env E -> WF E A ->
  { Algo.exposure2 E typ_top A } + { ~ Algo.exposure2 E typ_top A }.
Proof with auto.
  intros. apply exposure2_top_dec_aux with (k:=List.length E)...
Qed.

Lemma exposure_arr_dec_aux: forall k E A,
  List.length E <= k ->
  wf_env E -> WF E A ->
  { A1 & { A2 | Algo.exposure E A (typ_arrow A1 A2) } } + 
  { forall A1 A2,  ~  Algo.exposure E A (typ_arrow A1 A2) }.
Proof with auto.
  intros k. induction k;intros.
  {
    destruct A; 
    simpl in *; try solve [right; intros A1' A2' C; inversion C].
    - destruct E; simpl in H; try lia.
      right. intros A1' A2' C. inversion C;subst.
      inversion H3.
    - left. exists A1, A2. constructor...
  }
  destruct A; simpl in H0; try solve [right; intros A1' A2' C; inversion C].
  - destruct (binds_key_dec E a).
    2:{ right. intros A1' A2' C. inversion C;subst.
        apply n in H3...
    }
    destruct s. destruct x.
    {
      apply binds_In' in b.
      pose proof in_split' _ _ b EqDec_ab_eq.
      destruct H2 as [E1 [E2 ?]]. subst.
      destruct (IHk E2 t)...
      { rewrite app_length in H. simpl in H. lia. }
      { apply wf_env_cons in H0. inversion H0;subst... }
      { apply wf_env_cons in H0. inversion H0;subst... }
      + left. 
        destruct s as [A1' [A2' ?]]. exists A1', A2'.
        apply Algo.exposure_trans_tvar with (U:=t)...
        rewrite_alist (nil ++ (E1 ++ (a~ bind_sub t)) ++ E2).
        apply Algo.exposure_weakening_bind2...
      + right. intros A1' A2' C. inversion C;subst.
        apply binds_mid_eq in H3.
        2:{ apply uniq_from_wf_env... }
        inversion H3;subst. eapply n with (A1:=A1') (A2:=A2').
        rewrite_alist ((E1 ++ a ~ bind_sub t) ++ E2) in H5.
        apply exposure_strengthening in H5...
        { rewrite app_assoc... }
        { apply wf_env_cons in H0. inversion H0... }
    }
    { right. intros A1' A2' C. inversion C;subst.
      get_same_bind... }
    { right. intros A1' A2' C. inversion C;subst.
      get_same_bind... }
  - left.  exists A1, A2. constructor...
Qed.

Lemma exposure_arr_dec: forall E A,
  wf_env E -> WF E A ->
  { A1 & { A2 | Algo.exposure E A (typ_arrow A1 A2) } } + 
  { forall A1 A2,  ~  Algo.exposure E A (typ_arrow A1 A2) }.
Proof with auto.
  intros. apply exposure_arr_dec_aux with (k:=List.length E)...
Qed.


Lemma exposure_tabs_dec_aux: forall k E A,
  List.length E <= k ->
  wf_env E -> WF E A ->
  { A1 & { A2 | Algo.exposure E A (typ_all A1 A2) } } + 
  { forall A1 A2,  ~  Algo.exposure E A (typ_all A1 A2) }.
Proof with auto.
  intros k. induction k;intros.
  {
    destruct A; 
    simpl in *; try solve [right; intros A1' A2' C; inversion C].
    - destruct E; simpl in H; try lia.
      right. intros A1' A2' C. inversion C;subst.
      inversion H3.
    - left. exists A1, A2. constructor...
  }
  destruct A; simpl in H0; try solve [right; intros A1' A2' C; inversion C].
  - destruct (binds_key_dec E a).
    2:{ right. intros A1' A2' C. inversion C;subst.
        apply n in H3...
    }
    destruct s. destruct x.
    {
      apply binds_In' in b.
      pose proof in_split' _ _ b EqDec_ab_eq.
      destruct H2 as [E1 [E2 ?]]. subst.
      destruct (IHk E2 t)...
      { rewrite app_length in H. simpl in H. lia. }
      { apply wf_env_cons in H0. inversion H0;subst... }
      { apply wf_env_cons in H0. inversion H0;subst... }
      + left. 
        destruct s as [A1' [A2' ?]]. exists A1', A2'.
        apply Algo.exposure_trans_tvar with (U:=t)...
        rewrite_alist (nil ++ (E1 ++ (a~ bind_sub t)) ++ E2).
        apply Algo.exposure_weakening_bind2...
      + right. intros A1' A2' C. inversion C;subst.
        apply binds_mid_eq in H3.
        2:{ apply uniq_from_wf_env... }
        inversion H3;subst. eapply n with (A1:=A1') (A2:=A2').
        rewrite_alist ((E1 ++ a ~ bind_sub t) ++ E2) in H5.
        apply exposure_strengthening in H5...
        { rewrite app_assoc... }
        { apply wf_env_cons in H0. inversion H0... }
    }
    { right. intros A1' A2' C. inversion C;subst.
      get_same_bind... }
    { right. intros A1' A2' C. inversion C;subst.
      get_same_bind... }
  - left.  exists A1, A2. constructor...
Qed.

Lemma exposure_tabs_dec: forall E A,
  wf_env E -> WF E A ->
  { A1 & { A2 | Algo.exposure E A (typ_all A1 A2) } } + 
  { forall A1 A2,  ~  Algo.exposure E A (typ_all A1 A2) }.
Proof with auto.
  intros. apply exposure_tabs_dec_aux with (k:=List.length E)...
Qed.



Lemma exposure_tabs_lb_dec_aux: forall k E A,
  List.length E <= k ->
  wf_env E -> WF E A ->
  { A1 & { A2 | Algo.exposure E A (typ_all_lb A1 A2) } } + 
  { forall A1 A2,  ~  Algo.exposure E A (typ_all_lb A1 A2) }.
Proof with auto.
  intros k. induction k;intros.
  {
    destruct A; 
    simpl in *; try solve [right; intros A1' A2' C; inversion C].
    - destruct E; simpl in H; try lia.
      right. intros A1' A2' C. inversion C;subst.
      inversion H3.
    - left. exists A1, A2. constructor...
  }
  destruct A; simpl in H0; try solve [right; intros A1' A2' C; inversion C].
  - destruct (binds_key_dec E a).
    2:{ right. intros A1' A2' C. inversion C;subst.
        apply n in H3...
    }
    destruct s. destruct x.
    {
      apply binds_In' in b.
      pose proof in_split' _ _ b EqDec_ab_eq.
      destruct H2 as [E1 [E2 ?]]. subst.
      destruct (IHk E2 t)...
      { rewrite app_length in H. simpl in H. lia. }
      { apply wf_env_cons in H0. inversion H0;subst... }
      { apply wf_env_cons in H0. inversion H0;subst... }
      + left. 
        destruct s as [A1' [A2' ?]]. exists A1', A2'.
        apply Algo.exposure_trans_tvar with (U:=t)...
        rewrite_alist (nil ++ (E1 ++ (a~ bind_sub t)) ++ E2).
        apply Algo.exposure_weakening_bind2...
      + right. intros A1' A2' C. inversion C;subst.
        apply binds_mid_eq in H3.
        2:{ apply uniq_from_wf_env... }
        inversion H3;subst. eapply n with (A1:=A1') (A2:=A2').
        rewrite_alist ((E1 ++ a ~ bind_sub t) ++ E2) in H5.
        apply exposure_strengthening in H5...
        { rewrite app_assoc... }
        { apply wf_env_cons in H0. inversion H0... }
    }
    { right. intros A1' A2' C. inversion C;subst.
      get_same_bind... }
    { right. intros A1' A2' C. inversion C;subst.
      get_same_bind... }
  - left.  exists A1, A2. constructor...
Qed.

Lemma exposure_tabs_lb_dec: forall E A,
  wf_env E -> WF E A ->
  { A1 & { A2 | Algo.exposure E A (typ_all_lb A1 A2) } } + 
  { forall A1 A2,  ~  Algo.exposure E A (typ_all_lb A1 A2) }.
Proof with auto.
  intros. apply exposure_tabs_lb_dec_aux with (k:=List.length E)...
Qed.




Lemma exposure_mu_dec_aux: forall k E A,
  List.length E <= k ->
  wf_env E -> WF E A ->
  { A1 | Algo.exposure E A (typ_mu A1) } + 
  { forall A1 ,  ~  Algo.exposure E A (typ_mu A1) }.
Proof with auto.
  intros k. induction k;intros.
  {
    destruct A; 
    simpl in *; try solve [right; intros A1' C; inversion C].
    - destruct E; simpl in H; try lia.
      right. intros A1' C. inversion C;subst.
      inversion H3.
    - left. exists A. constructor...
  }
  destruct A; simpl in H0; try solve [right; intros A1' C; inversion C].
  - destruct (binds_key_dec E a).
    2:{ right. intros A1' C. inversion C;subst.
        apply n in H3...
    }
    destruct s. destruct x.
    {
      apply binds_In' in b.
      pose proof in_split' _ _ b EqDec_ab_eq.
      destruct H2 as [E1 [E2 ?]]. subst.
      destruct (IHk E2 t)...
      { rewrite app_length in H. simpl in H. lia. }
      { apply wf_env_cons in H0. inversion H0;subst... }
      { apply wf_env_cons in H0. inversion H0;subst... }
      + left. 
        destruct s as [A1' ?]. exists A1'.
        apply Algo.exposure_trans_tvar with (U:=t)...
        rewrite_alist (nil ++ (E1 ++ (a~ bind_sub t)) ++ E2).
        apply Algo.exposure_weakening_bind2...
      + right. intros A1' C. inversion C;subst.
        apply binds_mid_eq in H3.
        2:{ apply uniq_from_wf_env... }
        inversion H3;subst. eapply n with (A1:=A1').
        rewrite_alist ((E1 ++ a ~ bind_sub t) ++ E2) in H5.
        apply exposure_strengthening in H5...
        { rewrite app_assoc... }
        { apply wf_env_cons in H0. inversion H0... }
    }
    { right. intros A1' C. inversion C;subst.
      get_same_bind... }
    { right. intros A1' C. inversion C;subst.
      get_same_bind... }
  - left.  exists A. constructor...
Qed.

Lemma exposure_mu_dec: forall E A,
  wf_env E -> WF E A ->
  { A1 | Algo.exposure E A (typ_mu A1) } + 
  { forall A1,  ~  Algo.exposure E A (typ_mu A1) }.
Proof with auto.
  intros. apply exposure_mu_dec_aux with (k:=List.length E)...
Qed.




Lemma exposure2_mu_dec_aux: forall k E A,
  List.length E <= k ->
  wf_env E -> WF E A ->
  { A1 | Algo.exposure2 E (typ_mu A1) A } + 
  { forall A1 ,  ~  Algo.exposure2 E (typ_mu A1) A }.
Proof with auto.
  intros k. induction k;intros.
  {
    destruct A; 
    simpl in *; try solve [right; intros A1' C; inversion C].
    - destruct E; simpl in H; try lia.
      right. intros A1' C. inversion C;subst.
      inversion H3.
    - left. exists A. constructor...
  }
  destruct A; simpl in H0; try solve [right; intros A1' C; inversion C].
  - destruct (binds_key_dec E a).
    2:{ right. intros A1' C. inversion C;subst.
        apply n in H3...
    }
    destruct s. destruct x.
    { right. intros A1' C. inversion C;subst.
      get_same_bind... }
    {
      apply binds_In' in b.
      pose proof in_split' _ _ b EqDec_ab_eq.
      destruct H2 as [E1 [E2 ?]]. subst.
      destruct (IHk E2 t)...
      { rewrite app_length in H. simpl in H. lia. }
      { apply wf_env_cons in H0. inversion H0;subst... }
      { apply wf_env_cons in H0. inversion H0;subst... }
      + left. 
        destruct s as [A1' ?]. exists A1'.
        apply Algo.exposure2_trans_tvar_lb with (U:=t)...
        rewrite_alist (nil ++ (E1 ++ (a~ bind_sub_lb t)) ++ E2).
        apply Algo.exposure2_weakening_bind2...
      + right. intros A1' C. inversion C;subst.
        apply binds_mid_eq in H3.
        2:{ apply uniq_from_wf_env... }
        inversion H3;subst. eapply n with (A1:=A1').
        rewrite_alist ((E1 ++ a ~ bind_sub_lb t) ++ E2) in H6.
        apply exposure2_strengthening in H6...
        { rewrite app_assoc... }
        { apply wf_env_cons in H0. inversion H0... }
    }
    { right. intros A1' C. inversion C;subst.
      get_same_bind... }
  - left.  exists A. constructor...
Qed.

Lemma exposure2_mu_dec: forall E A,
  wf_env E -> WF E A ->
  { A1 | Algo.exposure2 E (typ_mu A1) A } + 
  { forall A1,  ~  Algo.exposure2 E (typ_mu A1) A }.
Proof with auto.
  intros. apply exposure2_mu_dec_aux with (k:=List.length E)...
Qed.

Lemma rt_expr_dec: forall  e,
  { rt_expr e } + { ~ rt_expr e }.
Proof with auto.
  intros. destruct e; try solve [right; intros C; inversion C].
  left. constructor...
  left. constructor...
Qed.



Lemma exposurei_dec_aux: forall k E A l,
  List.length E <= k ->
  wf_env E -> WF E A ->
  { A1 | Algo.exposure_i E A l A1 } +
  { forall A1 ,  ~  Algo.exposure_i E A l A1 }.
Proof with auto.
  intros k. induction k;intros.
  {
    induction A; 
    simpl in *; try solve [right; intros A1' C; inversion C].
    - left. exists typ_bot. constructor...
    - destruct E; simpl in H; try lia.
      right. intros A1' C. inversion C;subst.
      inversion H3.
    - destruct (Atom.eq_dec a l).
      + subst. left. exists A...
      + right. intros A1' C. inversion C;subst...
    - destruct IHA1.
      { inv H1... }
      { left. destruct s as [A' ?]. exists A'.
        apply Algo.exposurei_and1... }
      destruct IHA2.
      { inv H1... }
      { left. destruct s as [A' ?]. exists A'.
        apply Algo.exposurei_and2... }
      right. intros A' C. inv C.
      { apply n in H7... }
      { apply n0 in H7... }
  }
  induction A; simpl in H0; try solve [right; intros A1' C; inversion C].
  - left. exists typ_bot. constructor...
  - destruct (binds_key_dec E a).
    2:{ right. intros A1' C. inversion C;subst.
        apply n in H3...
    }
    destruct s. destruct x.
    {
      apply binds_In' in b.
      pose proof in_split' _ _ b EqDec_ab_eq.
      destruct H2 as [E1 [E2 ?]]. subst.
      destruct (IHk E2 t l)...
      { rewrite app_length in H. simpl in H. lia. }
      { apply wf_env_cons in H0. inversion H0;subst... }
      { apply wf_env_cons in H0. inversion H0;subst... }
      + left. 
        destruct s as [A1' ?]. exists A1'.
        apply Algo.exposurei_trans_tvar with (U:=t)...
        rewrite_alist (nil ++ (E1 ++ (a~ bind_sub t)) ++ E2).
        apply Algo.exposurei_weakening_bind2...
      + right. intros A1' C. inversion C;subst.
        apply binds_mid_eq in H3.
        2:{ apply uniq_from_wf_env... }
        inversion H3;subst. eapply n with (A1:=A1').
        rewrite_alist ((E1 ++ a ~ bind_sub t) ++ E2) in H5.
        apply exposurei_strengthening in H5...
        { rewrite app_assoc... }
        { apply wf_env_cons in H0. inversion H0... }
    }
    { right. intros A1' C. inversion C;subst.
      get_same_bind... }
    { right. intros A1' C. inversion C;subst.
      get_same_bind... }
  - destruct (Atom.eq_dec a l).
    + subst. left. exists A...
    + right. intros A1' C. inversion C;subst...
  - destruct IHA1.
    { inv H1... }
    { left. destruct s as [A' ?]. exists A'.
      apply Algo.exposurei_and1... }
    destruct IHA2.
    { inv H1... }
    { left. destruct s as [A' ?]. exists A'.
      apply Algo.exposurei_and2... }
    right. intros A' C. inv C.
    { apply n in H7... }
    { apply n0 in H7... }
Qed.

Lemma size_open_ee_var: forall e (x:atom),
  size_exp e = size_exp (open_ee e x).
Proof with auto.
  intros.
  unfold open_ee. generalize 0.
  induction e;intros;simpl...
  destruct (n0 == n)...
Qed.


Lemma size_open_te_var: forall e (x:atom),
  size_exp e = size_exp (open_te e x).
Proof with auto.
  intros.
  unfold open_te. generalize 0.
  induction e;intros;simpl...
Qed.


Lemma exposurei_dec: forall E A l,
  wf_env E -> WF E A ->
  { A1 | Algo.exposure_i E A l A1 } +
  { forall A1 ,  ~  Algo.exposure_i E A l A1 }.
Proof with auto.
  intros. apply exposurei_dec_aux with (k:=List.length E)...
Qed.

Lemma algotyping_dec : forall k E e,
  size_exp e <= k ->
  {A | Algo.typing E e A} + {forall A, ~ Algo.typing E e A}.
Proof with auto.
  intros k.
  induction k.
  {
    intros. destruct e; simpl in H; try lia.
  }
  intros.
  destruct (wf_env_dec E).
  2:{ right. intros A C. apply Algo.typing_regular in C.
    destruct_hypos... }
  intros. destruct e; simpl in H.
  -
    right. intros A C. inversion C.
  -
    destruct (binds_key_dec E a).
    2:{ right. intros A C. inversion C;subst.
        exfalso. apply n in H3... }
    destruct s. destruct x.
    { right. intros A C. inversion C;subst. get_same_bind. }
    { right. intros A C. inversion C;subst. get_same_bind. }
    left. exists t...
  -
    pick_fresh x.
    destruct (IHk (x ~ bind_typ t ++ E) (open_ee e (exp_fvar x))).
    { rewrite <- size_open_ee_var... lia. }
    + destruct s as [A' ?]. left.
      exists (typ_arrow t A')...
      eapply Algo.typing_abs with (L:={{x}} \u dom E ).
      intros. 
      rewrite_alist (nil ++ x0 ~ bind_typ t ++ E).
      rewrite subst_ee_intro with (x:=x)...
      apply Algo.typing_replacing...
      constructor...
      { apply Algo.typing_regular in t0. destruct_hypos.
        inversion H1;subst... }
    + right. intros A C. inversion C;subst.
      apply n with (A:=T1).
      pick_fresh x'.
      rewrite_alist (nil ++ x ~ bind_typ t ++ E).
      rewrite subst_ee_intro with (x:=x')...
      apply Algo.typing_replacing...
      { apply H4... }
      constructor...
      { apply Algo.typing_regular in C. destruct_hypos.
        inversion H2;subst... }
  -
    destruct (IHk E e1). { lia. }
    2:{
      right. intros A C.
      inversion C;subst.
      { apply n in H2... }
      { apply n in H2... }
    }
    destruct (IHk E e2). { lia. }
    2:{
      right. intros A C.
      inversion C;subst.
      { apply n in H5... }
      { apply n in H6... }
    }
    destruct s as [A1 Hty1], s0 as [A2 Hty2].
    assert (WF E A1).
    { apply Algo.typing_regular in Hty1. destruct_hypos... }
    destruct (exposure_bot_dec w H0)...
    { left. exists typ_bot.
      eapply Algo.typing_app_bot;eassumption.
    }
    destruct (exposure_arr_dec w H0)...
    { destruct s as [A1' [A2' ?]].
      destruct (@decidability A2 A1' E).
      + left. exists A2'.
        eapply Algo.typing_app;eassumption.
      + right. intros A C.
        inversion C;subst.
        { pose proof algotyping_uniq Hty1 H3.
          pose proof algotyping_uniq Hty2 H6. subst.
          pose proof exposure_uniq w e H4. inv H1.
          apply n0...
        }
        { pose proof algotyping_uniq Hty1 H3. subst.
          apply n...
        }
    }
    right. intros A C. inversion C;subst.
    { pose proof algotyping_uniq Hty1 H3. subst. 
      apply n0 in H4... }
    { pose proof algotyping_uniq Hty1 H3. subst. 
      apply n in H5... }
  -
    pick_fresh X.
    destruct (IHk (X ~ bind_sub t ++ E) (open_te e X)).
    { rewrite <- size_open_te_var... lia. }
    + destruct s as [A' ?]. left.
      exists (typ_all t (close_tt A' X))...
      eapply Algo.typing_tabs with (L:={{X}} \u dom E ).
      intros. 
      rewrite_alist (nil ++ X0 ~ bind_sub t ++ E).
      rewrite subst_te_intro with (X:=X)...
      rewrite <- open_close_reverse...
      2:{ apply Algo.typing_regular in t0. destruct_hypos.
        get_type... }
      apply Algo.typing_replacing2 with (E1:=nil)...
      { simpl. apply Algo.typing_regular in t0.
        destruct_hypos. inv H1. constructor... }
    + right. intros A C. inversion C;subst.
      apply n with (A:=open_tt T1 X).
      pick_fresh X'.
      rewrite_alist (nil ++ X ~ bind_sub t ++ E).
      rewrite subst_te_intro with (X:=X')...
      specialize_x_and_L X' L.
      apply Algo.typing_replacing2 with (E1:=nil) (Y:=X) in H4...
      2:{ apply Algo.typing_regular in H4. destruct_hypos.
          inversion H0;subst... constructor... }
      rewrite <- subst_tt_intro in H4...
  - 
    pick_fresh X.
    destruct (IHk (X ~ bind_sub_lb t ++ E) (open_te e X)).
    { rewrite <- size_open_te_var. lia. }
    + destruct s as [A' ?]. left.
      exists (typ_all_lb t (close_tt A' X))...
      eapply Algo.typing_tabs_lb with (L:={{X}} \u dom E ).
      intros. 
      rewrite_alist (nil ++ X0 ~ bind_sub_lb t ++ E).
      rewrite subst_te_intro with (X:=X)...
      rewrite <- open_close_reverse...
      2:{ apply Algo.typing_regular in t0. destruct_hypos.
        get_type... }
      apply Algo.typing_replacing2_lb with (E1:=nil)...
      { simpl. apply Algo.typing_regular in t0.
        destruct_hypos. inv H1. constructor... }
    + right. intros A C. inversion C;subst.
      apply n with (A:=open_tt T1 X).
      pick_fresh X'.
      rewrite_alist (nil ++ X ~ bind_sub_lb t ++ E).
      rewrite subst_te_intro with (X:=X')...
      specialize_x_and_L X' L.
      apply Algo.typing_replacing2_lb with (E1:=nil) (Y:=X) in H4...
      2:{ apply Algo.typing_regular in H4. destruct_hypos.
          inversion H0;subst... constructor... }
      rewrite <- subst_tt_intro in H4...
  - 
    (* tapp *)
    destruct (IHk E e). { lia. }
    2:{
      right. intros A C. inversion C;subst.
      + apply n in H2...
      + apply n in H2...
      + apply n in H2...
    }
    destruct s as [A ?].
    assert (WF E A). 
    { apply Algo.typing_regular in t0. destruct_hypos... }
    destruct (wf_dec (E:=E) t).
    { apply uniq_from_wf_env... }
    2:{ right. intros A' C. apply n. inversion C;subst...
      + get_well_form...
      + get_well_form...
    }
    destruct (exposure_bot_dec w H0).
    {
      left. exists typ_bot.
      eapply Algo.typing_tapp_bot;eassumption.
    }
    destruct (exposure_tabs_lb_dec w H0), 
      (exposure_tabs_dec w H0).
    {
      destruct s as [A1 [A2 ?]].
      destruct s0 as [A1' [A2' ?]].
      pose proof exposure_uniq w e0 e1. inversion H1;subst.
    }
    {
      destruct s as [A1 [A2 ?]].
      destruct (decidability A1 t E).
      + left. exists (open_tt A2 t).
        eapply Algo.typing_tapp_lb;eassumption.
      + right. intros A' C. inversion C;subst.
        * pose proof algotyping_uniq t0 H3.
          subst.
          pose proof exposure_uniq w e0 H5.
          inversion H1.
        * pose proof algotyping_uniq t0 H3.
          subst.
          pose proof exposure_uniq w e0 H5. inv H1.
          apply n1...
        * pose proof algotyping_uniq t0 H3.
          subst.
          pose proof exposure_uniq w e0 H5. inv H1.
    }
    {
      destruct s as [A1 [A2 ?]].
      destruct (decidability t A1 E).
      + left. exists (open_tt A2 t).
        eapply Algo.typing_tapp;eassumption.
      + right. intros A' C. inversion C;subst.
        * pose proof algotyping_uniq t0 H3.
          subst.
          pose proof exposure_uniq w e0 H5. inv H1.
          apply n1...
        * pose proof algotyping_uniq t0 H3.
          subst.
          pose proof exposure_uniq w e0 H5. inv H1.
        * pose proof algotyping_uniq t0 H3.
          subst.
          pose proof exposure_uniq w e0 H5. inv H1.
    }
    {
      right. intros A' C. inversion C;subst.
      * pose proof algotyping_uniq t0 H3.
        subst. apply n1 in H5...
      * pose proof algotyping_uniq t0 H3.
        subst. apply n0 in H5...
      * pose proof algotyping_uniq t0 H3.
        subst. apply n in H5...
    }
  -
    (* nat *)
    left. exists typ_nat...
  -
    (* unfold *)
    destruct (IHk E e). { lia. }
    2:{
      right. intros A C. inversion C;subst.
      + apply n in H2...
      + apply n in H2...
    }
    destruct s as [A ?].
    assert (WF E A). 
    { apply Algo.typing_regular in t0. destruct_hypos... }
    destruct (wf_dec (E:=E) t).
    { apply uniq_from_wf_env... }
    2:{ right. intros A' C. apply n. inversion C;subst...
      + get_well_form...
      + get_well_form...
    }
    destruct (decidability A t E).
    2:{ right. intros A' C. apply n. inversion C;subst...
      + pose proof algotyping_uniq t0 H3. subst...
      + pose proof algotyping_uniq t0 H3. subst...
    }
    destruct (exposure_bot_dec w w0).
    { left. exists typ_bot.
      eapply Algo.typing_unfold_bot;eassumption.
    }
    destruct (exposure_mu_dec w w0).
    { left. destruct s0 as [A' ?]. exists (open_tt A' t).
      eapply Algo.typing_unfold;eassumption.
    }
    { right. intros A' C. inversion C;subst.
      + apply n0 in H7...
      + apply n in H7...
    }
  -
    (* fold *)
    destruct (IHk E e). { lia. }
    2:{
      right. intros A C. inversion C;subst.
      + apply n in H2...
      + apply n in H2...
    }
    destruct s as [A ?].
    assert (WF E A). 
    { apply Algo.typing_regular in t0. destruct_hypos... }
    destruct (wf_dec (E:=E) t).
    { apply uniq_from_wf_env... }
    2:{ right. intros A' C. apply n. inversion C;subst... }
    destruct (exposure2_top_dec w w0).
    { left. exists typ_top.
      eapply Algo.typing_fold_top;eassumption. }
    destruct (exposure2_mu_dec w w0).
    { destruct s as [A' ?].
      destruct (decidability A (open_tt A' t) E).
      + left. exists t.
        eapply Algo.typing_fold;eassumption.
      + right. intros A'' C. inv C.
        * pose proof exposure_uniq2 w H6 e0.
          pose proof algotyping_uniq t0 H3.
          subst. inv H1. apply n0...
        * apply n...
    }
    { right. intros A' C. inv C.
      * apply n0 in H6...
      * apply n in H5... }
  -
    left. exists typ_top...
  -
    (* cons *)
    destruct (rt_expr_dec e2).
    2:{
      right. intros A' C. apply n. inv C.
      constructor... constructor...
    }
    destruct e2;
      try solve [right;intros A' C'; inv r].
    +
      (* single *)
      destruct (IHk E e1). { lia. }
      2:{
        right. intros A' C. inv C.
        apply n in H4...
      }
      destruct s as [A' ?]. left.
      exists (typ_single a A'). constructor...
    +
      (* cons *)
      destruct (IHk E e1). { lia. }
      2:{
        right. intros A' C. inv C.
        apply n in H7...
      }
      destruct s as [A1 ?].
      destruct (IHk E (exp_rcd_cons a0 e2_1 e2_2)).
      { simpl in H. simpl. lia. }
      2:{
        right. intros A' C. inv C.
        apply n in H8...
      }
      destruct s as [A2 ?].
      destruct (rt_expr_dec e2_2).
      2:{ right. intros A' C. inv C.
          apply n in H9...
      }
      destruct (KeySetProperties.In_dec a (union {{a0}} (collectLabele e2_2))).
      {
        right. intros A' C. inv C. fsetdec.
      }
      left. exists (typ_and (typ_single a A1) A2).
      constructor...
  -
    (* proj *)
    destruct (IHk E e). { lia. }
    2:{
      right. intros A' C. inv C.
      apply n in H3...
    }
    destruct s as [A' ?].
    assert (WF E A'). 
    { apply Algo.typing_regular in t. destruct_hypos... }
    destruct (exposurei_dec a w H0).
    + left. destruct s as [A1 ?].
      exists A1. eapply Algo.typing_proj;eauto.
    + right. intros A C. inv C.
      pose proof algotyping_uniq t H4.
      subst. apply n in H6...
Qed.



Lemma typing_dec : forall k E e A,
  size_exp e <= k ->
  {typing E e A} + {~ typing E e A}.
Proof with auto.
  intros.
  destruct (algotyping_dec E e H).
  +
    destruct s as [B ?].
    destruct (@decidability B A E).
    * left. eapply typing_sub; try eassumption.
      apply typing_algo_sound...
    * right. intros C. apply n.
      apply minimum_typing in C.
      destruct C as [B' [? ?]].
      pose proof algotyping_uniq t H0.
      subst...
  +
    right. intros C.
    apply minimum_typing in C.
    destruct C as [B [? ?]].
    apply n in H0...
Qed.


Lemma decidable_typing: forall E e A,
  {typing E e A} + {~ typing E e A}.
Proof with auto.
  intros.
  apply typing_dec with (k:=size_exp e)...
Qed.
