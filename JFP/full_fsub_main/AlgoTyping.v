Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Coq.micromega.Lia.
Require Export Progress.

Ltac inv H := inversion H; subst.

Module Algo.

(* This is the Algo typing for 
   Iso + Fsub, 
*)

Inductive exposure : env -> typ -> typ -> Prop :=
  | exposure_nat: forall E,
      exposure E typ_nat typ_nat
  | exposure_top : forall E,
      exposure E typ_top typ_top
  | exposure_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      exposure E U T ->
      exposure E (typ_fvar X) T
  | exposure_arrow: forall E A1 A2,
      exposure E (typ_arrow A1 A2) (typ_arrow A1 A2)
  | exposure_all : forall E S T,
      exposure E (typ_all S T) (typ_all S T)
  | exposure_rec: forall E A,
      exposure E (typ_mu A) (typ_mu A)
  | exposure_label: forall E X A,
      exposure E (typ_label X A) (typ_label X A)
  | exposure_rcd: forall E A,
      rt_type A ->
      exposure E A A
.


Inductive exposure2 : env -> typ -> typ -> Prop :=
  | exposure2_nat: forall E,
      exposure2 E typ_nat typ_nat
  | exposure2_top : forall E,
      exposure2 E (typ_mu typ_top) typ_top
  (* | exposure2_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      exposure2 E U T ->
      exposure2 E (typ_fvar X) T *)
  | exposure2_arrow: forall E A1 A2,
      exposure2 E (typ_arrow A1 A2) (typ_arrow A1 A2)
  | exposure2_all : forall E S T,
      exposure2 E (typ_all S T) (typ_all S T)
  | exposure2_rec: forall E A,
      exposure2 E (typ_mu A) (typ_mu A)
  | exposure2_label: forall E X A,
      exposure2 E (typ_label X A) (typ_label X A)
  | exposure2_rcd: forall E A,
      rt_type A ->
      exposure2 E A A
.


Inductive typing : env -> exp -> typ -> Prop :=
  | typing_nat: forall G,
    wf_env G ->
    typing G (exp_nat) (typ_nat)
  | typing_var : forall E x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E (exp_fvar x) T
  | typing_abs : forall L E V e1 T1,
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ V ++ E) (open_ee e1 x) T1) ->
      typing E (exp_abs V e1) (typ_arrow V T1)
  | typing_app : forall T11 T12 E e1 e2 T1 T2,
      typing E e1 T1 ->
      exposure E T1 (typ_arrow T11 T12) ->
      typing E e2 T2 ->
      sub E T2 T11 ->
      typing E (exp_app e1 e2) T12
  | typing_tabs : forall L E V e1 T1,
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_sub V ++ E) (open_te e1 X) (open_tt T1 X)) ->
      typing E (exp_tabs V e1) (typ_all V T1)
  | typing_tapp : forall E e1 T1 T11 T12 T2,
      typing E e1 T1 ->
      exposure E T1 (typ_all T11 T12) ->
      sub E T2 T11 ->
      typing E (exp_tapp e1 T2) (open_tt T12 T2)
  | typing_fold : forall G A S e T,
     typing G e S ->
     sub G S (open_tt A T) ->
     exposure2 G (typ_mu A) T ->
     WF G T -> (* cannot be removed  *)
     typing G (exp_fold T e) T
 (* | typing_fold_top : forall G S T e,
      typing G e S ->
      exposure2 G typ_top T ->
      WF G T ->
      typing G (exp_fold T e) typ_top *)
 | typing_unfold : forall G A A' T e,
     typing G e A' -> 
     sub G A' A ->
     exposure G A (typ_mu T) ->
     typing G (exp_unfold A e)  (open_tt T A)
  | typing_proj : forall G e T T' i Ti,
      typing G e T ->
      exposure G T T' ->
      Tlookup i T' = Some Ti ->
      typing G (exp_rcd_proj e i) Ti
  | typing_rcd_nil : forall G,
      wf_env G ->
      typing G exp_rcd_nil typ_rcd_nil
  | typing_rcd_cons: forall G e1 e2 T1 T2 i,
      typing G e1 T1 ->
      typing G e2 T2 ->
      rt_type T2 ->
      rt_expr e2 ->
      i \notin (collectLabele e2) ->
      typing G (exp_rcd_cons i e1 e2) (typ_rcd_cons i T1 T2)
.

#[global]
Hint Constructors exposure exposure2:core.


Lemma exposure_sound: forall E A B,
  wf_env E -> WF E A ->
  exposure E A B -> sub E A B.
Proof with auto.
  intros.
  induction H1;try solve [apply Reflexivity;auto]...
  - eapply sa_trans_tvar with (U:=U)...
    apply IHexposure... apply WF_from_binds_typ with (x:=X)...
Qed.


Lemma exposure2_sound: forall E A B,
  wf_env E -> WF E B ->
  exposure2 E A B -> sub E A B.
Proof with auto.
  intros.
  induction H1;try solve [apply Reflexivity;auto]...
  - constructor...
    apply WF_rec with (L:={})...
Qed.

Definition not_var_typ U :=
  match U with
  | typ_fvar _ => False
  | _ => True
  end.

Lemma exposure_promote: forall E S T U,
  WF E T ->
  exposure E S T -> sub E S U -> not_var_typ U ->
  sub E T U.
Proof with auto.
  intros. generalize dependent T.
  induction H1;intros...
  - inv H1...
  - inv H2...
    (* apply WF_rec with (L:={})... *)
  - inv H3;inv_rt. apply IHsub...
    + apply sub_regular in H1. destruct_hypos.
      pose proof binds_uniq _ _ _ H1 H H5. inversion H8.
      subst...
  - inv H0...
  - inv H4;inv_rt...
    eapply sa_all with (L:=L)...
  - inv H5;inv_rt. eapply sa_rec with (L:=L)...
  - inv H0...
  - inv H9;inv_rt...
Qed.


Lemma exposure_weakening: forall E S T X U,
  exposure E S T ->
  exposure (X ~ bind_sub U ++ E) S T.
Proof with auto.
  intros. induction H...
  eapply exposure_trans_tvar with (U:=U0)...
Qed.


Lemma exposure_weakening_bind: forall E S T a,
  exposure E S T ->
  exposure (a :: E) S T.
Proof with auto.
  intros. induction H...
  rewrite_env ([ a ] ++ E)...
  eapply exposure_trans_tvar with (U:=U)...
Qed.


Lemma exposure_weakening_bind2: forall E1 E2 S T a,
  exposure (E1 ++ E2) S T ->
  exposure (E1 ++ a ++ E2) S T.
Proof with auto.
  intros. dependent induction H...
  eapply exposure_trans_tvar with (U:=U)...
Qed.



Lemma exposure2_weakening: forall E S T X U,
  exposure2 E S T ->
  exposure2 (X ~ bind_sub U ++ E) S T.
Proof with auto.
  intros. induction H...
  (* eapply exposure_trans_tvar with (U:=U0)... *)
Qed.


Lemma exposure2_weakening_bind: forall E S T a,
  exposure2 E S T ->
  exposure2 (a :: E) S T.
Proof with auto.
  intros. induction H...
  (* rewrite_env ([ a ] ++ E)...
  eapply exposure_trans_tvar with (U:=U)... *)
Qed.


Lemma exposure2_weakening_bind2: forall E1 E2 S T a,
  exposure2 (E1 ++ E2) S T ->
  exposure2 (E1 ++ a ++ E2) S T.
Proof with auto.
  intros. dependent induction H...
  (* eapply exposure_trans_tvar with (U:=U)... *)
Qed.


Lemma exposure_ex: forall E A,
  wf_env E -> WF E A -> exists B,
  exposure E A B /\ not_var_typ B /\ WF E B.
Proof with auto.
  intros. revert A H0.
  induction E;intros...
  {
    dependent induction H0.
    (* + dependent induction H0. *)
    - exists typ_top;simpl...
    - exists typ_nat;simpl...
    - inv H0.
  
    - exists (typ_arrow A B).
      split;simpl...
    - exists (typ_all T1 T2).
      repeat split;simpl...
      apply WF_all with (L:=L)...
    - exists (typ_mu A).
      repeat split;simpl...
      apply WF_rec with (L:=L)...
    - exists (typ_label X A).
      repeat split;simpl...
    - exists (typ_rcd_nil)...
      repeat split;simpl...
    - exists (typ_rcd_cons i T1 T2)...
      repeat split;simpl...
  }

  {
    dependent induction H0.
    (* + dependent induction H0. *)
    - exists typ_top;simpl...
    - exists typ_nat;simpl...
    - inv H0.
      + inv H. dependent induction H5.
        * exists typ_top. repeat split;simpl...
          apply exposure_trans_tvar with (U:=typ_top)...
        * exists typ_nat. repeat split;simpl...
          apply exposure_trans_tvar with (U:=typ_nat)...
        * pose proof WF_from_binds_typ _ _ H4 H1.
          destruct (IHE H4 _ H2). destruct_hypos.
          exists x. repeat split;simpl...
          { apply exposure_trans_tvar with (U:= X0)...
            apply exposure_trans_tvar with (U:= U)...
            rewrite_env (X ~ bind_sub X0 ++ E).
            apply exposure_weakening...
          }
          { rewrite_env (nil ++ X ~ bind_sub X0 ++ E).
            eapply WF_weakening... }
        * inv H. exists (typ_arrow A B).
          repeat split;simpl...
          { apply exposure_trans_tvar with (U:=(typ_arrow A B))... }
          { rewrite_env (nil ++ X ~ bind_sub (typ_arrow A B) ++ E).
            eapply WF_weakening... }
        * inv H. exists (typ_all T1 T2).
          repeat split;simpl...
          { apply exposure_trans_tvar with (U:=(typ_all T1 T2))... }
          { rewrite_env (nil ++ X ~ bind_sub (typ_all T1 T2) ++ E).
            eapply WF_weakening... }
        * inv H. exists (typ_mu A).
          repeat split;simpl...
          { apply exposure_trans_tvar with (U:=(typ_mu A))... }
          { rewrite_env (nil ++ X ~ bind_sub (typ_mu A) ++ E).
            eapply WF_weakening... }
        * inv H. exists (typ_label X0 A).
          repeat split;simpl...
          { apply exposure_trans_tvar with (U:= (typ_label X0 A))... }
          { rewrite_env (nil ++ X ~ bind_sub  (typ_label X0 A) ++ E).
            eapply WF_weakening... }
        * exists typ_rcd_nil. repeat split;simpl...
          apply exposure_trans_tvar with (U:=typ_rcd_nil)...
        * inv H. exists (typ_rcd_cons i T1 T2).
          repeat split;simpl...
          { apply exposure_trans_tvar with (U:= (typ_rcd_cons i T1 T2))... }
          { rewrite_env (nil ++ X ~ bind_sub  (typ_rcd_cons i T1 T2) ++ E).
            eapply WF_weakening... }
      + assert (wf_env E). { inv H... }
        assert (WF E U).
        { eapply WF_from_binds_typ... apply H1. }
        destruct (IHE H2 _ H3) as [S ]. destruct_hypos.
        exists S. repeat split;simpl...
        { apply exposure_trans_tvar with (U:= U)...
          apply exposure_weakening_bind...
        }
        { rewrite_env (nil ++ [a] ++ E).
          apply WF_weakening... }
    - exists (typ_arrow A B).
      split;simpl...
    - exists (typ_all T1 T2).
      repeat split;simpl...
      apply WF_all with (L:=L)...
    - exists (typ_mu A).
      repeat split;simpl...
      apply WF_rec with (L:=L)...
    - exists (typ_label X A).
      repeat split;simpl...
    - exists (typ_rcd_nil)...
      repeat split;simpl...
    - exists (typ_rcd_cons i T1 T2)...
      repeat split;simpl...
  }
Qed.


Lemma exposure_WF: forall E A B,
  wf_env E -> WF E A -> exposure E A B ->
  WF E B.
Proof.
  intros.
  pose proof exposure_sound H H0 H1.
  apply sub_regular in H2.
  destruct_hypos. auto.
Qed.


Lemma exposure2_WF: forall E A B,
  wf_env E -> WF E B -> exposure2 E A B ->
  WF E A.
Proof.
  intros.
  pose proof exposure2_sound H H0 H1.
  apply sub_regular in H2.
  destruct_hypos. auto.
Qed.





Lemma typing_rt_expr_novar : forall E e (X:atom),
  typing E e X -> rt_expr e -> False.
Proof with auto.
  intros.
  dependent induction H;
  try match goal with
  | [H : rt_expr _ |- _] => inversion H
  end.
Qed.


Lemma typing_collectLabel_inclusion : forall E e T,
  typing E e T -> rt_type T -> rt_expr e ->
  collectLabel T [<=]
  collectLabele e.
Proof with auto.
  intros. induction H;inv_rt;try solve [inversion H1].
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
    pose proof exposure_WF H3 H8 H0.
    dependent destruction H9...
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
    pose proof exposure_WF H2 H4 H0.
    dependent destruction H5.
    repeat split...
    constructor...
    get_type...
    pick fresh X.
    rewrite subst_tt_intro with (X:=X)...
    rewrite_env (map (subst_tb X  T2) nil ++ E).
    apply subst_tb_wf with (Q:=bind_sub T11)...
    apply H6...
    get_well_form...
  -
    repeat split...
    get_type...
  (* -
    (* apply exposure2_sound in H1... *)
    get_well_form...
    repeat split...
    constructor...
    apply WF_type with (E:=G)...
    get_well_form... *)
  -
    repeat split...
    constructor... 
    apply WF_type with (E:=G)... { get_well_form... }
    apply sub_regular in H0. destruct_hypos...
    apply wf_open_rec2...
    apply exposure_WF in H1...
  -
    repeat split...
    apply wf_rcd_lookup with (i:=i) (T:=T')...
    apply exposure_sound in H0... get_well_form...
  -
    repeat split...
    constructor...
    rewrite typing_collectLabel_inclusion...
    apply H0.
Qed.


Lemma exposure_typ_strengthening: forall E1 E2 S T X U,
  exposure (E1 ++ X ~ bind_typ U ++ E2) S T ->
  exposure (E1 ++ E2) S T.
Proof with auto.
  intros. dependent induction H...
  eapply exposure_trans_tvar with (U:=U0)...
  2:{ apply IHexposure with (X0:=X) (U1:=U)... }
  apply binds_app_iff in H. destruct H.
  { apply binds_app_iff. left... }
  apply binds_app_iff in H. destruct H.
  { inv H. inv H1. inv H1. }
  apply binds_app_iff. right...
Qed.


Lemma exposure2_typ_strengthening: forall E1 E2 S T X U,
  exposure2 (E1 ++ X ~ bind_typ U ++ E2) S T ->
  exposure2 (E1 ++ E2) S T.
Proof with auto.
  intros. dependent induction H...
  (* eapply exposure_trans_tvar with (U:=U0)...
  2:{ apply IHexposure with (X0:=X) (U1:=U)... }
  apply binds_app_iff in H. destruct H.
  { apply binds_app_iff. left... }
  apply binds_app_iff in H. destruct H.
  { inv H. inv H1. inv H1. }
  apply binds_app_iff. right... *)
Qed.



Lemma typing_replacing: forall E1 E2 e T U X Y,
  typing (E1++ X ~ bind_typ U ++E2) e T ->
  X <> Y ->
  wf_env ( E1 ++ Y ~ bind_typ U ++ E2) ->
  typing (E1 ++ Y ~ bind_typ U ++E2) (subst_ee X Y e) T.
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros.
  - constructor. auto.
  - simpl. destruct (x == X)...
    { subst. apply typing_var...
      assert (binds X (bind_typ U) (E1 ++ X ~ bind_typ U ++ E2))...
      pose proof binds_unique _ _ _ _ _ H0 H3.
      rewrite H4... apply uniq_from_wf_env... }
    { apply typing_var with (T:=T)... analyze_binds H0. }
  - apply typing_abs with (L:=L \u {{ X }}
      \u dom (E1 ++ Y ~ bind_typ U ++ E2) )...
    intros.
    specialize_x_and_L x L.
    rewrite subst_ee_open_ee_var...
    rewrite_env ((x~bind_typ V ++ E1) ++ Y ~ bind_typ U ++ E2).
    apply H0...
    rewrite_env (x~bind_typ V ++ (E1 ++ Y ~ bind_typ U ++ E2)).
    constructor...
    { apply typing_regular in H. destruct_hypos.
      inv H... rewrite_env (E1 ++ X ~ bind_typ U ++ E2) in H10.
      apply wf_typ_strengthening in H10.
      apply WF_weakening... }
  - apply typing_app with (T11:=T11) (T2:=T2) (T1:=T1)...
    + apply exposure_typ_strengthening in H0.
      apply exposure_weakening_bind2...
    + apply Sub_weakening... apply Sub_typ_strengthening in H2...
  - simpl. apply typing_tabs with (L:=L \u {{ X }}
  \u dom (E1 ++ Y ~ bind_typ U ++ E2) ).
    intros.
    specialize_x_and_L X0 L.
    rewrite subst_ee_open_te_var...
    rewrite_env ((X0~bind_sub V ++ E1) ++ Y ~ bind_typ U ++ E2).
    apply H0...
    rewrite_env (X0~bind_sub V ++ (E1 ++ Y ~ bind_typ U ++ E2)).
    constructor...
    { apply typing_regular in H. destruct_hypos.
      inv H... rewrite_env (E1 ++ X ~ bind_typ U ++ E2) in H10.
      apply wf_typ_strengthening in H10.
      apply WF_weakening... }
  - apply typing_tapp with (T11:=T11) (T2:=T2) (T1:=T1)...
    + apply exposure_typ_strengthening in H0.
      apply exposure_weakening_bind2...
    + apply Sub_weakening... apply Sub_typ_strengthening in H1...
  - apply typing_fold with (T:= T) (S:=S)(A:=A)...
    + apply Sub_weakening... apply Sub_typ_strengthening in H0...
    + apply exposure2_typ_strengthening in H1.
      apply exposure2_weakening_bind2...
    + apply WF_weakening... apply wf_typ_strengthening in H2...
  (* - apply typing_fold_top with (S:=S)...
    + apply exposure2_typ_strengthening in H0.
      apply exposure2_weakening_bind2...
    + apply WF_weakening... apply wf_typ_strengthening in H1... *)
  - apply typing_unfold with (A:= A) (A' := A')...
    + apply Sub_weakening... apply Sub_typ_strengthening in H0...
    + apply exposure_typ_strengthening in H1.
      apply exposure_weakening_bind2...
    (* + apply Sub_weakening... apply Sub_typ_strengthening in H1... *)
  - apply typing_proj with (T:=T)(T':=T')...
    + apply exposure_typ_strengthening in H0.
      apply exposure_weakening_bind2...
  - simpl. apply typing_rcd_nil...
  - simpl. apply typing_rcd_cons...
    + apply IHtyping1...
    + apply IHtyping2...
    + apply subst_tt_rt_expr... apply typing_regular in H0.
      destruct_hypos...
    + rewrite <- label_choose_reserve_e...
      apply typing_regular in H0. destruct_hypos...
Qed.


Lemma uniq_map_app_r:
  forall (A : Type) (E F : list (atom * A)) (f : A -> A),
  uniq (map f F ++ E) -> uniq (F ++ E).
Proof.
  intros.
  apply uniq_app_iff in H. apply uniq_app_iff.
  destruct_hypos. repeat split;auto.
  { apply uniq_map_1 in H. auto. }
  { apply disjoint_map_1 in H1. auto. }
Qed.

Lemma binds_typ_replacing_subst_tb: forall E X Y T x,
  binds x (bind_typ T) E ->
  binds x (bind_typ (subst_tt X Y T)) ((map (subst_tb X Y) E)).
Proof.
  intros. induction E.
  - inv H.
  - destruct H.
    + subst. left. reflexivity.
    + right. apply IHE. auto.
Qed.

Lemma binds_sub_replacing_subst_tb: forall E X Y T x,
  binds x (bind_sub T) E ->
  binds x (bind_sub (subst_tt X Y T)) ((map (subst_tb X Y) E)).
Proof.
  intros. induction E.
  - inv H.
  - destruct H.
    + subst. left. reflexivity.
    + right. apply IHE. auto.
Qed.


Lemma binds_sub_replacing: forall E1 E2 U X Y x T,
    binds  x (bind_sub T) (E1++ X ~ bind_sub U ++E2) ->
    X <> Y -> x <> X ->
    wf_env ( E1 ++ X ~ bind_sub U ++ E2) ->
    binds  x (bind_sub (subst_tt X Y T)) (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++E2).
Proof with auto.
  intros.
  apply binds_app_iff in H. apply binds_app_iff.
  destruct H.
  - left. apply binds_sub_replacing_subst_tb...
  - right. inv H. { inv H3... exfalso... }
    apply wf_env_cons in H2. inv H2.
    pose proof WF_from_binds_typ _ _ H7 H3.
    apply WF_imply_dom in H4.
    rewrite <- subst_tt_fresh...
Qed.


Lemma exposure_replacing: forall E1 E2 A B U X Y,
    exposure (E1++ X ~ bind_sub U ++E2) A B ->
    wf_env ((E1++ X ~ bind_sub U ++E2) ) ->
    X <> Y ->
    wf_env (map (subst_tb X Y)  E1 ++ Y ~ bind_sub U ++ E2) ->
    exposure (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros;simpl;try solve [rewrite_alist (map (subst_tb X Y) E1 ++ [(Y, bind_sub U)] ++ E2);constructor;auto;apply WF_replacing;auto]...
  -
    destruct (X0==X)...
    + subst. assert (binds X (bind_sub U) (E1 ++ X ~ bind_sub U ++ E2) )...
      pose proof binds_uniq _ _ _ H1 H H4. inversion H5; subst.
      apply exposure_trans_tvar with (U:=subst_tt X Y U)...
      * rewrite <- subst_tt_fresh...
        apply wf_env_cons in H1. inv H1.
        apply WF_imply_dom in H10...
      * apply IHexposure...
    + apply exposure_trans_tvar with (U:=subst_tt X Y U0)...
      2:{ apply IHexposure... }
      apply binds_sub_replacing...
  - apply exposure_rcd. 
      apply Infrastructure.subst_tt_rt_type...

Qed.


Lemma exposure2_replacing: forall E1 E2 A B U X Y,
    exposure2 (E1++ X ~ bind_sub U ++E2) A B ->
    wf_env ((E1++ X ~ bind_sub U ++E2) ) ->
    X <> Y ->
    wf_env (map (subst_tb X Y)  E1 ++ Y ~ bind_sub U ++ E2) ->
    exposure2 (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros;simpl;try solve [rewrite_alist (map (subst_tb X Y) E1 ++ [(Y, bind_sub U)] ++ E2);constructor;auto;apply WF_replacing;auto]...
  - apply exposure2_rcd. 
    apply Infrastructure.subst_tt_rt_type...
Qed.


Lemma typing_replacing2: forall E1 E2 e T U X Y,
  typing (E1++ X ~ bind_sub U ++E2) e T ->
  X <> Y ->
  wf_env ( map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++ E2) ->
  typing (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++E2) (subst_te X Y e) (subst_tt X Y T).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros.
  - constructor. auto.
  - destruct (x == X)...
    { subst. apply typing_var...
      assert (binds X (bind_sub U) (E1 ++ X ~ bind_sub U ++ E2))...
      pose proof binds_unique _ _ _ _ _ H0 H3.
      apply uniq_from_wf_env in H.
      specialize (H4 H). inv H4.
    }
    { apply typing_var... apply binds_app_iff in H0. apply binds_app_iff.
      destruct H0.
      - left. apply binds_typ_replacing_subst_tb... 
      - right. destruct H0. { inv H0... }
        apply wf_env_cons in H. inv H.
        pose proof wf_typ_from_binds_typ _ _ H6 H0.
        apply WF_imply_dom in H3.
        rewrite <- subst_tt_fresh...
    }
  - simpl. apply typing_abs with (L:=L \u {{ X }} \u
      dom (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++ E2)
     )...
    intros.
    specialize_x_and_L x L.
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb X Y) (x ~ bind_typ V ++ E1) ++ Y ~ bind_sub U ++ E2).
    apply H0...
    rewrite_env (x ~ bind_typ (subst_tt X Y V) ++ (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++ E2)).
    constructor...
    { apply typing_regular in H. destruct_hypos.
      inv H... rewrite_env (E1 ++ (X ~ bind_sub U) ++ E2) in H10.
      apply WF_replacing... }
  - simpl. apply typing_app with (T11:= subst_tt X Y T11) (T2:=subst_tt X Y T2) (T1:=subst_tt X Y T1)...
    + apply IHtyping1...
    + 
      eapply exposure_replacing with (Y:=Y) in H0...
      apply typing_regular in H... destruct_hypos...
    + apply IHtyping2... 
    + apply sub_replacing...
  - simpl. apply typing_tabs with (L:=L \u {{ X }}
  \u dom (E1 ++ Y ~ bind_typ U ++ E2) ).
    intros.
    specialize_x_and_L X0 L.
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env ( map (subst_tb X Y) (X0~bind_sub V ++ E1) ++ Y ~ bind_sub U ++ E2).
    apply H0...
    rewrite_env (X0~bind_sub (subst_tt X Y V) ++ (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++ E2)).
    constructor...
    { apply typing_regular in H. destruct_hypos.
      inv H... rewrite_env(E1 ++ (X ~ bind_sub U) ++ E2) in H10.
      apply WF_replacing... }
  - simpl. rewrite subst_tt_open_tt...
    apply typing_tapp with (T11:=subst_tt X Y T11) (T2:=subst_tt X Y T2) (T1:=subst_tt X Y  T1)...
    + apply IHtyping...
    + eapply exposure_replacing with (Y:=Y) in H0...
      apply typing_regular in H... destruct_hypos...
    + apply sub_replacing...
  - simpl. apply typing_fold with 
      (S:= subst_tt X Y S) (A:=subst_tt X Y  A)
      (T:= subst_tt X Y T)...
    + apply IHtyping...
    + apply sub_replacing with (Y:=Y) in H0...
      rewrite subst_tt_open_tt in H0...
    + apply exposure2_replacing with (Y:=Y) in H1...
      get_well_form...
    (* + apply sub_replacing with (Y:=Y) in H1... *)
    + apply WF_replacing with (Y:=Y) in H2...
  (* - simpl. apply typing_fold_top with (S:=subst_tt X Y S)... 
    + apply IHtyping...
    + apply exposure2_replacing with (Y:=Y) in H0...
      apply typing_regular in H... destruct_hypos...
    + apply WF_replacing with (Y:=Y) in H1... *)
  - simpl. rewrite subst_tt_open_tt...
    apply typing_unfold with (A':= subst_tt X Y A') (A:= subst_tt X Y A)...
    + apply IHtyping...
    + apply sub_replacing with (Y:=Y) in H0...
    + apply exposure_replacing with (Y:=Y) in H1...
      get_well_form...
  - simpl. apply typing_proj with (T:=subst_tt X Y T) (T':=subst_tt X Y T')...
    + apply IHtyping...
    + apply exposure_replacing with (Y:=Y) in H0...
      apply typing_regular in H. destruct_hypos...
    + apply lookup_some_subst...
      { apply typing_regular in H. destruct_hypos...
        apply exposure_sound in H0... get_well_form...
        get_type... }
      { destruct T';inversion H1... }
  - simpl. apply typing_rcd_nil...
  - simpl. apply typing_rcd_cons...
    + apply IHtyping1...
    + apply IHtyping2...
    + apply Infrastructure.subst_tt_rt_type...
    + apply subst_te_rt_expr... apply typing_regular in H0.
      destruct_hypos...
    + apply subst_te_collect...
      apply typing_regular in H0. destruct_hypos...
Qed.


Lemma typing_replacing_var: forall E2 A U X Y T,
    typing (X ~ bind_typ U ++E2) (open_ee A X) T ->
    X \notin fv_ee A \u  {{Y}} ->
    wf_env (Y ~ bind_typ U ++ E2) ->
    typing (Y ~ bind_typ U ++E2) (open_ee A Y) T.
Proof with auto.
  intros.
  rewrite_env (nil ++ Y ~ bind_typ U ++ E2).
  rewrite subst_ee_intro with (x:=X)...
  apply typing_replacing...
Qed.


End Algo.

#[export]
Hint Constructors Algo.typing : core.


Lemma sub_inv_arrow: forall E A T1 T2, sub E A (typ_arrow T1 T2) ->
  (exists X:atom, A = X) \/
  (exists S1 S2, A = typ_arrow S1 S2 /\ sub E T1 S1 /\ sub E S2 T2).
Proof.
  intros.
  dependent induction H;inv_rt.
  - left. exists X. auto.
  - right. exists A1, A2. auto.
Qed. 

Lemma sub_inv_all: forall E A T1 T2, sub E A (typ_all T1 T2) ->
  (exists X:atom, A = X) \/
  (exists S1 S2, A = typ_all S1 S2 /\
   (* equiv E A (typ_all S1 S2) /\ *)
    sub E (typ_all S1 S2) (typ_all T1 T2)).
Proof with auto.
  intros.
  dependent induction H;inv_rt.
  - left. exists X. auto.
  - right.
    exists S1, T0.
    split...
    apply sa_all with (L:=L)...
Qed.


(* WFC typ n : type with < k binded variables *)
Inductive WFD :  typ -> nat -> Prop :=
| WD_nat: forall k,
    WFD typ_nat k
| WD_top: forall k,
    WFD typ_top k
| WD_fvar: forall X k,
    WFD (typ_fvar X) k
| WD_bvar: forall b k,
    b < k ->
    WFD (typ_bvar b) k
| WD_arrow: forall A B k,
    WFD A k ->
    WFD B k ->
    WFD (typ_arrow A B) k
| WD_rec: forall A n,
    WFD A (S n) ->
    WFD (typ_mu A) n
| WD_all: forall A B n,
    WFD A n ->
    WFD B (S n) ->
    WFD (typ_all A B) n
| WD_rcd: forall l A k,
    WFD A k ->
    WFD (typ_label l A) k
| WD_nil: forall k,
    WFD typ_rcd_nil k
| WD_cons: forall i A B k,
    WFD A k ->
    WFD B k ->
    WFD (typ_rcd_cons i A B) k
.

#[export] Hint Constructors WFD : core.

Fixpoint close_tt_rec (K : nat) (Z : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat      
  | typ_top         => typ_top              
  | typ_bvar J      => typ_bvar J
  | typ_fvar X      => if X == Z then typ_bvar K else typ_fvar X 
  | typ_arrow T1 T2 => typ_arrow (close_tt_rec K Z T1) (close_tt_rec K Z T2)
  | typ_mu T        => typ_mu (close_tt_rec (S K) Z T)
  | typ_all A B     => typ_all (close_tt_rec K Z A) 
                                (close_tt_rec (S K) Z B)
  | typ_label l T => typ_label l (close_tt_rec K Z T)
  | typ_rcd_nil => typ_rcd_nil
  | typ_rcd_cons i A B => typ_rcd_cons i (close_tt_rec K Z A) (close_tt_rec K Z B)
  end.

Definition close_tt T X := close_tt_rec 0 X T.


Lemma open_close_reverse_rec: forall T X X0,
  (* (X \notin fv_tt T \u {{X0}}) ->  *)
  (* (X0 \notin fv_tt T) -> *)
  forall k, WFD T k ->
  subst_tt X X0 T = open_tt_rec k X0 (close_tt_rec k X T).
   (* subst_tt X0 X T = close_tt_rec k X (open_tt_rec k (typ_fvar X0) T). *)
Proof with auto.
  intros T.
  induction T;intros;simpl in *;try solve [f_equal;auto]...
  - inv H. destruct (k == n);try lia...
  - destruct (a == X)... simpl. destruct (k == k); try lia...
  - inv H. rewrite IHT1 with (k:=k)...
    rewrite IHT2 with (k:=k)...
  - inv H. rewrite IHT1 with (k:=k)...
    rewrite IHT2 with (k:=S k)...
  - inv H. rewrite IHT with (k:=S k)...
  - inv H. rewrite IHT with (k:=k)...
  - inv H. rewrite IHT1 with (k:=k)... rewrite IHT2 with (k:=k)...
Qed.


Lemma close_wfd : forall A X,
    WFD A 0 ->
    WFD (close_tt A X) 1.
Proof with auto.  
  intros A.
  unfold close_tt.
  generalize 0.
  induction A;intros;try solve [dependent destruction H;simpl in *;auto]...
  -
    simpl...
    destruct (a==X)...
Qed.


Lemma close_open_reverse_rec: forall T X,
    (X \notin fv_tt T) -> forall k, T = close_tt_rec k X (open_tt_rec k (typ_fvar X) T).
Proof with auto.
  intros T.
  induction T;intros;simpl in *;try solve [f_equal;auto]...
  -   
    destruct (k==n)...
    simpl...
    destruct (X==X)...
    destruct n0...
  -
    destruct (a==X)...
    apply notin_singleton_1 in H...
    destruct H...
Qed.

Lemma close_open_reverse: forall T X,
    (X \notin fv_tt T) ->  T = close_tt (open_tt T (typ_fvar X)) X.
Proof with auto.
  intros.
  apply close_open_reverse_rec...
Qed.


Lemma close_type_wfd: forall A,
    type A -> WFD A 0.
Proof with auto.
  intros.
  induction H;intros...
  - pick fresh X.
    specialize_x_and_L X L.
    constructor...
    apply close_wfd with (X:=X) in H0.
    rewrite <-close_open_reverse in H0...
  - (* WFD_all *)
    constructor...
    pick_fresh X.
    specialize_x_and_L X L.
    apply close_wfd with (X:=X) in H1.
    rewrite <- close_open_reverse in H1...
Qed.


Lemma open_close_reverse: forall T (X0 X:atom),
  type T ->
  (* (X \notin fv_tt T \u {{ X0 }}) ->  *)
   subst_tt X X0 T = open_tt (close_tt T X) X0.
Proof with auto.
intros. unfold open_tt, close_tt.
rewrite <- open_close_reverse_rec...
apply close_type_wfd...
Qed.



Lemma wf_open_all: forall A B G T,
    WF G T ->
    WF G (typ_all A B) -> WF G (open_tt B T).
Proof with auto.
  intros.
  dependent destruction H0.
  pick fresh X.
  rewrite subst_tt_intro with (X:=X)...
  rewrite_env (map (subst_tb X T) nil ++ E).
  apply subst_tb_wf with (Q:=bind_sub A)...
  apply H1...
Qed.


Lemma sub_rcd_proper: forall E a T1 T2 T1' T2',
  sub E T1 T1' ->
  sub E T2 T2' -> 
  rt_type T2 -> rt_type T2' ->
  a `notin` collectLabel T2 ->
  sub E (typ_rcd_cons a T1 T2) (typ_rcd_cons a T1' T2').
Proof with auto.
  intros.
  apply sa_rcd...
  + get_well_form...
  + simpl.
    rewrite <- !KeySetProperties.add_union_singleton.
    apply add_s_m...
    inversion H0;subst;inv_rt...
  + constructor;try solve [get_well_form;auto]...
  + constructor;try solve [get_well_form;auto]...
    inversion H0;subst;inv_rt...
  + intros. simpl in H4, H5. destruct (a==i).
    * inversion H4;subst. inversion H5;subst...
    * inversion H0;subst;inv_rt...
      apply H12 with (i:=i)...
Qed.


Theorem minimum_typing: forall E e T, typing E e T -> 
exists S, Algo.typing E e S /\ sub E S T .
(* /\ expr_label E e (collectLabel T). *)
Proof with auto.
  intros.
  induction H.
  - 
    exists typ_nat...
  - 
    exists T. split...
    (* 2:{ apply expr_label_var with (T:=T)... } *)
    apply Reflexivity...
    eapply wf_typ_from_binds_typ with (x:=x)...
    
  - 
    pick_fresh X. specialize_x_and_L X L.
    destruct H0 as [T2 [? ?]].
    assert (Hwf: wf_env E). 
    { apply typing_regular in H.
      destruct_hypos. inv H... }
    exists (typ_arrow V T2). split...
    { apply Algo.typing_abs with (L:=L \u {{X}} \u dom E).
      intros.
      apply Algo.typing_replacing_var with (X:=X)...
      apply typing_regular in H... destruct_hypos.
      inv H...
    }
    { eapply sa_arrow.
      { apply Reflexivity... 
        apply typing_regular in H.
        destruct_hypos. inv H... }
      rewrite_env (nil ++ X ~ bind_typ V ++ E) in H1.
      apply Sub_typ_strengthening in H1... }
  -
    destruct IHtyping1 as [Tarr' [? ?]].
    destruct IHtyping2 as [T2' [? ?]].
    pose proof sub_regular H2. destruct_hypos.
    destruct (Algo.exposure_ex H5 H6) as [N1 [? [? ?]]].
    epose proof Algo.exposure_promote H10 H8 H2 I.
    destruct (sub_inv_arrow H11) as [|].
    { destruct H12. subst. inv H9.  }
    destruct H12 as [N11 [N12 ?]]. destruct_hypos.
    exists N12. split...
    eapply Algo.typing_app with (T11:=N11) (T1:=Tarr') (T2:=T2')...
    { subst... }
    { eapply sub_transitivity with (Q:=T1)... }
  -
    pick_fresh X. specialize_x_and_L X L.
    destruct H0 as [S ]. destruct_hypos.
    assert (Hwf: wf_env E). 
    { apply typing_regular in H.
      destruct_hypos. inv H... }
    exists (typ_all V (close_tt S X)). split...
    { apply Algo.typing_tabs with (L:=L \u {{X}} \u dom E).
      intros. 
      rewrite <- open_close_reverse...
      2:{ apply Algo.typing_regular in H0. destruct_hypos...
          apply WF_type in H4... }
      replace (open_te e1 X0) with (subst_te X X0 (open_te e1 X)).
      2:{ rewrite <- subst_te_intro... }
      rewrite_env (map (subst_tb X X0) nil ++ X0 ~ bind_sub V ++ E).
      apply Algo.typing_replacing2...
      { constructor...
        apply sub_regular in H1. destruct_hypos.
        inv H1...
      }
    }
    { eapply sa_all with (L:=L \u {{X}} \u dom E).
      { apply Reflexivity...
        apply typing_regular in H.
        destruct_hypos. inv H... }
      (* { apply Reflexivity...
        apply typing_regular in H.
        destruct_hypos. inv H... } *)
      intros.
      rewrite <- open_close_reverse...
      2:{ apply Algo.typing_regular in H0. destruct_hypos...
          apply WF_type in H4... }
      replace (open_tt T1 X0) with (subst_tt X X0 (open_tt T1 X)).
      2:{ rewrite <- subst_tt_intro... }
      rewrite_env (map (subst_tb X X0) nil ++ X0 ~ bind_sub V ++ E).
      apply sub_replacing...
      { constructor...
        apply sub_regular in H1. destruct_hypos.
        inv H1...
      }
    }
  -
    destruct IHtyping as [Tall' ?]. destruct_hypos.
    pose proof sub_regular H2. destruct_hypos.
    destruct (Algo.exposure_ex H3 H4) as [N1 [? [? ?]]].
    epose proof Algo.exposure_promote H8 H6 H2 I. simpl in H9.
    destruct (sub_inv_all H9) as [|].
    { destruct H10. subst. inv H7.  }
    destruct H10 as [S1 [S2 ?]]. destruct_hypos.
    subst.

    exists (open_tt S2 T). split...
    { eapply Algo.typing_tapp with (T11:=S1) (T1:=Tall')...
      eapply sub_transitivity with (Q:=T1)...
      inv H11;inv_rt...
    }
    {
      inv H11; inv_rt...
      pick_fresh X0.
      rewrite_env (map (subst_tb X0 T) nil ++ E).
      replace (open_tt S2 T) with (subst_tt X0 T (open_tt S2 X0)).
      2:{ rewrite <- subst_tt_intro... }
      replace (open_tt T2 T) with (subst_tt X0 T (open_tt T2 X0)).
      2:{ rewrite <- subst_tt_intro... }
      apply sub_through_subst_tt with (Q:=T1)...
      apply H17...
    }
  -
    destruct IHtyping as [S]. destruct_hypos.
    pose proof sub_regular H2. destruct_hypos.

    dependent destruction H;inv_rt.
    { 
      exists (typ_top). split...
      eapply  Algo.typing_fold with (S:=S) (A:=typ_top)...
    }

    assert (WF E (typ_mu A2)).
    { apply WF_rec with (L:=L)...
      intros. specialize_x_and_L X L. get_well_form... }
    
    exists (typ_mu A2). split...
    2:{ apply Reflexivity... }
    eapply  Algo.typing_fold with (S:=S) (A:=A2)...
      (* 2:{ constructor... } *)
      eapply sub_transitivity with (Q:=open_tt A (typ_mu A2))...
      
      { pick_fresh Y.
        specialize_x_and_L Y L.
        apply sub_nominal_inversion in H1...
        rewrite subst_tt_intro with (X:=Y)...
        rewrite subst_tt_intro with (X:=Y) (U:=typ_mu A2)...
        rewrite_env (map (subst_tb Y (typ_mu A2)) nil ++ E).
        apply sub_through_subst_tt with (Q:=typ_top)... }


  -

    destruct IHtyping as [S]. destruct_hypos.
    pose proof sub_regular H0. destruct_hypos.
    pose proof sub_regular H2. destruct_hypos.
    destruct (Algo.exposure_ex H3 H4) as [N ]. destruct_hypos.
    (* pose proof sub_transitivity H2 H0. *)
    epose proof Algo.exposure_promote H11 H9 H0 I.
    dependent destruction H12;inv_rt.
    { inversion H10. }
    exists (open_tt A1 A).
    split...
    { 
      eapply Algo.typing_unfold with (A' := S)... }
    { pick_fresh Y.
      specialize_x_and_L Y L.
      apply sub_nominal_inversion in H14...
      rewrite subst_tt_intro with (X:=Y)...
      rewrite subst_tt_intro with (X:=Y) (U:=A)...
      rewrite_env (map (subst_tb Y A) nil ++ E).
      apply sub_through_subst_tt with (Q:=typ_top)... }

  - 
    destruct IHtyping as [S']. destruct_hypos.
    exists S'. split...
    apply sub_transitivity with (Q:=S)...
  -
    destruct IHtyping as [S']. destruct_hypos.
    pose proof sub_regular H2. destruct_hypos.
    destruct (Algo.exposure_ex H3 H4) as [N ]. destruct_hypos.
    assert (Algo.not_var_typ T). { destruct T;try inversion H0... simpl... }
    epose proof Algo.exposure_promote H8 H6 H2 H9.
    destruct (rcd_types_match _ H10 H0).
    2:{ destruct H11. subst. inversion H7. }
    destruct H11 as [Ti']. destruct_hypos.
    exists Ti'. split...
    apply Algo.typing_proj with (T:=S') (T':=N)...
  -
    exists typ_rcd_nil. split...
    constructor...
    + reflexivity.
    + intros. inversion H0.
  -
    destruct IHtyping1 as [T1' [? ?]].
    destruct IHtyping2 as [T2' [? ?]].
    assert (rt_type T2').
    { dependent destruction H7;inv_rt...
      { apply Algo.typing_rt_expr_novar in H6... destruct H6. }
    }
    exists (typ_rcd_cons i T1' T2')... split...
    + apply sub_rcd_proper...
      rewrite Algo.typing_collectLabel_inclusion... apply H6.
Qed.

Theorem typing_algo_sound: forall E e T, Algo.typing E e T ->
  typing E e T.
Proof with auto.
  intros.
  induction H...
  - apply typing_abs with (L:=L)...
  - eapply typing_app with (T1:=T11).
    + apply typing_sub with (S:=T1)...
      apply Algo.typing_regular in H. destruct_hypos.
      apply Algo.exposure_sound...
    + apply typing_sub with (S:=T2)...
  - apply typing_tabs with (L:=L)...
  - apply typing_tapp with (T1:=T11)...
    + apply typing_sub with (S:=T1)...
      apply Algo.typing_regular in H. destruct_hypos.
      apply Algo.exposure_sound...
  - apply typing_fold with (A:=A)...
    (* + apply Reflexivity... get_well_form...  *)
    + apply Algo.exposure2_sound... get_well_form...
    + apply typing_sub with (S:=S)...
  (* - inversion H0;subst;inv_rt.
    apply typing_fold with (A:=typ_top)...
    + apply Algo.typing_regular in H. destruct_hypos. apply sa_top...
      apply WF_rec with (L:={})...
    + unfold open_tt. simpl. apply typing_sub with (S:=S)...
      apply Algo.typing_regular in H. destruct_hypos. apply sa_top... *)
  - apply typing_unfold...
    + apply typing_sub with (S:=A')...
    + get_well_form. apply Algo.exposure_sound...
  - apply typing_proj with (T:=T')...
    apply typing_sub with (S:=T)...
    apply Algo.typing_regular in H. destruct_hypos. apply Algo.exposure_sound...
Qed.
