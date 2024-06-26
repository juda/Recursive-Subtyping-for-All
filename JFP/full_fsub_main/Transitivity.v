Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Variance.

Inductive type4rec : typ -> Prop :=
  | type4_top :
      type4rec typ_top
  | type4_nat :
      type4rec typ_nat
  | type4_var : forall X,
      type4rec (typ_fvar X)
  | type4_arrow : forall T1 T2,
      type4rec T1 -> 
      type4rec T2 -> 
      type4rec (typ_arrow T1 T2)
  | type4_mu : forall L T,
      (forall X, X \notin L -> type4rec (open_tt T (typ_label X (open_tt T (typ_fvar X))))) ->
      (forall X, X \notin L -> type4rec (open_tt T (typ_fvar X))) ->
      type4rec (typ_mu T)
  | type4_all : forall L T1 T2,
      type4rec T1 ->
      (forall X, X `notin` L -> type4rec (open_tt T2 (typ_fvar X))) ->
      type4rec (typ_all T1 T2)
  | type4_label: forall l A,
      type4rec A ->
      type4rec (typ_label l A)
  | type4_rcd_nil :
      type4rec typ_rcd_nil
  | type4_rcd_cons : forall i T1 T2,
      type4rec T1 ->
      type4rec T2 ->
      rt_type T2 ->
      type4rec (typ_rcd_cons i T1 T2)
.

Hint Constructors type4rec : core.

Lemma type4rec_to_type : forall A,
    type4rec A -> type A.
Proof with auto.
  intros.
  induction H...
  apply type_mu with (L:=L)...
  apply type_all with (L:=L)...
Qed.


Lemma subst_tt_type4rec : forall Z P T,
  type4rec T ->
  type4rec P ->
  type4rec (subst_tt Z P T).
Proof with auto using type4rec_to_type.
  intros Z P T HT HP.
  induction HT; simpl...
  -
    destruct (X == Z)...
  -
    apply type4_mu with (L:=L \u {{Z}});intros...
    rewrite <- subst_tt_open_tt_twice...
    rewrite subst_tt_open_tt_var...
  -
    apply type4_all with (L:=L \u {{Z}});intros...
    rewrite subst_tt_open_tt_var...
  -
    apply type4_rcd_cons...
    apply Infrastructure.subst_tt_rt_type...
Qed.

Lemma type_to_rec : forall A,
    type A -> type4rec A.
Proof with auto.
  intros.
  induction H...
  -
    apply type4_mu with (L:=L \u fv_tt T)...
    intros.
    rewrite subst_tt_intro with (X:=X)...
    apply subst_tt_type4rec...
  -
    apply type4_all with (L:=L \u fv_tt T1 \u fv_tt T2)...
Qed.


Definition transitivity_on Q := forall E S T,
    sub E S Q -> sub E Q T -> sub E S T.

Lemma wf_env_narrowing: forall F Z Q E P,
    wf_env (F ++ Z ~ bind_sub Q ++ E) ->
    WF E P ->
    wf_env  (F ++ Z ~ bind_sub P ++ E).
Proof with auto.
  induction F;intros...
  -
    simpl...
    dependent destruction H...
    constructor...
  -
    dependent destruction H...
    +
      rewrite_env ((X, bind_sub T) :: F ++ Z ~ bind_sub P ++ E).
      constructor...
      apply IHF with (Q:=Q)...
      apply WF_narrowing with (V:=Q)...
    +
      rewrite_env ((x, bind_typ T) :: F ++ Z ~ bind_sub P ++ E).
      constructor...
      apply IHF with (Q:=Q)...
      apply WF_narrowing with (V:=Q)...
Qed.


Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  sub (F ++ Z ~ bind_sub P ++ E) S T.
Proof with auto.
  intros.
  generalize dependent P.
  dependent induction H0;intros...
  -
    constructor...
    apply wf_env_narrowing with (Q:=Q)...
    get_well_form...
  -
    constructor...
    apply wf_env_narrowing with (Q:=Q)...
    get_well_form...
    apply WF_narrowing with (V:=Q)...
  -
    constructor...
    apply wf_env_narrowing with (Q:=Q)...
    get_well_form...
    apply WF_narrowing with (V:=Q)...
  -
    destruct (X==Z);subst...
    +
      apply sa_trans_tvar with (U:=P)...
      apply H...
      * Case "P < Q".
        rewrite_env (nil ++ (F ++ Z ~ bind_sub P) ++ E).
        apply Sub_weakening...
        get_well_form...
        rewrite_env (F ++ Z ~ bind_sub P ++ E).
        apply wf_env_narrowing with (Q:=Q)...
      * Case "Q < T".
        analyze_binds_uniq H1...
        apply uniq_from_wf_env...
        get_well_form...
        dependent destruction BindsTacVal.
        apply IHsub with (Q0:=Q)...
    +
      apply sa_trans_tvar with (U:=U)...
      analyze_binds_uniq H1...
      apply uniq_from_wf_env...
      get_well_form...
      apply IHsub with (Q0:=Q)...
  -
    constructor...
    apply IHsub1 with (Q0:=Q)...
    apply IHsub2 with (Q0:=Q)...
  -
    apply sa_all with (L:=L);intros...
    +
      apply IHsub with (Q0:=Q)...
    +
      rewrite_env ((X ~ bind_sub S2 ++ F) ++ Z ~ bind_sub P ++ E).
      apply H1 with (Q0:=Q)...
  -
    apply sa_rec with (L:=L \u fv_tt A1 \u fv_tt A2);intros...
    +
      rewrite_env ((X ~ bind_sub typ_top ++ F) ++ Z ~ bind_sub P ++ E).
      apply WF_narrowing with (V:=Q)...
      apply H3...
    +
      rewrite_env ((X ~ bind_sub typ_top ++ F) ++ Z ~ bind_sub P ++ E).
      apply WF_narrowing with (V:=Q)...
      apply H0...
    +
      rewrite_env ((X ~ bind_sub typ_top ++ F) ++ Z ~ bind_sub P ++ E).
      apply H2 with (Q0:=Q)...
  -
    constructor.
    apply IHsub with (Q0:=Q)...
  - 
    apply sa_rcd...
    + apply wf_env_narrowing with (Q:=Q)... get_well_form...
    + apply WF_narrowing with (V:=Q)...
    + apply WF_narrowing with (V:=Q)...
    + intros. apply H6 with (i:=i) (Q0:=Q)...
Qed.


Lemma sub_top: forall E T S,  
  sub E typ_top T ->
  WF E S ->
  sub E S T.
Proof with auto.
  intros.
  dependent destruction H.
  - constructor...
  - inversion H0.
Qed.


Lemma WF_drop: forall A i E,
   
    WF E A -> WF E (dropLabel i A).
Proof with auto.
  intros.
  induction H;simpl;try solve [inversion H]...
  + apply WF_var with (U:=U)...
  + apply WF_all with (L:=L)...
    intros. unfold open_tt.
    rewrite open_tt_drop_var...
    add_nil.
    apply WF_narrowing with (V:=T1).
    apply H1...
  + apply WF_rec with (L:=L \u fv_tt A \u {{i}});intros.
    * unfold open_tt.
      rewrite open_tt_drop_var...
      apply H0...
    * rewrite subst_tt_intro with (X:=X)...
      ++ assert (WF (X ~ bind_sub typ_top ++ E) (open_tt (dropLabel i A) X)).
        { unfold open_tt.
          rewrite open_tt_drop_var...
          apply H0... }
        apply subst_tt_wf...
      ++ apply notin_drop_fv...
  + destruct (i0==i)...
    constructor...
    * apply rt_type_drop with (E:=E)...
    * apply notin_drop_collect...
Qed.  


Lemma Tlookup_drop:forall i j T A,
    Tlookup j (dropLabel i A) = Some T ->
    Tlookup j A = Some T.
Proof with auto.
  intros.
  induction A;simpl in *;try solve [inversion H]...
  destruct (a==i)...
  destruct (a==j)...
  subst.
  apply label_belong in H.
  assert (j `notin` collectLabel (dropLabel j A2)).
  apply notin_drop_self...
  assert (False).
  apply H0...
  destruct H1.
  simpl in H.
  destruct (a==j)...
Qed.

Lemma Tlookup_drop_flip: forall i A j t,
    Tlookup i A = Some t ->
    i <> j ->
    Tlookup i (dropLabel j A) = Some t.
Proof with auto.
  intros.
  induction A;simpl in *;try solve [inversion H]...
  destruct (a==i)...
  destruct (a==j)...
  subst.
  destruct H0...
  simpl.
  destruct (a==i)...
  destruct n0...
  destruct (a==j)...
  simpl...
  destruct (a==i)...
  destruct n...
Qed.  


Lemma in_dec: forall T X,
    X \notin T \/ X \in T.
Proof with auto.
  intros.
  apply notin_diff_1.
  assert (AtomSetImpl.diff T T [=] Metatheory.empty).
  apply AtomSetProperties.diff_subset_equal.
  apply KeySetProperties.subset_refl.
  rewrite H...
Qed.


Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof with auto.
  intros.
  unfold transitivity_on.
  intros.
  assert (type Q).
  get_type...
  apply type_to_rec in H1.
  generalize dependent S.
  generalize dependent T.
  generalize dependent E.
  induction H1;intros...
  -
    apply sub_top... get_well_form...
  -
    dependent induction H...
    apply sa_trans_tvar with (U:=U)...
    inversion H2.
  -
    dependent induction H0...
    + constructor...
      get_well_form...
    +
      (* S <: X /\  X <: U <: T *)
      generalize dependent T.
      generalize dependent U.
      dependent induction H1;intros...
      *
        apply sa_trans_tvar with (U:=U)...
      *
        apply sa_trans_tvar with (U:=U)...
        apply IHsub with (X0:=X) (U0 := U0)...
      *
        inversion H1.
    +
      inversion H0.
  -
    dependent induction H0...
    + constructor...
      get_well_form...
    +
      dependent induction H...
      *
        apply sa_trans_tvar with (U:=U)...
        apply IHsub with (T4:=T1) (T3:=T2)...
      *
        inversion H1.
    +
      inversion H0.
  -
    dependent induction H3...
    + constructor...
      get_well_form...
    +
      clear H6.
      dependent induction H7...
      *
        apply sa_trans_tvar with (U:=U)...
        apply IHsub with (T0:=T)...
      *
        clear H9.
        apply sa_rec with (L:=L \u L0 \u L1);intros...
        apply H0 with (X:=X)...
      *
        inversion H12.
    +
      inversion H8.
  -
    dependent induction H2...
    + 
      constructor...
      get_well_form...
    +
      clear H3 IHsub.
      dependent induction H5...
      *
        apply sa_trans_tvar with (U:=U)...
        apply IHsub with (T4:=T1) (T3:=T2)...
      *
        clear IHsub.
        apply sa_all with (L:=L \u L0 \u L1)...
        intros.
        apply H0 with (X:=X)...
        rewrite_env (nil ++ X ~ bind_sub S2 ++ E).
        apply sub_narrowing_aux with (Q:=T1)...
        unfold transitivity_on...
        apply H6...
      *
        inversion H11.
    +
      inversion H8.
  -
    dependent induction H0...
    +
      constructor...
      get_well_form...
    +
      clear IHsub.
      dependent induction H...
      * apply sa_trans_tvar with (U:=U)...
        apply IHsub with (l0:=l) (A0:=A)...
      * inversion H8.
    + inversion H0.
  -
    dependent induction H0...
    + constructor...
      get_well_form...
    + dependent induction H7...
      * apply sa_trans_tvar with (U:=U)...
      * inversion H1;subst... collect_nil H2.
  -
    dependent destruction H0...
    + constructor...
      get_well_form...
    + dependent induction H7...
      * apply sa_trans_tvar with (U:=U)...
        apply IHsub with (T4:=T1) (T3:=T2) (i0:=i)...
      *
        apply sa_rcd...
        apply F.Subset_trans with (s':=collectLabel (typ_rcd_cons i T1 T2))...    
        intros.
        destruct (i0==i).
        ++
          subst.
          assert (Tlookup i (typ_rcd_cons i T1 T2) = Some T1).
          {
            simpl.
            destruct (i==i)...
            destruct n...
          }
          apply (IHtype4rec1)...
          apply H6 with (i0:=i)...
          apply H7 with (i0:=i)...
        ++
          assert (sub E (dropLabel i A1) T2).
          {
            apply sa_rcd...
            + apply rt_type_drop with (E:=E)...
            + simpl in H6.
              assert (union (singleton i) (collectLabel T2) [<=] {{i}} \u collectLabel (dropLabel i A1)).
              {
                apply KeySetProperties.subset_trans with (s2:=collectLabel A1)...
                apply drop_collect...
              }
              apply union_subset_x2 in H17...
              { inversion H4... }
            + apply WF_drop...
            + inversion H4...
            + intros.
              inversion H4;subst.
              inversion H13;subst.
              apply H7 with (i0:=i1)...
              { apply Tlookup_drop in H17... }
              {
                simpl.
                destruct (i==i1)...
                apply label_belong in H17.
                subst.
                assert (i1 `notin` collectLabel (dropLabel i1 A1)) by apply notin_drop_self.
                exfalso...
              }
          }
          assert (sub E T2 (dropLabel i A2)).
          {
            apply sa_rcd...
            + apply rt_type_drop with (E:=E)...
            + simpl in H3.
              assert (i \notin  collectLabel A2 \/ i \in collectLabel A2).
              { apply in_dec... }
              destruct H18.
              { rewrite <- notin_drop_collect_self...
                unfold "[<=]" in *.
                intros.
                specialize (H3 _ H19).
                apply union_iff in H3.
                destruct H3...
                apply AtomSetImpl.singleton_1 in H3.
                subst.
                exfalso... }
              { assert ( {{i}} \u collectLabel (dropLabel i A2) [<=] {{i}} \u (collectLabel T2) ).
                { apply KeySetProperties.subset_trans with (s2:=collectLabel A2)...
                  apply drop_collect_flip...
                }
                apply union_subset_x2 in H19...
                apply notin_drop_self.
              }
          + inversion H4...
          + apply WF_drop...
          + intros.
            apply H6 with (i0:=i1)...
            simpl.
            destruct (i==i1)...
            apply label_belong in H19.
            subst.
            assert (i1 `notin` collectLabel (dropLabel i1 A2)) by apply notin_drop_self.
            exfalso.
            apply H20...
            apply Tlookup_drop in H19...
          }
          assert (sub E (dropLabel i A1) (dropLabel i A2)).
          {
            apply IHtype4rec2...
          }
          apply rcd_inversion with (i:=i0) (t1:=t1) (t2:=t2) in H19...
          apply rt_type_drop with (E:=E)...
          apply rt_type_drop with (E:=E)...
          apply Tlookup_drop_flip...
          apply Tlookup_drop_flip...
Qed.


Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub (F ++ Z ~ bind_sub P ++ E) S T.
Proof with auto.
  intros.
  apply sub_narrowing_aux with (Q:=Q)...
  apply sub_transitivity.
Qed.
