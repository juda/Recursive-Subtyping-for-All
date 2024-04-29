Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Antisymmetry.


Lemma label_transform3: forall (X X0:atom) T D,
    X \notin fl_tt T \u {{X0}} ->
    type D ->
    open_tt (subst_label X (subst_tt X (typ_label X D) T))
             (typ_label X0 (open_tt (subst_label X (subst_tt X (typ_label X D) T)) X0))
      = subst_label X (subst_tt X (typ_label X D) (open_tt T (typ_label X0 (open_tt T X0)))).
Proof with auto.
  intros.
  rewrite  subst_tt_open_tt ...
  rewrite subst_label_open_tt ...
  f_equal...
  rewrite drop_label_reverse_type...  
  rewrite drop_label_reverse_type...
  solve_notin.
Qed.

Lemma label_transform4 : forall (X X0:atom) T D,
    X \notin fl_tt T \u {{X0}} ->
    type D ->
    (open_tt (subst_label X (subst_tt X (typ_label X D) T)) X0) = (subst_label X (subst_tt X (typ_label X D) (open_tt T X0))).
Proof with auto.
  intros.
  rewrite <- subst_label_open_tt_var...
  f_equal...
  rewrite subst_tt_open_tt_var...
Qed.  


Lemma binds_subst_label_existial : forall E X Y T U,
    binds X (bind_sub U) (map (drop_label Y) (map (subst_tb Y (typ_label Y T)) E)) ->
    exists Q,
      binds X (bind_sub Q) E.
Proof with auto.
  induction E;intros;simpl in *...
  analyze_binds H...
  destruct a.
  analyze_binds H...
  2: {
    destruct IHE with (X:=X) (Y:=Y) (U:=U) (T:=T)...
    exists x...
  }  
  destruct b;simpl in *.
  dependent destruction BindsTacVal.
  exists t...
  inversion BindsTacVal.
Qed.

Lemma WF_narrowing_env_subst_inv: forall E1 E2 (X:atom) Y S,
    WF (map (subst_tb Y S) E1 ++ Y ~ bind_sub typ_top ++ E2) X ->
    WF (E1 ++ Y ~ bind_sub typ_top ++ E2) X.
Proof with auto.
  induction E1;intros...
  simpl in *.
  destruct a.
  dependent destruction H...
  analyze_binds H...
  -
    destruct b.
    apply WF_var with (U:=t)...
    simpl in *.
    inversion BindsTacVal...
  -
    rewrite_env (nil ++ (a~ b) ++ E1 ++ (Y, bind_sub typ_top) :: E2).
    apply WF_weakening...
    apply IHE1  with (S:=S)...
    apply WF_var with (U:=U)...
  -
    apply WF_var with (U:=typ_top)...
  -
    apply WF_var with (U:=U)...
Qed.   

Lemma binds_subst_extensial: forall E S T X0 X U,
    binds X0 (bind_sub U) (map (subst_tb X S) E) ->
    exists A,
      binds X0 (bind_sub A) (map (subst_tb X T) E).
Proof with auto.
  induction E;intros...
  simpl in *.
  analyze_binds H.
  simpl in *.
  destruct a.
  analyze_binds H.
  -
    destruct b;simpl in *; inversion BindsTacVal.
    exists (subst_tt X T t)...
  -
    apply IHE with (T:=T) in BindsTac...
    destruct_hypos.
    exists x...
Qed.


Lemma sub_map_inv_var: forall X Y X0 C E1 E2, 
    X <> Y -> X0 <> Y ->
  sub (map (subst_tb Y C) E1 ++ (Y, bind_sub typ_top) :: E2) X X0 ->
  sub (map (subst_tb Y C) E1 ++ (Y, bind_sub typ_top) :: E2) X0 X ->
  wf_env (E1 ++ (Y, bind_sub typ_top) :: E2) ->
  sub (E1 ++ (Y, bind_sub typ_top) :: E2) X X0.
Proof with auto.
  intros.
  pose proof suba_sub_tvar_chain H1.
  pose proof suba_sub_tvar_chain H2.
  destruct H4 as [W1 ?].
  destruct H5 as [W2 ?].
  pose proof sub_tvar_chain_antisym H4 H5.
  subst.
  apply sa_fvar...
  get_well_form.
  apply WF_narrowing_env_subst_inv in H6...
Qed.


Lemma subst_label_collect3': forall T i X,
    rt_type T -> type T ->
    i `in` collectLabel T ->
    i `in` collectLabel (subst_label X T).
Proof with auto.
  intros.
  induction H0;try solve [inversion H]...
  simpl in *.
  apply union_iff in H1. apply union_iff.
  destruct H1...
Qed.  


Lemma subst_tt_collect2': forall T i X A,
    i `in` collectLabel T ->
    rt_type T ->
    type T ->
    i `in` collectLabel (subst_tt X A T).
Proof with auto.
  intros.
  induction H1;try solve [inversion H0]...
  simpl in *.
  apply union_iff in H. apply union_iff.
  destruct H...
Qed.  


Lemma drop_label_reverse_wf: forall E1 E2 C D A X,
    WF (map (drop_label X) (map (subst_tb X (typ_label X C)) E1) ++
            (X, bind_sub typ_top) :: E2)
       (subst_label X (subst_tt X (typ_label X D) A)) ->
    X \notin fl_tt A -> type D ->
    WF (E1 ++ (X, bind_sub typ_top) :: E2) A.
Proof with auto.
  intros.
  assert (type A) as HA.
  get_type...
  rewrite drop_label_reverse_type in H... 
  apply type_to_rec in HA.
  generalize dependent E1.
  generalize dependent E2.
  generalize dependent C.
  generalize dependent D.
  generalize dependent X.
  induction HA;intros;simpl in *;try solve [dependent destruction H;auto]...
  -
    destruct (X==X0);subst...
    +
      apply WF_var with (U:=typ_top)...
    +
      simpl in H...
      dependent destruction H...
      analyze_binds H...
      apply binds_subst_label_existial in BindsTac.
      destruct_hypos.
      apply WF_var with (U:=x)...
      apply WF_var with (U:=U)...
  -
    dependent destruction H.
    constructor...
    apply IHHA1 with (C:=C) (D:=D)...
    apply IHHA2 with (C:=C) (D:=D)...
  -
    dependent destruction H5.
    apply WF_rec with (L:=L \u L0 \u {{X}});intros...
    +
      rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ (X, bind_sub typ_top) :: E2).
      apply H2 with (C:=C) (D:=D)...
      solve_notin.
      rewrite <- subst_tt_open_tt_var...
      rewrite  subst_label_open_tt_var...
      apply H5...
    +
      rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ (X, bind_sub typ_top) :: E2).
      apply H0 with (C:=C) (D:=D)...
      solve_notin.
      rewrite <- label_transform3...
      apply H6...
  -
    dependent destruction H3.
    apply WF_all with (L:=L \u L0 \u {{X}});intros...
    +
      apply IHHA with (C:=C) (D:=D)...
    +
      rewrite_env ((X0 ~ bind_sub T1 ++ E1) ++ (X, bind_sub typ_top) :: E2).
      apply H0 with (C:=C) (D:=D)...
      solve_notin.
      rewrite <- label_transform4...
      simpl.
      rewrite drop_label_reverse_type...
      assert (T1 = subst_label X (subst_tt X (typ_label X D) T1)).
      rewrite drop_label_reverse_type ...
      rewrite H6.
      apply H4...
  -
    destruct (l==X);subst...
    +
      apply notin_union  in H0.
      destruct_hypos.
      apply test_solve_notin_7 in H0.
      destruct H0.
    +
      dependent destruction H.
      constructor...
      apply IHHA with (C:=C) (D:=D)...
  -
    dependent destruction H2... 
    apply WF_rcd_cons...
    + apply IHHA1 with (D:=D) (C:=C)...
    + apply IHHA2 with (D:=D) (C:=C)...
    + intros Hc.
      apply H3.
      apply subst_label_collect3' with (X:=X)...
      { apply Infrastructure.subst_tt_rt_type... }
      { apply subst_tt_type... apply type4rec_to_type... }
      apply subst_tt_collect2'...
      apply type4rec_to_type...
Qed.

    
Lemma WF_nominal_inversion: forall E1 E2 X A (X0:atom) D C,
    WF (X0 ~ bind_sub typ_top ++
           map (subst_tb X (typ_label X (open_tt C X))) E1 ++ (X, bind_sub typ_top) :: E2)
          (open_tt (subst_tt X (typ_label X (open_tt D X)) A) X0)->
    X \notin {{X0}} \u fl_tt A  ->
    wf_env (X0 ~ bind_sub typ_top ++
           map (subst_tb X (typ_label X (open_tt C X))) E1 ++ (X, bind_sub typ_top) :: E2) ->
    type (open_tt D X) ->
    WF (X0 ~ bind_sub typ_top ++ E1 ++ (X, bind_sub typ_top) :: E2) (open_tt A X0) .
Proof with auto.
  intros.
  rewrite subst_tt_open_tt_var in H...
  rewrite_env ((X0 ~ bind_sub typ_top ++
           map (subst_tb X (typ_label X (open_tt C X))) E1) ++ (X, bind_sub typ_top) :: E2) in H.
  apply WF_drop_label in H...
  simpl in H...
  rewrite_env ((X0 ~ bind_sub typ_top ++ E1) ++ (X, bind_sub typ_top) :: E2).
  apply drop_label_reverse_wf with (C:=open_tt C X) (D:=open_tt D X)...
  solve_notin.
Qed.

Ltac inv_rt :=
  try solve [
    repeat match goal with
    | [ H : rt_type ?T |- _ ] => inversion H;clear H
    end
      ].

Lemma Tlookup_first_element: forall i T1 T2,
    Tlookup i (typ_rcd_cons i T1 T2) = Some T1.
Proof with auto.
  intros.
  simpl.
  destruct (i==i);subst...
  destruct n...
Qed.

Lemma dropLable_notin: forall T2 i E,
    WF E T2 ->
    rt_type T2 ->
    i `notin` collectLabel T2 ->
    dropLabel i T2 = T2.
Proof with eauto.
  intros.
  induction H;try solve [inversion H0]...
  simpl in *.
  destruct (i0==i);subst...
  apply notin_union in H1.
  destruct_hypos.
  apply test_solve_notin_7 in H1...
  destruct H1.
  f_equal...
Qed.

Lemma dropLabel_first_element: forall E i T1 T2,
    WF E (typ_rcd_cons i T1 T2) ->
    dropLabel i (typ_rcd_cons i T1 T2) = T2.
Proof with auto.
  intros.
  dependent destruction H...
  simpl...
  destruct (i==i)...
  apply dropLable_notin with (E:=E)...
  destruct n...
Qed.

Lemma dom_add_subset: forall a E T,
    a \notin E \u T ->
    add a E [<=] add a T ->
    E [<=] T.
Proof with auto.
  intros.
  unfold "[<=]" in *.
  intros.
  specialize (H0 a0).
  assert (a0 \in add a E).
  apply AtomSetImpl.add_2...
  apply H0 in H2.
  apply KeySetProperties.FM.add_iff in H2...
  destruct H2...
  subst...
  assert (False).
  apply H...
  destruct H2.
Qed.

Lemma dom_notin_in: forall (X Y:atom) E,
    X \notin E ->
    Y \in E ->
          X <> Y.
Proof with auto.
  intros...
  unfold "\notin" in *...
  intros.
  apply H...
  subst...
Qed.

Lemma union_swap_assoc: forall A B C,
    A \u B \u C [=] B \u A \u C.
Proof with auto.
  intros.
  rewrite <- AtomSetProperties.union_assoc...
  rewrite <- AtomSetProperties.union_assoc...
  assert (union A B [=] union B A).
  apply AtomSetProperties.union_sym...
  rewrite H...
  apply AtomSetProperties.equal_refl...
Qed.


Lemma drop_collect_flip: forall E A i,
    WF E A ->
    rt_type A ->
    i \in collectLabel A ->
    {{i}} \u collectLabel (dropLabel i A) [=] collectLabel A.
Proof with auto.
  intros.
  induction H;try solve [inversion H0]...
  -
    simpl in *.
    apply empty_iff in H1.
    destruct H1.
  -
    simpl in *...
    destruct (i0==i);subst.
    +
      apply KeySetProperties.union_equal_2...
      rewrite <- notin_drop_collect_self...
      apply AtomSetProperties.equal_refl...
    +
      simpl in *.
      rewrite union_swap_assoc...
      apply KeySetProperties.union_equal_2...
      apply IHWF2...
      apply AtomSetImpl.union_1 in H1.
      destruct H1...
      apply AtomSetImpl.singleton_1 in H1...
      destruct n...
Qed.
    
Lemma record_permutation: forall S2 T2 E i j T1 S1,
    equiv E (typ_rcd_cons i T1 T2) (typ_rcd_cons j S1 S2) ->
    j \in collectLabel (typ_rcd_cons i T1 T2) /\
          (exists T0, Tlookup j (typ_rcd_cons i T1 T2) = Some T0 /\ equiv E T0 S1) /\
          equiv E (dropLabel j (typ_rcd_cons i T1 T2)) S2.
Proof with auto.
  unfold equiv.
  intros.
  destruct_hypos.
  dependent destruction H.
  dependent destruction H6.
  destruct (j==i);subst...
  -
    repeat split...
    +
      apply label_belong with (B:=T1)...
      apply Tlookup_first_element...
    +
      exists T1.
      repeat split...
      apply Tlookup_first_element...
      apply H5 with (i0:=i)...
      apply Tlookup_first_element...
      apply Tlookup_first_element...
      apply H12 with (i0:=i)...
      apply Tlookup_first_element...
      apply Tlookup_first_element...
    +
      rewrite dropLabel_first_element with (E:=E)...
      dependent destruction H3.
      dependent destruction H6.
      dependent destruction H3;dependent destruction H6.
      *
        apply Reflexivity...
      *
        simpl in H2...
        simpl in H7.
        rewrite <- KeySetProperties.add_union_singleton in H2.
        rewrite <- KeySetProperties.add_union_singleton in H2.
        rewrite <- KeySetProperties.add_union_singleton in H2.
        apply dom_add_subset in H2...
        rewrite KeySetProperties.add_union_singleton in H2.
        apply union_empty in H2...
        destruct H2.
      *
        simpl in H12...
        simpl in H4.
        rewrite <- KeySetProperties.add_union_singleton in H12.
        rewrite <- KeySetProperties.add_union_singleton in H12.
        rewrite <- KeySetProperties.add_union_singleton in H12.
        apply dom_add_subset in H12...
        rewrite KeySetProperties.add_union_singleton in H12.
        apply union_empty in H12...
        destruct H12.
      *
        constructor...
        --
          simpl in *...
          rewrite <- KeySetProperties.add_union_singleton in H2.
          rewrite <- KeySetProperties.add_union_singleton in H2.
          rewrite <- KeySetProperties.add_union_singleton in H2.
          rewrite <- KeySetProperties.add_union_singleton in H2.
          apply dom_add_subset in H2...
          rewrite <- KeySetProperties.add_union_singleton.
          rewrite <- KeySetProperties.add_union_singleton...
        --
          intros.
          apply H5 with (i2:=i2)...
          ++
            assert (Hq1:=H3).
            assert (Hq2:=H6).
            apply label_belong in Hq1.
            apply label_belong in Hq2.
            apply dom_notin_in with (X:=i) in Hq1...
            apply dom_notin_in with (X:=i) in Hq2...
            simpl...
            destruct (i==i2);subst...
            destruct Hq1...
          ++
            assert (Hq1:=H3).
            assert (Hq2:=H6).
            apply label_belong in Hq1.
            apply label_belong in Hq2.
            apply dom_notin_in with (X:=i) in Hq1...
            apply dom_notin_in with (X:=i) in Hq2...
            simpl...
            destruct (i==i2);subst...
            destruct Hq1...
    +
      rewrite dropLabel_first_element with (E:=E)...
      dependent destruction H3.
      dependent destruction H6.
      dependent destruction H3;dependent destruction H6.
      *
        apply Reflexivity...
      *
        simpl in H2...
        simpl in H7.
        rewrite <- KeySetProperties.add_union_singleton in H2.
        rewrite <- KeySetProperties.add_union_singleton in H2.
        rewrite <- KeySetProperties.add_union_singleton in H2.
        apply dom_add_subset in H2...
        rewrite KeySetProperties.add_union_singleton in H2.
        apply union_empty in H2...
        destruct H2.
      *
        simpl in H12...
        simpl in H4.
        rewrite <- KeySetProperties.add_union_singleton in H12.
        rewrite <- KeySetProperties.add_union_singleton in H12.
        rewrite <- KeySetProperties.add_union_singleton in H12.
        apply dom_add_subset in H12...
        rewrite KeySetProperties.add_union_singleton in H12.
        apply union_empty in H12...
        destruct H12.
      *
        constructor...
        --
          simpl in *...
          rewrite <- KeySetProperties.add_union_singleton in H12.
          rewrite <- KeySetProperties.add_union_singleton in H12.
          rewrite <- KeySetProperties.add_union_singleton in H12.
          rewrite <- KeySetProperties.add_union_singleton in H12.
          apply dom_add_subset in H12...
          rewrite <- KeySetProperties.add_union_singleton.
          rewrite <- KeySetProperties.add_union_singleton...
        --
          intros.
          apply H14 with (i2:=i2)...
          ++
            assert (Hq1:=H3).
            assert (Hq2:=H6).
            apply label_belong in Hq1.
            apply label_belong in Hq2.
            apply dom_notin_in with (X:=i) in Hq1...
            apply dom_notin_in with (X:=i) in Hq2...
            simpl...
            destruct (i==i2);subst...
            destruct Hq1...
          ++
            assert (Hq1:=H3).
            assert (Hq2:=H6).
            apply label_belong in Hq1.
            apply label_belong in Hq2.
            apply dom_notin_in with (X:=i) in Hq1...
            apply dom_notin_in with (X:=i) in Hq2...
            simpl...
            destruct (i==i2);subst...
            destruct Hq1...
  -
    simpl in H2...
    assert (j \in collectLabel T2) as Hj.
    {
      assert (j `in` collectLabel (typ_rcd_cons i T1 T2)) as HH.
      auto.
      simpl in HH.
      apply AtomSetImpl.union_1 in HH...
      destruct HH...
      apply AtomSetImpl.singleton_1 in H13.
      destruct n...
    }    
    repeat split...
    +
      apply lookup_some in Hj...
      destruct Hj.
      exists x...
      repeat split...
      *
        simpl...
        destruct (i==j);subst...
        destruct n...
      *
        apply H5 with (i0:=j)...
        simpl...
        destruct (i==j);subst...
        destruct n...
        simpl...
        destruct (j==j);subst...
        destruct n0...
      *
        apply H12 with (i0:=j)...
        simpl...
        destruct (j==j);subst...
        destruct n0...
        simpl...
        destruct (i==j);subst...
        destruct n...        
    +
      dependent destruction H3.
      dependent destruction H5.
      constructor...
      *
        apply rt_type_drop with (E:=E)...
      *
        simpl in *.
        destruct (i==j);subst...
        destruct n...
        clear H7 H14.
        simpl.
        apply dom_add_subset with (a:=j)...
        solve_notin.
        apply notin_drop_self...
        rewrite  KeySetProperties.add_union_singleton.
        rewrite  KeySetProperties.add_union_singleton...
        rewrite union_swap_assoc...
        rewrite drop_collect_flip with (E:=E)...
      *
        apply WF_drop...
      *
        intros.
        apply H7 with (i0:=i0)...
        --
          apply Tlookup_drop in H15...
        --
          assert (Ht:=H16).
          apply label_belong in Ht.
          apply dom_notin_in with (Y:=i0) in H6...
          simpl...
          destruct (j==i0);subst...
          destruct H6...
    +
      dependent destruction H3.
      dependent destruction H5.
      constructor...
      *
        apply rt_type_drop with (E:=E)...
      *
        simpl in *.
        destruct (i==j);subst...
        destruct n...
        clear H7 H14.
        simpl.
        apply dom_add_subset with (a:=j)...
        solve_notin.
        apply notin_drop_self...
        rewrite  KeySetProperties.add_union_singleton.
        rewrite  KeySetProperties.add_union_singleton...
        rewrite union_swap_assoc...
        rewrite drop_collect_flip with (E:=E)...
      *
        apply WF_drop...
      *
        intros.
        apply H14 with (i0:=i0)...
        --
          assert (Ht:=H15).
          apply label_belong in Ht.
          apply dom_notin_in with (Y:=i0) in H6...
          simpl...
          destruct (j==i0);subst...
          destruct H6...       
        --
          apply Tlookup_drop in H16...
Qed.
