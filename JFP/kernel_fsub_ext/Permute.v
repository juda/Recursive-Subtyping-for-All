Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export DecidabilityWF.
Require Export Coq.micromega.Lia.

Lemma sub_and_r_inv: forall E A B C,
  sub E C (typ_and A B) ->
  sub E C A /\ sub E C B.
Proof with auto.
  intros.
  dependent induction H...
  - inversion H0;subst. split...
  - destruct (IHsub A B)...
    split;apply sa_trans_tvar with (U:=U)...
  - destruct (IHsub A B)...
  - destruct (IHsub A B)...
Qed.

Inductive permute: typ -> typ -> Prop :=
  (* | permute_base_top:
      permute typ_top typ_top *)
  | permute_base_single:
      forall i T,
      permute (typ_single i T) (typ_single i T)
  | permute_comm:
      forall T1 T2 T1' T2',
      permute T1 T1' ->
      permute T2 T2' ->
      permute (typ_and T1 T2) (typ_and T2' T1')
  | permute_trans:
      forall T1 T2 T3,
      permute T1 T2 ->
      permute T2 T3 ->
      permute T1 T3
  | permute_and_cong:
      forall T1 T2 T1' T2',
      permute T1 T1' ->
      permute T2 T2' ->
      permute (typ_and T1 T2) (typ_and T1' T2')
  (* | permute_add_top:
      forall T T',
      permute T T' ->
      permute T (typ_and typ_top T') *)
  | permute_symm:
      forall T1 T2,
      permute T1 T2 ->
      permute T2 T1
  | permute_assoc:
      forall T1 T1' T2 T2' T3 T3',
      permute T1 T1' ->
      permute T2 T2' ->
      permute T3 T3' ->
      permute (typ_and T1 (typ_and T2 T3)) (typ_and (typ_and T1' T2') T3').

#[global]
Hint Constructors permute : core.


Inductive collect_typ: typ -> list (atom * typ) -> Prop :=
(* | cty_top : collect_typ typ_top nil *)
| cty_single : forall l A, 
    collect_typ (typ_single l A) (l ~ A)
| cty_and : forall A B ts1 ts2,
    collect_typ A ts1 ->
    collect_typ B ts2 ->
    collect_typ (typ_and A B) (ts1 ++ ts2).

#[global]
Hint Constructors collect_typ : core.

Lemma permute_refl: forall T ts,
  collect_typ T ts ->
  permute T T.
Proof with auto.
  intros. generalize dependent ts.
  induction T;intros;try solve [inversion H]...
  - inversion H;subst... eauto.
Qed.


#[export]
Hint Extern 1 (permute ?T ?T) =>
  match goal with
  | H: collect_typ ?T _ |- _ => apply (@permute_refl T) in H
  end : core.




Lemma collect_typ_ex: forall A B,
  Compatible A B ->
  exists ts, collect_typ A ts.
Proof with auto.
  intros.
  induction H;eauto.
  - destruct IHCompatible1 as [ts1' ?],
    IHCompatible2 as [ts2' ?].
    exists (ts1' ++ ts2')...
Qed.


Lemma sub_single_collect_in: forall E A l t ts,
  sub E A (typ_single l t) ->
  collect_typ A ts ->
  l `in` dom ts.
Proof with auto.
  intros.
  induction H0...
  (* - inversion H. *)
  - inversion H;subst. simpl...
  - rewrite dom_app. inversion H;subst...
Qed.


Lemma sub_collect_subset: forall E A B ts1 ts2,
  sub E A B ->
  collect_typ A ts1 ->
  collect_typ B ts2 ->
  dom ts2 [<=] dom ts1.
Proof with auto.
  intros E A B ts1 ts2 Hsub Hct1 Hct2. 
  generalize dependent ts1.
  generalize dependent ts2.
  induction Hsub;intros;try solve [inversion Hct1;inversion Hct2].
  (* - inversion Hct2;subst. simpl. fsetdec. *)
  - inversion Hct1;inversion Hct2;subst. simpl. fsetdec.
  - inversion Hct1;subst.
    rewrite dom_app.
    rewrite (IHHsub _ Hct2 _ H3)... fsetdec.
  - inversion Hct1;subst.
    rewrite dom_app.
    rewrite (IHHsub _ Hct2 _ H5)... fsetdec.
  - inversion Hct2;subst.
    rewrite dom_app.
    rewrite (IHHsub1 _ H2 _ Hct1)...
    rewrite (IHHsub2 _ H4 _ Hct1)... fsetdec.
Qed.

Lemma Compatible_disjoint: forall A B ts1 ts2,
  Compatible A B ->
  collect_typ A ts1 ->
  collect_typ B ts2 ->
  disjoint ts1 ts2.
Proof with auto.
  intros A B ts1 ts2 Hcomp Hct1 Hct2.
  generalize dependent ts1.
  generalize dependent ts2.
  induction Hcomp;intros;
  inversion Hct1;inversion Hct2;subst...
Qed.

Lemma collect_uniq: forall E A ts,
  WF E A ->
  collect_typ A ts ->
  uniq ts.
Proof with auto.
  intros.
  induction H0...
  inversion H;subst.
  apply uniq_app_4...
  eapply Compatible_disjoint;eauto.
Qed.



Lemma collect_typ_sub_sem: forall E A B ts1 ts2,
  sub E A B ->
  collect_typ A ts1 ->
  collect_typ B ts2 ->
  (forall l t t', binds l t ts2 ->
      binds l t' ts1 ->
      sub E t' t).
Proof with auto.
  intros E A B ts1 ts2 Hsub Hct1 Hct2.
  generalize dependent B.
  generalize dependent ts2.
  induction Hct1;intros.
  (* -
    inversion H0. *)
  -
    analyze_binds H0.
    induction Hct2.
    (* + inversion H;subst. *)
    + analyze_binds H. 
      inversion Hsub;subst...
    + 
      inversion Hsub;subst.
      analyze_binds H...
  - 
    generalize dependent ts0. 
    dependent induction Hsub;intros;subst;try solve [inversion Hct2].
    (* + inversion Hct2;subst. inversion H2. *)
    + eapply IHHct1_1 with (B:=C);try eassumption...
      analyze_binds_uniq H1.
      { get_well_form.
        eapply collect_uniq with (A:=typ_and A B) (E:=E)... }
      epose proof sub_collect_subset Hsub Hct1_1 Hct2.
      apply binds_In in H2.
      fsetdec.
    + eapply IHHct1_2 with (B0:=C);eauto.
      analyze_binds_uniq H1.
      { get_well_form.
        eapply collect_uniq with (A:=typ_and A B) (E:=E)... }
      epose proof sub_collect_subset Hsub Hct1_2 Hct2.
      apply binds_In in H2.
      fsetdec.
    +
      inversion Hct2;subst. analyze_binds H1.
      * eapply IHHsub1;try eassumption...
      * eapply IHHsub2;try eassumption...
Qed.



Lemma collect_typ_sem1: forall E A B ts1 ts2,
  equiv E A B ->
  collect_typ A ts1 ->
  collect_typ B ts2 ->
  (forall l t t', binds l t ts1 ->
      binds l t' ts2 ->
      equiv E t t').
Proof with auto.
  intros E A B ts1 ts2 (Hsub1 & Hsub2) Hct1 Hct2.
  pose proof collect_typ_sub_sem Hsub1 Hct1 Hct2 as Hsub.
  pose proof collect_typ_sub_sem Hsub2 Hct2 Hct1 as Hsub'.
  intros. split;eauto.
Qed.


Lemma equiv_collect_dom: forall E A B ts1 ts2,
  sub E A B ->
  sub E B A ->
  collect_typ A ts1 ->
  collect_typ B ts2 ->
  dom ts1 [=] dom ts2.
Proof with auto.
  intros E A B ts1 ts2 Hsub1 Hsub2 Hct1 Hct2.
  pose proof sub_collect_subset Hsub1 Hct1 Hct2 as Hsub1'.
  pose proof sub_collect_subset Hsub2 Hct2 Hct1 as Hsub2'.
  fsetdec.
Qed.

Lemma binds_split_ts: forall ts (l:var) (T:typ), 
  binds l T ts ->
  exists ts1 ts2, ts = ts1 ++ l ~ T ++ ts2.
Proof with auto.
  intros.
  induction ts...
  - inversion H.
  - destruct a. analyze_binds H.
    + exists nil, ts...
    + destruct (IHts BindsTac) as [ts1 [ts2 ?]]...
      exists ((a, t) :: ts1), ts2...
      rewrite H. simpl...
Qed.


Lemma collect_typ_perm_nil: forall A,
  collect_typ A nil ->
  (* permute A typ_top. *)
  False.
Proof with auto.
  intros.
  dependent induction H...
  - apply app_eq_nil in x. destruct_hypos...
    (* apply permute_trans with (T2:=typ_and typ_top typ_top)... *)
Qed.


Lemma collect_typ_perm_single: forall A l t,
  collect_typ A (l ~ t) ->
  permute A (typ_single l t).
Proof with auto.
  intros.
  dependent induction H...
  - destruct ts1...
    + simpl in x. destruct ts2;inversion x;subst.
      apply collect_typ_perm_nil in H. exfalso...
      (* apply permute_trans with (T2:=typ_and typ_top (typ_single l t))... *)
    + simpl in x. destruct p. inversion x;subst.
      apply app_eq_nil in H4. destruct_hypos. subst.
      apply collect_typ_perm_nil in H0. exfalso...
      (* apply permute_trans with (T2:=typ_and  typ_top (typ_single l t))... *)
Qed.

Lemma collect_typ_not_nil: forall A ts,
  collect_typ A ts ->
  ts <> nil.
Proof with auto.
  intros.
  dependent induction H...
  - intros Hc. inversion Hc.
  - intros Hc. apply app_eq_nil in Hc. destruct_hypos...
Qed.

Lemma collect_typ_inv: forall A ts1 ts2 l t,
  uniq (ts1 ++ l ~ t ++ ts2) ->
  collect_typ A (ts1 ++ l ~ t ++ ts2) ->
  (exists A1 A2, permute A (typ_and A1 A2) /\
    collect_typ A1 (l ~ t) /\ 
    collect_typ A2 (ts1 ++ ts2)  ) \/ 
  (ts1 ++ ts2 = nil /\ A = typ_single l t).
Proof with auto.
  intros A ts1 ts2 l t Huniq Hct.
  generalize dependent ts1.
  generalize dependent ts2.
  generalize dependent l.
  generalize dependent t.
  induction A;intros;try solve [inversion Hct].
  (* *
    inversion Hct;subst.
    destruct ts1;inversion H. *)
  *
    inversion Hct;subst.
    destruct ts1;inversion H;subst.
    { right... }
    (* + exists (typ_single l t), typ_top, typ_top.
      repeat split...
      apply permute_trans with (T2:=typ_and typ_top (typ_single l t))... *)
    + destruct ts1;inversion H.

  *
    inversion Hct;subst.
    assert (binds l t (ts0 ++ ts3)).
    { rewrite H1... }
    symmetry in H1.
    pose proof uniq_align_eq _ _ _ _ _ _ _ Huniq H1.
    destruct H0 as [(ts1' & ts2' & ? & ? & ?) |(ts1' & ts2' & ? & ? & ?)].
    -
      subst ts0.
      apply IHA1 in H2.
      2:{ simpl in Huniq. rewrite H1 in Huniq.
        apply uniq_app_1 in Huniq... }
      destruct H2 as [[A1a [A1b [A1c [? ?]]]]| [Hnil ?]].
      2:{  apply app_eq_nil in Hnil. destruct_hypos... subst.
          left. exists (typ_single l t), A2. repeat split... }
      left.
      exists A1a , (typ_and A1b A2).
      subst...
      repeat split...
      + eapply permute_trans.
        { apply permute_and_cong;try eassumption.
          eapply permute_refl;eassumption. }
        apply permute_symm.
        apply permute_assoc...
      + rewrite <- app_assoc. constructor...
    -
      subst ts3.
      apply IHA2 in H3. 2:{ simpl in Huniq. rewrite H1 in Huniq.
        apply uniq_app_2 in Huniq... }
      destruct H3 as [[A1a [A1b [A1c [? ?]]]]| [Hnil ?]].
      2:{ apply app_eq_nil in Hnil. destruct_hypos... subst.
          left. exists (typ_single l t), A1. repeat split...
          rewrite !app_nil_r... }
      left. exists A1a, (typ_and A1 A1b).
      subst...
      repeat split...
      + eapply permute_trans.
        { apply permute_comm;try eassumption.
          eapply permute_refl;eassumption. }
        eapply permute_trans.
        { eapply permute_symm. 
          eapply permute_assoc;eapply permute_refl;eauto. }
        eapply permute_and_cong.
        { eapply permute_refl;eauto. }
        { eapply permute_comm;eapply permute_refl;eauto. }
      + rewrite app_assoc...
Qed.


Lemma collect_typ_perm: forall A1 A2 B ts1a ts1b ts2,
  dom (ts1a ++ ts1b) [=] dom ts2 -> 
  uniq (ts1a ++ ts1b) ->
  uniq ts2 ->
  collect_typ A1 ts1a ->
  collect_typ A2 ts1b ->
  collect_typ B ts2 ->
  exists B1 B2 ts2a ts2b, permute B (typ_and B1 B2) /\
    collect_typ B1 ts2a /\
    collect_typ B2 ts2b /\
    dom ts2a [=] dom ts1a /\ dom ts2b [=] dom ts1b /\ uniq (ts2a ++ ts2b).
Proof with auto.
  intros A1 A2 B ts1a ts1b ts2 Hdom Huniq1 Huniq2 Hct1 Hct2.
  generalize dependent ts2.
  generalize dependent ts1b.
  generalize dependent B.
  generalize dependent A1.
  generalize dependent A2.
  induction ts1a;intros.
  - simpl in Hct1. exfalso. apply collect_typ_not_nil in Hct1...
  - destruct a as [X ?].
    simpl in Hct1.
    assert (X `in` dom ts2).
    { apply (Hdom X). simpl... }
    apply binds_In_inv in H0.
    destruct H0 as [t' Hbinds].
    apply binds_split_ts in Hbinds.
    destruct Hbinds as [ts2a [ts2b ?]].
    subst ts2.




    (* apply collect_typ_inv in Hct2...
    destruct Hct2 as  (B1 & B2 & B3 & ?).
    destruct_hypos. *)
    pose proof Hct1 as Hct1'.
    rewrite_alist (nil ++ (X ~ t) ++ ts1a) in Hct1.
    apply collect_typ_inv in Hct1...
    destruct Hct1 as [(A1' & A2' & ?)|?].
    3:{ inversion Huniq1;subst. rewrite !dom_app in *.
        constructor... apply uniq_app_1 in H2... }
    2:{
      destruct H0. simpl in H0. subst.
      apply collect_typ_inv in H...
      destruct H as [(B1' & B2' & ?)|?].
      + exists (typ_single X t'), B2', (X ~ t'), (ts2a ++ ts2b).
        destruct_hypos. split;[|split;[|split;[|split;[|split]]]]...
        * eapply permute_trans;[apply H|].
          pose proof collect_typ_perm_single H0.
          eapply permute_and_cong;eauto.
        * simpl. fsetdec.
        * pose proof fresh_mid_head _ _ _ _ _ Huniq2.
          pose proof fresh_mid_tail _ _ _ _ _ Huniq2. simpl in Huniq1.
          pose proof uniq_cons_2 _ _ _ _ Huniq1.
          rewrite !dom_app in *. simpl in Hdom.
          { rewrite <- KeySetProperties.remove_add with (x:=X)...
            rewrite <- KeySetProperties.remove_add with (x:=X) (s:=dom ts1b)...
            clear - Hdom. apply remove_m...
            fsetdec.
          }
        * rewrite <- app_assoc in Huniq2. 
          apply uniq_app_iff in Huniq2. destruct_hypos...
          rewrite <- app_assoc. 
          apply uniq_app_iff. repeat split...
          { apply uniq_reorder_1... }
          { apply disjoint_app_l in H4. destruct_hypos. apply disjoint_app_3... }
      + destruct_hypos. apply app_eq_nil in H. destruct_hypos. subst.
        simpl in Hdom. inversion Huniq1;subst.
        destruct ts1b. { apply collect_typ_not_nil in Hct2. exfalso... }
        destruct p as [X' ?].
        specialize (Hdom X'). simpl in *. fsetdec.
    }

    destruct_hypos. simpl in H2.
    inversion Huniq1;subst.
    apply collect_typ_inv in H...
    destruct H as [(B1' & B2' & ?)|?].
    2:{ destruct_hypos. apply app_eq_nil in H. destruct_hypos. subst.
        simpl in Hdom.
        destruct ts1a. { apply collect_typ_not_nil in H2. exfalso... }
        destruct p as [X' ?].
        specialize (Hdom X'). simpl in *. fsetdec. }
    epose proof IHts1a _ _ H2 B2' _ H5 Hct2. destruct_hypos.
    destruct (H3 (ts2a ++ ts2b)) as [B1'' [B2'' [ts2a' [ts2b' ?]]]]...
    { pose proof fresh_mid_head _ _ _ _ _ Huniq2.
      pose proof fresh_mid_tail _ _ _ _ _ Huniq2. simpl in Huniq1.
      pose proof uniq_cons_2 _ _ _ _ Huniq1.
      rewrite !dom_app in *. simpl in Hdom.
      { rewrite <- KeySetProperties.remove_add with (x:=X)...
        rewrite <- KeySetProperties.remove_add with (x:=X) (s:=dom ts2a \u dom ts2b)...
        clear - Hdom. apply remove_m...
        fsetdec.
      }
    }
    { apply uniq_remove_mid in Huniq2... }
    
    exists (typ_and B1' B1''), B2'', ((X ~ t' ++ ts2a')), ts2b'. destruct_hypos.
    split;[|split;[|split;[|split;[|split]]]]...
    + eapply permute_trans. { apply H. }
      eapply permute_trans. 
      { eapply permute_and_cong;[|apply H8]. eapply permute_refl;eauto... }
      eapply permute_assoc... eapply permute_refl;eauto.
    + simpl. fsetdec.
    + simpl. constructor...
      inversion Huniq1;subst.  rewrite !dom_app in *. 
      fsetdec.
Qed.



Lemma sub_and_cons: forall E A1 A2 B1 B2,
  Compatible A1 A2 ->
  Compatible B1 B2 ->
  sub E A1 B1 ->
  sub E A2 B2 ->
  sub E (typ_and A1 A2) (typ_and B1 B2).
Proof with auto.
  intros.
  apply sa_and_both...
  + apply sa_and_a... get_well_form...
  + apply sa_and_b... get_well_form...
Qed.


Lemma equiv_and_cons: forall E A1 A2 B1 B2,
  Compatible A1 A2 ->
  Compatible B1 B2 ->
  equiv E A1 B1 ->
  equiv E A2 B2 ->
  equiv E (typ_and A1 A2) (typ_and B1 B2).
Proof with auto.
  intros.
  destruct H1. destruct H2.
  split.
  - apply sub_and_cons...
  - apply sub_and_cons...
Qed.

Lemma collect_typ_det: forall A ts1 ts2,
  collect_typ A ts1 ->
  collect_typ A ts2 ->
  ts1 = ts2.
Proof with auto.
  intros A ts1 ts2 Hct1 Hct2.
  generalize dependent ts2.
  generalize dependent ts1.
  induction A;intros;try solve [inversion Hct1].
  (* - inversion Hct1;inversion Hct2;subst... *)
  - inversion Hct1;inversion Hct2;subst...
  - inversion Hct1;inversion Hct2;subst...
    apply IHA1 with(ts2:= ts4) in H1 ...
    apply IHA2 with(ts2:= ts5) in H3 ...
    subst...
Qed.

Lemma permute_collect_ty_ex: forall A B,
  permute A B ->
  (forall ts1, collect_typ A ts1 -> exists ts2, collect_typ B ts2)
  /\( forall ts1, collect_typ B ts1 -> exists ts2, collect_typ A ts2).
Proof with auto.
  intros A B Hperm.
  induction Hperm;intros;split;intros ts1 Hct; try solve [inversion Hct;eauto].
  - inversion Hct;subst.
    apply IHHperm1 in H1. destruct H1 as [? ?].
    apply IHHperm2 in H3. destruct H3 as [? ?].
    eauto.
  - inversion Hct;subst.
    apply IHHperm2 in H1. destruct H1 as [? ?].
    apply IHHperm1 in H3. destruct H3 as [? ?].
    eauto.
  - apply IHHperm1 in Hct. destruct Hct as [? Hct].
    apply IHHperm2 in Hct. destruct Hct as [? ?].
    eauto.
  - apply IHHperm2 in Hct. destruct Hct as [? Hct].
    apply IHHperm1 in Hct. destruct Hct as [? ?].
    eauto.
  - inversion Hct;subst.
    apply IHHperm1 in H1. destruct H1 as [? ?].
    apply IHHperm2 in H3. destruct H3 as [? ?].
    eauto.
  - inversion Hct;subst.
    apply IHHperm1 in H1. destruct H1 as [? ?].
    apply IHHperm2 in H3. destruct H3 as [? ?].
    eauto.
  - apply IHHperm in Hct. destruct Hct as [? ?].
    eauto.
  (* - 
    inversion Hct;subst. inversion H1;subst.
    simpl in *.
    apply IHHperm in H3.
    eauto. *)
  - 
    apply IHHperm in Hct. eauto.
  (* - 
    apply IHHperm in Hct. eauto. *)
  - inversion Hct;subst. inversion H3;subst.
    apply IHHperm1 in H1. destruct H1 as [? ?].
    apply IHHperm2 in H2. destruct H2 as [? ?].
    apply IHHperm3 in H5. destruct H5 as [? ?].
    eauto.
  - inversion Hct;subst. inversion H1;subst.
    apply IHHperm1 in H2. destruct H2 as [? ?].
    apply IHHperm2 in H5. destruct H5 as [? ?].
    apply IHHperm3 in H3. destruct H3 as [? ?].
    eauto.
Qed.


Lemma permute_binds: forall A B ts1 ts2 l t,
  permute A B ->
  collect_typ A ts1 ->
  collect_typ B ts2 ->
  (binds l t ts1 <-> binds l t ts2).
Proof with auto.
  intros A B ts1 ts2 l t Hperm Hct1 Hct2.
  generalize dependent ts2.
  generalize dependent ts1.
  induction Hperm;intros.
  (* - inversion Hct1;inversion Hct2;subst... split... *)
  - inversion Hct1;inversion Hct2;subst... split...
  (* - inversion Hct1;inversion Hct2;subst...
    pose proof collect_typ_det H1 H6. subst.
    split;intro Hbinds.
    { analyze_binds Hbinds.
      + apply IHHperm with (ts2:=ts5) in BindsTac... }
    { analyze_binds Hbinds.
      + apply IHHperm with (ts1:=ts3) in BindsTac... } *)
  - inversion Hct1;inversion Hct2;subst...
    split;intro Hbinds.
    { analyze_binds Hbinds.
      + apply IHHperm1 with (ts2:=ts5) in BindsTac...
      + apply IHHperm2 with (ts2:=ts4) in BindsTac... }
    { analyze_binds Hbinds.
      + apply IHHperm2 with (ts1:=ts3) in BindsTac...
      + apply IHHperm1 with (ts1:=ts0) in BindsTac... }
  - 
    pose proof Hct1 as Hct1'.
    pose proof permute_collect_ty_ex Hperm1.
    apply H in Hct1'. clear H.
    destruct Hct1' as [ts3 Hct3].
    split;intro Hbinds.
    + apply IHHperm1 with (ts2:=ts3) in Hbinds...
      apply IHHperm2 with (ts2:=ts2) in Hbinds...
    + apply IHHperm2 with (ts1:=ts3) in Hbinds...
      apply IHHperm1 with (ts1:=ts1) in Hbinds...
  -
    inversion Hct1;inversion Hct2;subst...
    split;intro Hbinds.
    { analyze_binds Hbinds.
      + apply IHHperm1 with (ts2:=ts4) in BindsTac...
      + apply IHHperm2 with (ts2:=ts5) in BindsTac... }
    { analyze_binds Hbinds.
      + apply IHHperm1 with (ts1:=ts0) in BindsTac...
      + apply IHHperm2 with (ts1:=ts3) in BindsTac... }
  (* -
    inversion Hct2;subst... inversion H1;subst... *)
  -
    pose proof IHHperm _ Hct2.
    apply IHHperm with (ts2:=ts1) in Hct2...
    tauto.
  -
    inversion Hct1;subst. inversion H3;subst.
    inversion Hct2;subst. inversion H4;subst.
    split;intro Hbinds.
    { analyze_binds Hbinds.
      + apply IHHperm1 with (ts2:=ts2) in BindsTac...
      + apply IHHperm2 with (ts2:=ts6) in BindsTac0...
      + apply IHHperm3 with (ts2:=ts5) in BindsTac0... }
    { analyze_binds Hbinds.
      + apply IHHperm1 with (ts1:=ts0) in BindsTac0...
      + apply IHHperm2 with (ts1:=ts1) in BindsTac0...
      + apply IHHperm3 with (ts1:=ts4) in BindsTac...
    } 
Qed.


Lemma equiv_and_cons2: forall E A1 A2 B1 B2,
  Compatible A1 A2 ->
  Compatible B1 B2 ->
  equiv E A1 B1 ->
  equiv E A2 B2 ->
  equiv E (typ_and A2 A1) (typ_and B1 B2).
Proof with auto.
  intros.
  destruct H1. destruct H2.
  split.
  - apply sa_and_both...
    + apply sa_and_b... get_well_form...
      apply Compatible_symm...
    + apply sa_and_a... get_well_form...
      apply Compatible_symm...
  - apply sa_and_both...
    + apply sa_and_b... get_well_form...
    + apply sa_and_a... get_well_form...
    + apply Compatible_symm...
Qed.


Lemma permute_type: forall A B,
  permute A B ->
  type4rec A <-> type4rec B.
Proof with auto;try tauto.
  intros.
  induction H;try solve[split;auto]...
  - split;intros Hty;inversion Hty;subst...
    + apply type4_and; tauto.
    +  apply type4_and; tauto.
  - split;intros Hty;inversion Hty;subst...
    + apply type4_and; tauto.
    +  apply type4_and; tauto.
  (* - split;intros Hty.
    + constructor...
    + inversion Hty;subst... *)
  - split;intros Hty.
    + inversion Hty. inversion H5;subst...
      constructor... constructor...
    + inversion Hty. inversion H4;subst...
      constructor... constructor...
Qed.


Lemma cty_form_Compatible:
  forall A B ts1 ts2,
    collect_typ A ts1 ->
    collect_typ B ts2 ->
    disjoint ts1 ts2 ->
    Compatible A B.
Proof with auto.
  intros A B ts1 ts2 Hct1 Hct2 Hdisj.
  generalize dependent ts2.
  generalize dependent B.
  generalize dependent ts1.
  induction A;intros;try solve [inversion Hct1].
  (* - induction Hct2...
    constructor...
    + apply IHHct2_1...
      apply disjoint_sym in Hdisj.
      apply disjoint_app_1 in Hdisj...
    + apply IHHct2_2...
      apply disjoint_sym in Hdisj.
      apply disjoint_app_2 in Hdisj... *)
  - induction Hct2...
    * inversion Hct1;subst.
      constructor... apply disjoint_one_1 in Hdisj.
      simpl in Hdisj. fsetdec.
    * constructor...
      + apply IHHct2_1...
        apply disjoint_sym in Hdisj.
        apply disjoint_app_1 in Hdisj...
      + apply IHHct2_2...
        apply disjoint_sym in Hdisj.
        apply disjoint_app_2 in Hdisj...
  - inversion Hct1;subst.
    constructor.
    + eapply IHA1;eauto.
      apply disjoint_app_1 in Hdisj...
    + eapply IHA2;eauto.
      apply disjoint_app_2 in Hdisj...
Qed.

Lemma permute_dom: forall A B ts1 ts2,
  permute A B ->
  collect_typ A ts1 ->
  collect_typ B ts2 ->
  dom ts1 [=] dom ts2.
Proof with auto.
  intros A B ts1 ts2 Hper Hct1 Hct2.
  generalize dependent ts1.
  generalize dependent ts2.
  induction Hper; intros;try solve [inversion Hct1;inversion Hct2;subst;simpl;fsetdec].
  - inversion Hct1;inversion Hct2;subst.
    rewrite !dom_app.
    rewrite IHHper1 with (ts1:=ts0) (ts2:=ts5)...
    rewrite IHHper2 with (ts1:=ts3) (ts2:=ts4)... fsetdec.
  -
    pose proof Hct1 as Hct1'. 
    apply (permute_collect_ty_ex Hper1) in Hct1.
    destruct Hct1 as [ts' ?].
    rewrite IHHper1 with (ts1:=ts1) (ts2:=ts')...
  - inversion Hct1;inversion Hct2;subst.
    rewrite !dom_app.
    rewrite IHHper1 with (ts1:=ts0) (ts2:=ts4)...
    rewrite IHHper2 with (ts1:=ts3) (ts2:=ts5)... fsetdec.
  (* - inversion Hct2;subst.
    inversion H1;subst.
    rewrite IHHper with (ts1:=ts1) (ts2:=ts3)...
    simpl. fsetdec. *)
  - rewrite IHHper with (ts1:=ts2) (ts2:=ts1)...
    fsetdec.
  - inversion Hct2;inversion Hct1;subst.
    inversion H8;inversion H1;subst. rewrite !dom_app.
    rewrite IHHper1 with (ts1:=ts4) (ts2:=ts6)...
    rewrite IHHper2 with (ts1:=ts1) (ts2:=ts7)...
    rewrite IHHper3 with (ts1:=ts2) (ts2:=ts3)...
    fsetdec.
Qed.




Lemma permute_Compatible: forall A1 A2 B1 B2,
  permute A1 A2 ->
  permute B1 B2 ->
  Compatible A1 B1 ->
  Compatible A2 B2.
Proof with auto.
  intros.
  pose proof collect_typ_ex H1.
  apply Compatible_symm in H1.
  pose proof collect_typ_ex H1.
  destruct H2 as [ts1 ?].
  destruct H3 as [ts2 ?].
  pose proof H2 as H2'.
  apply (permute_collect_ty_ex H) in H2'.
  destruct H2' as [ts3 ?].
  pose proof H3 as H3'.
  apply (permute_collect_ty_ex H0) in H3'.
  destruct H3' as [ts4 ?].
  pose proof permute_dom H H2 H4.
  pose proof permute_dom H0 H3 H5.
  eapply cty_form_Compatible;try eassumption.
  hnf. intros. eapply Compatible_disjoint in H1;try eassumption.
  hnf in H1. specialize (H1 a). fsetdec.
Qed.

Lemma permute_ex_cty: forall T1 T2,
  permute T1 T2 ->
  exists ts1 ts2, collect_typ T1 ts1 /\ collect_typ T2 ts2.
Proof with auto.
  intros. induction H;eauto.
  - destruct IHpermute1 as [ts1' [ts2' ?]],
    IHpermute2 as [ts1'' [ts2'' ?]]. destruct_hypos.
    exists (ts1' ++ ts1''), (ts2'' ++ ts2')...
  - destruct IHpermute1 as [ts1' [ts2' ?]],
    IHpermute2 as [ts1'' [ts2'' ?]]. destruct_hypos.
    eauto.
  - destruct IHpermute1 as [ts1' [ts2' ?]],
    IHpermute2 as [ts1'' [ts2'' ?]]. destruct_hypos.
    exists (ts1' ++ ts1''), (ts2' ++ ts2'')...
  (* - destruct IHpermute as [ts1' [ts2' ?]].
    destruct_hypos. exists ts1', (nil ++ ts2')... *)
  - destruct IHpermute as [ts1' [ts2' ?]].
    destruct_hypos. exists ts2', ts1'...
  - destruct IHpermute1 as [ts1' [ts2' ?]],
    IHpermute2 as [ts1'' [ts2'' ?]],
    IHpermute3 as [ts1''' [ts2''' ?]]. destruct_hypos.
    exists (ts1' ++ (ts1'' ++ ts1''')), ((ts2' ++ ts2'') ++ ts2''')...
Qed.


Lemma permute_WF: forall A B,
  permute A B ->
  (forall E, WF E A <-> WF E B).
Proof with auto;try tauto.
  intros.
  induction H;try solve[split;auto]...
  - split;intros Hty;inversion Hty;subst...
    + constructor...
      { eapply permute_Compatible;try eassumption. apply Compatible_symm... } 
    + constructor...
      { apply Compatible_symm.
        eapply permute_Compatible;try eassumption.
        apply permute_symm... apply permute_symm... }
  - split;intros Hty;inversion Hty;subst...
    + constructor...
      { eapply permute_Compatible;try eassumption. }
    + constructor...
      { apply Compatible_symm. apply Compatible_symm in H6.
        eapply permute_Compatible;try eassumption.
        apply permute_symm... apply permute_symm... }
  (* - split;intros Hty.
    + constructor...
      { destruct (permute_ex_cty H) as (ts1' & ts2' & ?).
        destruct_hypos.
        eapply cty_form_Compatible;eauto.
      }
    + inversion Hty;subst... *)
  - 
    destruct (permute_ex_cty H) as (ts1' & ts2' & H1a & H1b).
    destruct (permute_ex_cty H0) as (ts1'' & ts2'' & H2a & H2b).
    destruct (permute_ex_cty H1) as (ts1''' & ts2''' & H3a & H3b).
    pose proof permute_dom H H1a H1b.
    pose proof permute_dom H0 H2a H2b.
    pose proof permute_dom H1 H3a H3b.
    split;intros Hty.
    + inversion Hty. inversion H9;subst...
      apply Compatible_r_split in H10. destruct_hypos.
      eapply Compatible_disjoint with (ts1:=ts1') (ts2:=ts1'') in H5...
      eapply Compatible_disjoint with (ts1:=ts1') (ts2:=ts1''') in H6...
      eapply Compatible_disjoint with (ts1:=ts1'') (ts2:=ts1''') in H16...
      constructor...
      2:{ eapply cty_form_Compatible with (ts1:=ts2' ++ ts2'') (ts2:=ts2''')...
          hnf. intros a. specialize (H5 a). specialize (H6 a). specialize (H16 a).
          rewrite dom_app. fsetdec. }
      constructor...
      { eapply cty_form_Compatible with (ts1:=ts2') (ts2:=ts2'')...
        hnf. intros a. specialize (H5 a). specialize (H6 a). specialize (H16 a).
        fsetdec. }
    + inversion Hty. inversion H7;subst...
      apply Compatible_l_split in H10. destruct_hypos.
      eapply Compatible_disjoint with (ts1:=ts2') (ts2:=ts2''') in H5...
      eapply Compatible_disjoint with (ts1:=ts2'') (ts2:=ts2''') in H6...
      eapply Compatible_disjoint with (ts1:=ts2') (ts2:=ts2'') in H16...
      constructor...
      2:{ eapply cty_form_Compatible with (ts1:=ts1') (ts2:=ts1''++ ts1''')...
          hnf. intros a. specialize (H5 a). specialize (H6 a). specialize (H16 a).
          rewrite dom_app. fsetdec. }
      constructor...
      { eapply cty_form_Compatible with (ts1:=ts1'') (ts2:=ts1''')...
        hnf. intros a. specialize (H5 a). specialize (H6 a). specialize (H16 a).
        fsetdec. }
Qed.


Lemma permute_top_toplike: forall A B,
  permute A B ->
  (toplike A <-> toplike B).
Proof with (auto;try tauto).
  intros. induction H;eauto...
  - split;intros Ht.
    + inversion Ht;subst... constructor...
    + inversion Ht;subst... constructor...
  - split;intros Ht.
    + inversion Ht;subst... constructor...
    + inversion Ht;subst... constructor...
  (* - split;intros Ht.
    + constructor...
    + inversion Ht;subst... *)
  - split;intros Ht.
    + inversion Ht;subst. inversion H5;subst.
      constructor... constructor...
    + inversion Ht;subst. inversion H4;subst.
      constructor... constructor...
Qed.


Lemma Compatible_bot_absurd_through_sub: forall E A B,
  sub E A typ_bot ->
  Compatible A B ->
  False.
Proof with auto.
  intros. dependent induction H...
  + eapply Compatible_bot_absurd. apply H1.
  + inv_compatible.
  + apply IHsub... apply Compatible_l_split in H2; destruct_hypos...
  + apply IHsub... apply Compatible_l_split in H2; destruct_hypos...
Qed.

Lemma sub_nat_and_absurd: forall E A B,
  sub E (typ_and A B) typ_nat -> False.
Proof with auto.
  intros. dependent induction H...
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
Qed.


Lemma sub_bot_and_absurd: forall E A B,
  sub E (typ_and A B) typ_bot -> False.
Proof with auto.
  intros. dependent induction H...
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
Qed.




Lemma sub_and_arr_absurd: forall E A B C D,
  sub E (typ_and A B) (typ_arrow C D) -> False.
Proof with auto.
  intros. dependent induction H...
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
Qed.


Lemma sub_and_all_absurd: forall E A B C D,
  sub E (typ_and A B) (typ_all C D) -> False.
Proof with auto.
  intros. dependent induction H...
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
Qed.



Lemma sub_and_all_lb_absurd: forall E A B C D,
  sub E (typ_and A B) (typ_all_lb C D) -> False.
Proof with auto.
  intros. dependent induction H...
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
Qed.


Lemma sub_and_label_absurd: forall E A B C D,
  sub E (typ_and A B) (typ_label C D) -> False.
Proof with auto.
  intros. dependent induction H...
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
Qed.



Lemma sub_and_mu_absurd: forall E A B C,
  sub E (typ_and A B) (typ_mu C) -> False.
Proof with auto.
  intros. dependent induction H...
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
  - inversion H0;subst;inv_compatible.
    eapply IHsub;eauto.
    eapply IHsub;eauto.
Qed.

Lemma sub_top_and_absurd: forall E A B,
  sub E typ_top (typ_and A B) -> False.
Proof with auto.
  intros. dependent induction H...
  - inversion H0;subst;inv_compatible.
    eapply IHsub2;eauto.
Qed.


Lemma sub_single_and_absurd: forall E A B l T,
  sub E (typ_single l T) (typ_and A B) -> False.
Proof with auto.
  intros. dependent induction H...
  - inversion H0;subst;inv_compatible.
    + inversion H1;subst. 
      * inversion H;subst...
      * eapply IHsub1;eauto.
    + eapply IHsub2;eauto.
Qed.


Ltac inv_lbub := try solve [get_well_form;match goal with
  | [H1: wf_env ?E,
      H2: binds ?X (bind_sub _) ?E,
      H3: binds ?X (bind_sub_lb _) ?E |- _] =>
      pose proof binds_uniq _ _ _ H1 H2 H3 as C;inversion C
end].

Lemma sub_and_var_absurd: forall E A B (X:atom),
  sub E (typ_and A B) X ->
  sub E X (typ_and A B) -> False.
Proof with auto.
  intros.
  destruct (sub_tvar_inv H)as [?|[?|?]];destruct_hypos.
  - inversion H1.
  - destruct (sub_tvar_inv2 H0) as [?|[?|?]];destruct_hypos.
    + inversion H3.
    + inv_lbub.
    + inversion H3.
  - inversion H1.
Qed.
