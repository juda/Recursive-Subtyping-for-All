Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Reverse.


Lemma fl_tt_open_tt: forall (X:atom) T,
    fl_tt (open_tt T X)  = fl_tt T.
Proof with auto.
  intros. unfold open_tt. generalize 0. induction T;intros;simpl...
  - destruct (n0==n)...
  - rewrite <- (IHT1 n), <- (IHT2 n)...
  - rewrite <- (IHT1 n), <- (IHT2 (S n))...
  - rewrite <- (IHT n)...
  - rewrite <- (IHT1 n), <- (IHT2 (n))...
Qed.


Lemma fl_tt_subst_tt: forall X S T,
 fl_tt T [<=] fl_tt (subst_tt X S T).
Proof with auto.
  induction T;intros;simpl;try apply AtomSetProperties.subset_empty...
  + apply union_s_m...
  + apply union_s_m...
  + apply union_s_m... intros x...
  + apply union_s_m... reflexivity.
    fsetdec. 
Qed.


Lemma notin_fl_env: forall E X Y U,
    binds X (bind_sub U) E ->
    Y \notin fl_env E ->
    Y \notin fl_tt U.
Proof with eauto.
  induction E;intros...
  simpl in *.
  destruct a.
  destruct b...
  -
    analyze_binds H.
    inversion BindsTacVal...
    apply IHE with (X:=X)...
  -
    analyze_binds H.
    apply IHE with (X:=X)...
Qed.


Lemma EqDec_eq : forall (A B: typ),
    {A = B} + {A <> B}.
Proof with auto.
  intros.
  decide equality.
  decide equality. 
Qed.  


Inductive sub_env_ext  (E:env) (X:atom) (C D:typ) : env -> env -> Prop :=
  | sub_env_ext_base:
      wf_env E ->
      X \notin dom E ->
      sub_env_ext E X C D 
        (X ~ bind_sub typ_top ++ E) 
        (E) 
    
  | sub_env_ext_cons_1: forall E1 E2 T Y,
      Y \notin dom E2 ->
      sub_env_ext E X C D E1 E2 ->
      sub_env_ext E X C D
        (Y ~ bind_sub (subst_tt X (typ_label X (open_tt C X)) T) ++ E1)
        (Y ~ bind_sub (subst_tt X (typ_mu C) T) ++ E2)

  | sub_env_ext_cons_2: forall E1 E2 T Y,
      Y \notin dom E2 ->
      sub_env_ext E X C D E1 E2 ->
      sub_env_ext E X C D
        (Y ~ bind_sub (subst_tt X (typ_label X (open_tt D X)) T) ++ E1)
        (Y ~ bind_sub (subst_tt X (typ_mu D) T) ++ E2)
.


Lemma sub_env_ext_regular: forall E X C D E1 E2,
  sub_env_ext E X C D E1 E2 ->
  wf_env E.
Proof with auto.
  intros.
  induction H...
Qed.



Lemma sub_env_ext_sem: forall E X C D F G,
  sub_env_ext E X C D F G ->
  forall a U, 
  a <> X ->
  binds a (bind_sub U) F ->
  (exists T, 
    binds a (bind_sub (subst_tt X (typ_mu C) T)) G /\
    U = subst_tt X (typ_label X (open_tt C X)) T) \/
  (exists T,
    binds a (bind_sub (subst_tt X (typ_mu D) T)) G /\
    U = subst_tt X (typ_label X (open_tt D X)) T).
Proof with auto.
  intros E X C D F G H.
  induction H;intros.
  -
    left.
    exists U.
    inversion H2;subst. { inversion H3;subst... exfalso... }
    assert (X `notin` fv_tt U).
    { apply notin_fv_tt_fv_env with (E:=E) (Y:=a)...
      rewrite fv_env_ls_dom... }
    rewrite <- subst_tt_fresh...
    rewrite <- subst_tt_fresh...
  -
    inversion H2;subst...
    { inversion H3;subst. left. exists T... }
    destruct (IHsub_env_ext a U) as [[T' [Hbinds Heq]] | [T' [Hbinds Heq]]]...
    * left. exists T'...
    * right. exists T'...
  -
    inversion H2;subst...
    { inversion H3;subst. right. exists T... }
    destruct (IHsub_env_ext a U) as [[T' [Hbinds Heq]] | [T' [Hbinds Heq]]]...
    * left. exists T'...
    * right. exists T'...
Qed.


Lemma sub_env_ext_flip: forall E X C D F G,
  sub_env_ext E X C D F G ->
  sub_env_ext E X D C F G.
Proof with auto.
  intros.
  induction H.
  - apply sub_env_ext_base...
  - apply sub_env_ext_cons_2...
  - apply sub_env_ext_cons_1...
Qed.


Lemma sub_env_ext_app: forall E X C D F G,
  sub_env_ext E X C D F G ->
  exists G', G = G' ++ E.
Proof with auto.
  intros.
  induction H.
  - exists  nil...
  - destruct IHsub_env_ext as [G' eq]; subst.
    exists ( Y ~ bind_sub (subst_tt X (typ_mu C) T) ++ G')...
  - destruct IHsub_env_ext as [G' eq]; subst.
    exists ( Y ~ bind_sub (subst_tt X (typ_mu D) T) ++ G')...
Qed.

Lemma sub_env_ext_app': forall E X C D F G,
  sub_env_ext E X C D F G ->
  exists F', F = F' ++ X ~ bind_sub typ_top ++ E.
Proof with auto.
  intros.
  induction H.
  - exists  nil...
  - destruct IHsub_env_ext as [F' eq]; subst.
    exists ( Y ~ bind_sub (subst_tt X (typ_label X (open_tt C X)) T) ++ F')...
  - destruct IHsub_env_ext as [F' eq]; subst.
    exists ( Y ~ bind_sub (subst_tt X (typ_label X (open_tt D X)) T) ++ F')...
Qed.


Lemma sub_env_ext_add_top: forall E X C D F G Y,
  sub_env_ext E X C D F G ->
  Y \notin dom G ->
  sub_env_ext E X C D (Y ~ bind_sub typ_top ++ F) (Y ~ bind_sub typ_top ++ G).
Proof with auto.
  intros.
  replace (Y ~ bind_sub typ_top ++ F)
    with (Y ~ bind_sub (subst_tt X (typ_label X (open_tt C X)) typ_top) ++ F)...
  replace (Y ~ bind_sub typ_top ++ G)
    with (Y ~ bind_sub (subst_tt X (typ_mu C) typ_top) ++ G)...
  apply sub_env_ext_cons_1...
Qed.

Lemma sub_env_ext_WF_base: forall m E X C D F G A,
  sub_env_ext E X C D F G -> X `notin` fl_tt A ->
  WF E (typ_mu (choose m C D)) ->
  WF F (subst_tt X (typ_label X (open_tt (choose m C D) X)) A) ->
  type A.
Proof with auto.
  intros m E X C D F G A Hsub Hfl Hwfc Hwf.
  assert (Hty: type (typ_label X (open_tt (choose m C D) X))).
  {
    apply WF_type in Hwfc. inversion Hwfc;subst.
    pick_fresh X0.
    constructor.
    replace (open_tt (choose m C D) X) with (subst_tt X0 X (open_tt (choose m C D) X0)).
    { apply subst_tt_type... }
    rewrite <- subst_tt_intro... destruct m...
  }
  generalize dependent G.
  dependent induction Hwf;intros...
  -
    destruct A; try solve [inversion x
    |simpl in *;destruct (a==X);inversion x]...
  -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
  (* -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]... *)
  -
    destruct A; try solve [inversion x]. constructor...
  -
    destruct A; try solve [inversion x
    |simpl in *;destruct (a==X);inversion x]...
    simpl in Hfl.
    simpl in x. inversion x. subst.
    simpl. constructor...
    + eapply IHHwf1 with (G:=G);try eassumption;auto.
    + eapply IHHwf2 with (G:=G);try eassumption;auto.
  -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl in Hfl.
    simpl in x. inversion x. subst.
    pose proof WF_type Hwfc.
    inversion H1;subst. 
    simpl. apply type_all with (L:=L \u {{X}}\u L0 \u fv_tt C \u dom G)...
    { eapply IHHwf with (G:=G);try eassumption;auto. } 
    intros. specialize_x_and_L X0 L.
    eapply H0
      with (G:= X0 ~ bind_sub (subst_tt X (typ_mu (choose m C D)) A1) ++ G);
      try eassumption.
    + rewrite fl_tt_open_tt...
    + rewrite <- subst_tt_open_tt_var...
    + destruct m. constructor... constructor...
  -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl in x. inversion x. subst.
    pose proof WF_type Hwfc.
    inversion H3;subst.
    simpl. apply type_mu with (L:=L \u {{X}}\u L0 \u fv_tt C \u dom G)...
    +
      intros. specialize_x_and_L X0 L.
      eapply H0
        with (G:= X0 ~ bind_sub typ_top ++ G);
        try eassumption.
      * rewrite fl_tt_open_tt...
      * rewrite <- subst_tt_open_tt_var...
      * apply sub_env_ext_add_top...
  - 
    destruct A; try solve [inversion x].
    + simpl in *. destruct (a==X);inversion x;subst...
    + simpl in *. constructor. inversion x; subst...
      eapply IHHwf;try eassumption; auto.
  -
    destruct A; try solve [inversion x].
    + simpl in *. destruct (a==X);inversion x;subst...
    + simpl in *. constructor...
  -
    destruct A; try solve [inversion x].
    + simpl in *. destruct (a==X);inversion x;subst...
    + simpl in *. inversion x;subst. constructor...
      * eapply IHHwf1;try eassumption...
      * eapply IHHwf2;try eassumption...
      *
        apply subst_label_rt_type with (Z:=X) in H.
        rewrite drop_label_reverse_type in H...
Qed.


Lemma subst_tt_collect: forall T i X A,
    i `notin` collectLabel T ->
    rt_type T ->
    type T ->
    i `notin` collectLabel (subst_tt X A T).
Proof with auto.
  intros.
  induction H1;try solve [inversion H0]...
  simpl in *.
  apply notin_union in H.
  destruct H.
  apply notin_union.
  split...
Qed.  


Lemma subst_tt_collect2: forall T i X A,
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


Lemma subst_tt_collect3: forall T i X A,
    i `in` collectLabel (subst_tt X A T) ->
    rt_type T ->
    type T ->
    i `in` collectLabel T.
Proof with auto.
  intros.
  induction H1;try solve [inversion H0]...
  simpl in *.
  apply union_iff in H. apply union_iff.
  destruct H...
Qed.  


Lemma sub_env_ext_WF_subst: forall m E X C D F G A,
  sub_env_ext E X C D F G -> X `notin` fl_tt A ->
  WF E (typ_mu (choose m C D)) ->
  WF F (subst_tt X (typ_label X (open_tt (choose m C D) X)) A) ->
  WF G (subst_tt X (typ_mu (choose m C D)) A) .
Proof with auto.
  intros m E X C D F G A Hsub Hfl Hwfc Hwf.
  assert (Hty: type (typ_label X (open_tt (choose m C D) X))).
  {
    apply WF_type in Hwfc. inversion Hwfc;subst.
    pick_fresh X0.
    constructor.
    replace (open_tt (choose m C D) X) with (subst_tt X0 X (open_tt (choose m C D) X0)).
    { apply subst_tt_type... }
    rewrite <- subst_tt_intro... destruct m...
  }
  assert (Hty': type A).
  {
    eapply sub_env_ext_WF_base with (m:=m) (E:=E) (X:=X) (C:=C) (D:=D) (F:=F) (G:=G)...
  }

  generalize dependent G.
  dependent induction Hwf;intros...
  -
    destruct A; try solve [inversion x
    |simpl in *;destruct (a==X);inversion x]...
  -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
  (* -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]... *)
  -
    destruct A; try solve [inversion x].
    simpl in *. destruct (a==X);subst;inversion x;subst.
    pose proof (sub_env_ext_sem Hsub _ n H).
    destruct H0 as [[T [Hbinds Heq]]|[T [Hbinds Heq]]];subst.
    { apply (WF_var _ _ _ Hbinds). }
    { apply (WF_var _ _ _ Hbinds). }
  -
    destruct A; try solve [inversion x
    |simpl in *;destruct (a==X);inversion x]...
    simpl in Hfl. inversion Hty';subst.
    simpl in x. inversion x. subst.
    simpl. constructor...
  -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl in Hfl. inversion Hty';subst.
    simpl in x. inversion x. subst.
    pose proof WF_type Hwfc.
    inversion H1;subst. 
    simpl. apply WF_all with (L:=L \u {{X}}\u L0 \u fv_tt C \u dom G)...
    intros. specialize_x_and_L X0 L.
    rewrite subst_tt_open_tt_var...
    { apply H0...
      + rewrite fl_tt_open_tt...
      + rewrite <- subst_tt_open_tt_var...
      + destruct m; constructor...
    }
  -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl in x. inversion x. subst.
    inversion Hty';subst.
    pose proof WF_type Hwfc.
    inversion H3;subst.
    simpl. apply WF_rec with (L:=L \u {{X}}\u L0 \u fv_tt C \u dom G)...
    +
      intros. specialize_x_and_L X0 L.
      rewrite subst_tt_open_tt_var...
      apply H0...
      *
        rewrite fl_tt_open_tt...
      *
        rewrite <- subst_tt_open_tt_var...
      *
        apply sub_env_ext_add_top...
    +
      intros. specialize_x_and_L X0 L.
      rewrite <- subst_tt_open_tt_twice...
      apply H2...
      *
        apply notin_fl_tt_open... solve_notin.
      *
        rewrite  subst_tt_open_tt_twice...
      *
        pick_fresh X'.
        rewrite subst_tt_intro with (X:=X')...
        apply subst_tt_type...
      *
        apply sub_env_ext_add_top...
  - 
    destruct A; try solve [inversion x].
    + simpl in *. destruct (a==X);inversion x;subst...
      pose proof sub_env_ext_app Hsub as [G' eq].
      subst. add_nil. apply WF_weakening...
    + simpl in *.
      inversion Hty';subst. 
      destruct (a==X);inversion x;subst...
  -
    destruct A; try solve [inversion x].
    + simpl in *. destruct (a==X);inversion x;subst...
    + simpl in *. constructor...
  -
    destruct A; try solve [inversion x].
    + simpl in *. destruct (a==X);inversion x;subst...
    + simpl in *. inversion x;subst.
      inversion Hty';subst. constructor...
      * apply subst_label_rt_type with (Z:=X) in H.
        rewrite drop_label_reverse_type in H...
        apply Infrastructure.subst_tt_rt_type...
        { get_type... }
      *
        assert (Hrt: rt_type A2).
        {
          apply subst_label_rt_type with (Z:=X) in H.
          rewrite drop_label_reverse_type in H...
        }
        intros Hc.
        eapply subst_tt_collect3 in Hc...
        apply H0. apply subst_tt_collect2...
Qed.


Lemma type_mu_open: forall t (X:atom),
  type (typ_mu t) ->
  type (open_tt t X).
Proof with auto.
  intros.
  inversion H;subst.
  pick_fresh Y.
  specialize_x_and_L Y L.
  rewrite subst_tt_intro with (X:=Y)...
  apply subst_tt_type...
Qed.


Lemma fl_tt_subst_tt2: forall X S T,
  fl_tt (subst_tt X S T) [<=] fl_tt T  \u fl_tt S.
Proof with auto.
  induction T;intros;simpl;try apply AtomSetProperties.subset_empty...
  + destruct (a==X); simpl; fsetdec.
  + fsetdec.
  + fsetdec.
  + fsetdec.
  + fsetdec.
Qed.


Lemma lookup_some_subst: forall i A T X B,
    type A -> rt_type A ->
    Tlookup i A = Some T->
    Tlookup i (subst_tt X B A) = Some (subst_tt X B T).
Proof with auto.
  intros.
  induction H;try solve [inversion H0]...
  inversion H1...
  simpl in *.
  destruct (i0==i);subst...
  inversion H1...
Qed.


Lemma lookup_some_in_fl_tt : forall i A x,
    type A -> rt_type A ->
    Tlookup i A = Some x->
    fl_tt x [<=] fl_tt A.
Proof with auto.
  intros.
  induction H;try solve [inversion H0]...
  inversion H1...
  simpl in *.
  destruct (i0==i);subst...
  inversion H1;subst...
  rewrite union_swap_assoc...
  apply KeySetProperties.union_subset_1...
  apply IHtype2 in H1...
  rewrite KeySetProperties.union_sym...
  apply union_subset_6...
  rewrite KeySetProperties.union_sym...
  apply union_subset_6...
Qed.


Lemma sub_generalize_intensive : forall m n r E X C D A B G F,
sub_env_ext E X C D F G ->
wf_env G -> wf_env F ->
sub E (typ_mu ( (choose m C D)))  
      (typ_mu ((choose m D C))) ->
X \notin fv_tt C \u fv_tt D \u fl_env E  \u fl_env G \u fl_tt A \u fl_tt B \u dom E  \u dom G \u fl_tt C \u fl_tt D  ->
sub F (subst_tt X (typ_label X (open_tt (choose n C (choose r C D)) X)) A) (subst_tt X (typ_label X  (open_tt (choose n D (choose r C D)) X)) B) ->
sub G (subst_tt X (typ_mu (choose n C (choose r C D ))) A) 
      (subst_tt X (typ_mu (choose n D (choose r C D ))) B).
Proof with auto.
  intros m n r E X C D A B G F Henv Hwfe1 Hwfe2 Hcd Hx Hsub.
  (* 
  generalize dependent n. *)
  generalize dependent m.
  generalize dependent G.


  dependent induction Hsub;intros.
    -
    (* nat <: nat *)
    dependent destruction A;try solve [inversion x0
      |simpl in *;destruct (a==X);inversion x0]...
    dependent destruction B;try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
  -
    (* X <: X *)
    dependent destruction A;try solve [inversion x0
      |simpl in *;destruct (a==X);inversion x0]...
    dependent destruction B;try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl; simpl in x0, x. 
    destruct (a == X), (a0 == X);subst.
    + inversion x0.
    + inversion x0.
    + inversion x.
    + inversion x0;subst. inversion x;subst.
      apply sa_fvar... inversion H0;subst.
      pose proof (sub_env_ext_sem Henv _ n0 H3).
      destruct H1 as [[T [Hbinds Heq]]|[T [Hbinds Heq]]];subst.
      { apply (WF_var _ _ _ Hbinds). }
      { apply (WF_var _ _ _ Hbinds). }
  -
    (* A <: Top *)
    (* eapply equiv_env_sub. apply Heqenv. *)
    dependent destruction B;try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl. apply sa_top...
      destruct m, n, r;get_well_form;simpl in *;
      try solve 
      [apply sub_env_ext_WF_subst with (m:=Pos) (C:=C) (D:=D) (E:=E) (F:=E0);auto|
      apply sub_env_ext_WF_subst with (m:=Neg) (C:=C) (D:=D) (E:=E) (F:=E0);auto]...
  
  (* -
    (* Bot <: A *)
    (* eapply equiv_env_sub. apply Heqenv. *)
    dependent destruction A;try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl. apply sa_bot...
      destruct m, n, r;get_well_form;simpl in *;
      try solve 
      [apply sub_env_ext_WF_subst with (m:=Pos) (C:=C) (D:=D) (E:=E) (F:=E0);auto|
      apply sub_env_ext_WF_subst with (m:=Neg) (C:=C) (D:=D) (E:=E) (F:=E0);auto]... *)
  -
    destruct n; cbn [choose] in *.
    *
      (* X <: A <: B  unfolding lemma part *)
      destruct A; try solve [inversion x].
      simpl in x. simpl. destruct (a == X);subst;inversion x;subst.

      pose proof sub_env_ext_sem Henv _  n H.

      destruct H0 as [[T [Hbinds Heq]]|[T [Hbinds Heq]]];
      subst U;
      apply (sa_trans_tvar _ _ _ _ Hbinds).
        
      +
        apply IHHsub with (m:=m) (n:=Pos) (r:=r)...
        { solve_notin. 
          apply notin_fl_env with (Y:= X) in Hbinds...
          rewrite <- fl_tt_subst_tt in Hbinds...
        }
      +
        apply IHHsub with (r:=Neg) (n:=Neg) (m:=m) (C:=C)...
        { solve_notin.
          apply notin_fl_env with (Y:= X) in Hbinds...
          rewrite <- fl_tt_subst_tt in Hbinds...
        }
    *
      (* subst lemma part *)
      destruct A; try solve [inversion x].
      simpl in x. simpl. destruct (a == X);subst;inversion x;subst.

      pose proof sub_env_ext_sem Henv _  n H.

      destruct H0 as [[T [Hbinds Heq]]|[T [Hbinds Heq]]];
      subst U;
      apply (sa_trans_tvar _ _ _ _ Hbinds).
      +
        destruct r;simpl.
        {
          apply IHHsub with (m:=m) (n:=Neg) (r:=Pos) (D0:=D)...
          {  solve_notin.
            apply notin_fl_env with (Y:= X) in Hbinds...
            rewrite <- fl_tt_subst_tt in Hbinds...
          }
        }
        {
          apply IHHsub with (m:=m) (n:=Pos) (r:=Pos)...
          { solve_notin.
            apply notin_fl_env with (Y:= X) in Hbinds...
            rewrite <- fl_tt_subst_tt in Hbinds...
          }
        }
      +
        destruct r;simpl.
        { apply IHHsub with (m:=flip m) (n:=Pos) (r:=Pos)...
          { apply sub_env_ext_flip... }
          { solve_notin.           
            apply notin_fl_env with (Y:= X) in Hbinds...
            rewrite <- fl_tt_subst_tt in Hbinds...
          }
          { destruct m... }
        }
        { apply IHHsub with (m:=m) (n:=Neg) (r:=Neg) (C0:=C)...
          { solve_notin.
            apply notin_fl_env with (Y:= X) in Hbinds...
            rewrite <- fl_tt_subst_tt in Hbinds...
          }
        }


  -
    (* arrow *)
    destruct A; try solve [inversion x0].
    { simpl in x0. destruct (a == X);subst;inversion x0;subst. }
    destruct B;try solve [inversion x].
    { simpl in x. destruct (a == X);subst;inversion x;subst. }
    inversion x0;subst. inversion x;subst.
    destruct n; cbn [choose] in *.
    *
      (* unfolding lemma part *)
      simpl. apply sa_arrow.
      + apply IHHsub1 with (m:= flip m) (n:=Pos) (r:=r)...
        { apply sub_env_ext_flip... } 
        { simpl in Hx. solve_notin. }
        { destruct m... }
      + apply IHHsub2 with (m:=m) (n:=Pos) (r:=r)...
        { simpl in Hx. solve_notin. }
    *
      (* substitution lemma part *)
      simpl. apply sa_arrow.
      + apply IHHsub1 with (m:=m) (n:=Neg) (r0:=r)... 
        { simpl in Hx. solve_notin. }
      + apply IHHsub2 with (m:=m) (n:=Neg) (r0:=r)...
        { simpl in Hx. solve_notin. }

  -
    (* all *)
    destruct B; try solve [inversion x].
    { simpl in x. destruct (a == X);subst;inversion x;subst. }
    destruct A;try solve [inversion x0].
    { simpl in x0. destruct (a == X);subst;inversion x0;subst. }
    inversion x0;inversion x;subst.
    destruct n; cbn [choose] in *;simpl.
    *
      (* unfolding lemma part *)
      assert (Htyc: type (typ_mu C)). 
      { destruct m; get_type... }
      assert (Htyd: type (typ_mu D)). 
      { destruct m; get_type... }
      inversion Htyc;subst.
      inversion Htyd;subst.



      apply sa_all with (L:=L \u {{ X}} \u dom G \u dom E0 \u L1 \u L0 \u fv_tt C \u fv_tt D) ...
      +
        apply IHHsub1 with (m:=m) (n:=Pos) (r:=r)...
        (* { apply sub_env_ext_flip... }  *)
        { simpl in Hx. solve_notin. }
        (* { destruct m... } *)
      +
        apply IHHsub2 with (m:=flip m) (n:=Pos) (r:=r)...
        { apply sub_env_ext_flip... } 
        { simpl in Hx. solve_notin. }
        { destruct m... }
      +
        intros. 
        rewrite subst_tt_open_tt_var... 
        rewrite subst_tt_open_tt_var...
        specialize_x_and_L X0 L.


        apply H0 with (m:=m) (n:=Pos) (r:=r)...
        { constructor... get_well_form... }
        { simpl. rewrite subst_tt_open_tt... 
          2:{ constructor. get_type.
              apply type_mu_open;destruct m...
          }
          simpl. destruct (X0 == X)...
          exfalso. subst. clear - H1.  fsetdec. }
        { simpl. rewrite subst_tt_open_tt...
          2:{ constructor. get_type.
              apply type_mu_open;destruct m...
          }
          simpl. destruct (X0 == X)...
          exfalso. subst. clear - H1.  fsetdec. }
        { 
          constructor...
        }
        { constructor...
          get_well_form...
          apply sub_env_ext_WF_subst with (m:=Neg) (C:=C) (D:=D) (E:=E) (F:=E0)...
          { simpl in Hx... }
          destruct m;simpl in *; get_well_form...
        }
        { simpl in Hx. simpl. solve_notin.
          rewrite fl_tt_subst_tt2... }
          
    *
      (* subsitution lemma part *)
      assert (Htyc: type (typ_mu C)). 
      { destruct m; get_type... }
      assert (Htyd: type (typ_mu D)). 
      { destruct m; get_type... }
      inversion Htyc;subst.
      inversion Htyd;subst.

      apply sa_all with (L:=L \u {{ X}} \u dom G \u dom E0 \u L1 \u L0 \u fv_tt C \u fv_tt D) ...
      +
        apply IHHsub1 with (m:=m) (n:=Neg) (r0:=r)...
        (* { destruct r; apply sub_env_ext_flip... }  *)
        { simpl in Hx. solve_notin. }
        (* { destruct m... } *)
      +
        apply IHHsub2 with (m:=m) (n:=Neg) (r0:=r)...
        (* { apply sub_env_ext_flip... }  *)
        { simpl in Hx. solve_notin. }
        (* { destruct m... } *)
      +
        intros. 
        rewrite subst_tt_open_tt_var... 
        2:{ destruct r, m;get_type... }
        rewrite subst_tt_open_tt_var...
        2:{ destruct r, m; get_type... }
        specialize_x_and_L X0 L.


        apply H0 with (m:=m) (n:=Neg) (r0:=r)...
        { constructor... get_well_form... }
        { simpl. rewrite subst_tt_open_tt... 
          2:{ constructor. apply type_mu_open. destruct r, m; get_type... }
          simpl. destruct (X0 == X)...
          exfalso. subst. clear - H1.  fsetdec. }
        { simpl. rewrite subst_tt_open_tt... 
          2:{ constructor. apply type_mu_open. destruct r, m; get_type... }
          simpl. destruct (X0 == X)...
          exfalso. subst. clear - H1.  fsetdec. }
        {
          destruct r; 
          constructor...
        }
        { constructor... 
          get_well_form...
          apply sub_env_ext_WF_subst with (m:=r) (C:=C) (D:=D) (E:=E) (F:=E0)...
          { simpl in Hx... }
          destruct m, r;simpl in *; get_well_form...
        }
        { simpl in Hx. solve_notin. 
          rewrite fl_tt_subst_tt2.
          destruct r... }


  -
    destruct B; try solve [inversion x].
    { simpl in x. destruct (a == X);subst;inversion x;subst. }
    destruct A;try solve [inversion x0].
    { simpl in x0. destruct (a == X);subst;inversion x0;subst. }
    
    simpl in x0. simpl in x.
    inversion x0;inversion x;subst. simpl. 
    
    destruct n; cbn [choose] in *;simpl.
    *
      (* unfolding lemma part *)
      apply sa_rec with (L:=L \u {{ X}} \u dom G \u dom E0)...

      +
        intros. 
        rewrite subst_tt_open_tt_var... 2:{ destruct m;get_type... }
        specialize_x_and_L X0 L. 
        rewrite subst_tt_open_tt_var in H...
        2:{ constructor. apply type_mu_open. get_type. destruct m... }
        apply sub_env_ext_WF_subst with (m:=Pos) (C:=C) (D:=D) 
          (E:=E) (F:=X0 ~ bind_sub typ_top ++ E0)...
        2:{ simpl in Hx... rewrite fl_tt_open_tt... }
        2:{ simpl. destruct m;get_well_form... }
        apply sub_env_ext_add_top...
      +
        intros. 
        rewrite subst_tt_open_tt_var... 2:{ destruct m;get_type... }
        specialize_x_and_L X0 L. 
        rewrite subst_tt_open_tt_var in H0...
        2:{ constructor. apply type_mu_open. get_type. destruct m... }
        apply sub_env_ext_WF_subst with (m:=Neg) (C:=C) (D:=D) 
          (E:=E) (F:=X0 ~ bind_sub typ_top ++ E0)...
        2:{ simpl in Hx... rewrite fl_tt_open_tt... }
        2:{ simpl. destruct m;get_well_form... }
        apply sub_env_ext_add_top...

      +
        intros.
        rewrite <- subst_tt_open_tt_twice... 2:{ get_type;destruct m... }
        rewrite <- subst_tt_open_tt_twice... 2:{ get_type;destruct m... }
        specialize_x_and_L X0 L.
      
        apply H2 with (m:=m) (n:=Pos) (r:=r)...
        { rewrite  subst_tt_open_tt_twice...
          constructor. simpl. apply type_mu_open. get_type;destruct m... }
        { rewrite  subst_tt_open_tt_twice...
          constructor. simpl. apply type_mu_open. get_type;destruct m... }
        { apply sub_env_ext_add_top... }
        { solve_notin. }
   *
      (* subsitution lemma part *)
      apply sa_rec with (L:=L \u {{ X}} \u dom G \u dom E0)...
      +
        intros. 
        rewrite subst_tt_open_tt_var... 2:{ destruct r, m;get_type... }
        specialize_x_and_L X0 L. 
        rewrite subst_tt_open_tt_var in H...
        2:{ constructor. destruct r; apply type_mu_open;simpl; get_type; destruct m... }
        apply sub_env_ext_WF_subst with (m:=r) (C:=C) (D:=D) 
          (E:=E) (F:=X0 ~ bind_sub typ_top ++ E0)...
        2:{ simpl in Hx. rewrite fl_tt_open_tt... }
        2:{ simpl. destruct m, r;get_well_form... }
        apply sub_env_ext_add_top...
      +
        intros. 
        rewrite subst_tt_open_tt_var... 2:{ destruct r, m;get_type... }
        specialize_x_and_L X0 L. 
        rewrite subst_tt_open_tt_var in H0...
        2:{ constructor. destruct r; apply type_mu_open;simpl; get_type; destruct m... }
        apply sub_env_ext_WF_subst with (m:=r) (C:=C) (D:=D) 
          (E:=E) (F:=X0 ~ bind_sub typ_top ++ E0)...
        2:{ simpl in Hx. rewrite fl_tt_open_tt... }
        2:{ simpl. destruct m, r;get_well_form... }
        apply sub_env_ext_add_top...
      +
        intros.
        rewrite <- subst_tt_open_tt_twice... 2:{ destruct r, m;get_type... }
        rewrite <- subst_tt_open_tt_twice... 2:{ destruct r, m;get_type... }
        specialize_x_and_L X0 L.
      
        apply H2 with (m:=m) (n:=Neg) (r0:=r)...
        { rewrite  subst_tt_open_tt_twice...
          constructor. simpl.
          destruct r; apply type_mu_open; get_type;destruct m... }
        { rewrite  subst_tt_open_tt_twice...
          constructor. simpl.
          destruct r; apply type_mu_open; get_type;destruct m... }
        { apply sub_env_ext_add_top... }
        { solve_notin. }
  -
    destruct B; try solve [inversion x];
    destruct A; try solve [inversion x0].
    +
      (* A and B are labels *)
      simpl in x. destruct (a == X);subst;inversion x;subst.
      simpl in x0. destruct (a0 == X);subst;inversion x0;subst.
      simpl. rewrite eq_dec_refl.
      pose proof sub_env_ext_app Henv as [G' eq].
      subst G. add_nil. apply Sub_weakening...
      destruct n.
      2:{ simpl. apply Reflexivity...
        destruct r, m;simpl in *; get_well_form...
        get_well_form... }
      cbn [choose] in *. destruct m; simpl in  Hcd...

      inversion Hcd;subst;inv_rt.
      apply sa_rec with (L:=L \u (fl_tt D) \u (fl_tt C) \u (fl_env E) \u {{X}} \u fv_tt C \u fv_tt D \u dom E0)...
      intros. specialize_x_and_L X0 L.
      rewrite_alist (nil ++ X0 ~ bind_sub typ_top ++ E) in H4.
      apply sub_nominal_inversion in H4...
      pose proof sub_env_ext_app' Henv as [F' eq].
      subst E0.
      rewrite_alist ( F' ++ X ~ bind_sub typ_top ++ E) in Hsub.
      apply sub_strengthening_env in Hsub...
      2:{ constructor... get_well_form... }
      2:{ apply WF_replacing_var with (X:=X0)... }
      2:{ apply WF_replacing_var with (X:=X0)... }
      apply sub_replacing_var with (Y:=X0) in Hsub ...
      2:{ constructor... get_well_form... }
      rewrite subst_tt_intro with (X:=X0)...
      rewrite subst_tt_intro with (X:=X0) (T2:=D)...
      eapply equiv_sub_subst with (E1:=nil) (S:=(typ_label X0 (open_tt C X0))); try solve[ split;auto]...
      split;constructor;apply Reflexivity;try solve [constructor;get_well_form;auto]...
    +
      (* A label. b not  *)
      simpl in x, x0. simpl. 
      destruct (a == X);subst;inversion x;subst.
      inversion x0;subst. simpl in Hx. clear - Hx. 
      exfalso. apply Hx.
      repeat (apply AtomSetImpl.union_3;
        try solve [repeat apply AtomSetImpl.union_2; apply AtomSetImpl.singleton_2;auto]).
    +
      (* B label. A not *)
      simpl in x, x0. simpl. 
      destruct (a0 == X);subst;inversion x0;subst.
      inversion x;subst. simpl in Hx. clear - Hx. 
      exfalso. apply Hx.
      repeat (apply AtomSetImpl.union_3;
        try solve [repeat apply AtomSetImpl.union_2; apply AtomSetImpl.singleton_2;auto]).
    +
      (* A B both variable *)
      simpl in x, x0. simpl.
      inversion x0;subst. inversion x;subst.
      constructor. apply IHHsub with (m:=m)...
      { simpl in Hx. clear - Hx. solve_notin. }
  -
    (* records *)
    assert (Hwf1: WF G (subst_tt X (typ_mu (choose n C (choose r C D))) A)).
    { 
      destruct r.
      + apply sub_env_ext_WF_subst with (m:=Pos) (D:=D) (E:=E) (G:=G) in H3...
        { destruct n;simpl... }
        { get_well_form; destruct n, m;simpl...  }
      + apply sub_env_ext_WF_subst with (m:=n) (D:=D) (E:=E) (G:=G) in H3...
        { get_well_form; destruct n, m;simpl...  }
    }
    assert (Hwf2: WF G (subst_tt X (typ_mu (choose n D (choose r C D))) B)).
    { 
      destruct n; cbn [choose] in *.
      + apply sub_env_ext_WF_subst with (m:=Neg) (C:=C) (E:=E) (G:=G) in H4...
        { get_well_form; destruct m;simpl...  }
      + apply sub_env_ext_WF_subst with (m:=r) (D:=D) (E:=E) (G:=G) in H4...
        { get_well_form; destruct m, r;simpl...  }
    }
    assert (Hrt1: rt_type A).
    {
      apply subst_label_rt_type with (Z:=X) in H0.
      rewrite drop_label_reverse_type in H0...
    }
    assert (Hrt2: rt_type B).
    {
      apply subst_label_rt_type with (Z:=X) in H1.
      rewrite drop_label_reverse_type in H1...
    }
    assert (Hty1: type A).
    {
      destruct n; cbn [choose] in *.
      + apply sub_env_ext_WF_base with (m:=Pos) (D:=D) (E:=E) (G:=G) in H3...
        { get_well_form; destruct m;simpl...  }
      + apply sub_env_ext_WF_base with (m:=r) (D:=D) (E:=E) (G:=G) in H3...
        { get_well_form; destruct m, r;simpl...  }
    }
    assert (Hty2: type B).
    {
      destruct n; cbn [choose] in *.
      + apply sub_env_ext_WF_base with (m:=Neg) (C:=C) (E:=E) (G:=G) in H4...
        { get_well_form; destruct m;simpl...  }
      + apply sub_env_ext_WF_base with (m:=r) (D:=D) (E:=E) (G:=G) in H4...
        { get_well_form; destruct m, r;simpl...  }
    }
    
    apply sa_rcd...
    + apply Infrastructure.subst_tt_rt_type...
      { get_type. destruct m,n,r... }
    + apply Infrastructure.subst_tt_rt_type...
      { get_type. destruct m,n,r... }
    +
      intro i. intros. specialize (H2 i).
      apply subst_tt_collect3  in H7... 
      apply subst_tt_collect2  with (X:=X)
        (A:=(typ_label X (open_tt (choose n D (choose r C D)) X))) in H7...
      apply H2 in H7.
      apply subst_tt_collect3 in H7...
      apply subst_tt_collect2 ...
    +
      intros.
      apply Tlookup_subst in H7... 
      apply Tlookup_subst in H8...
      destruct H7 as [t1'].
      destruct H8 as [t2'].
      destruct_hypos. subst.
      eapply H6 with (m:=m) (i:=i)
      (t1:= subst_tt X (typ_label X (open_tt (choose n C (choose r C D)) X)) t1')
      (t2:= subst_tt X (typ_label X (open_tt (choose n D (choose r C D)) X)) t2')...
      {
        eapply lookup_some_subst...
      }
      {
        eapply lookup_some_subst...
      }
      { solve_notin. 
        + rewrite lookup_some_in_fl_tt with (A:=A) (i:=i)...
        + rewrite lookup_some_in_fl_tt with (A:=B) (i:=i)...
      }
Qed.


Lemma unfolding_lemma: forall E A B,
    sub E (typ_mu A) (typ_mu B) ->
    sub E (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof with auto.
  intros.
  assert (Ht:=H).
  dependent destruction H.
  pick fresh X.
  rewrite subst_tt_intro with (X:=X)...
  remember (subst_tt X (typ_mu A) (open_tt A X)) .
  rewrite subst_tt_intro with (X:=X)...
  subst.
  assert (wf_env E) by (get_well_form;auto).
  apply sub_generalize_intensive with (m:=Pos) (n:=Pos) (r:=Pos) (E:=E) (F:=X ~ bind_sub typ_top ++ E)...
  { constructor... }
  { solve_notin. }
  { cbn [choose].
    specialize_x_and_L X L.
    rewrite <- subst_tt_intro...
    rewrite <- subst_tt_intro...
  }
  { inv_rt. }
Qed.
