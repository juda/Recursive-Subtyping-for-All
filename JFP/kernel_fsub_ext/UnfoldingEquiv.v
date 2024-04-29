Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Reverse.


Lemma fl_tt_subst_tt: forall X S T,
 fl_tt T [<=] fl_tt (subst_tt X S T).
Proof with auto.
  induction T;intros;simpl;try apply AtomSetProperties.subset_empty...
  + apply union_s_m...
  + apply union_s_m...
  + apply union_s_m...
  + apply union_s_m... intros x...
  + apply union_s_m...
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
  -
    analyze_binds H.
    apply IHE with (X:=X)...
Qed.


Lemma notin_fl_env_lb: forall E X Y U,
    binds X (bind_sub_lb U) E ->
    Y \notin fl_env E ->
    Y \notin fl_tt U.
Proof with eauto.
  induction E;intros...
  simpl in *.
  destruct a.
  destruct b...
  -
    analyze_binds H.
    apply IHE with (X:=X)...
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
  
  | sub_env_ext_cons_lb_1: forall E1 E2 T Y,
      Y \notin dom E2 ->
      sub_env_ext E X C D E1 E2 ->
      sub_env_ext E X C D
        (Y ~ bind_sub_lb (subst_tt X (typ_label X (open_tt C X)) T) ++ E1)
        (Y ~ bind_sub_lb (subst_tt X (typ_mu C) T) ++ E2)

  | sub_env_ext_cons_lb_2: forall E1 E2 T Y,
      Y \notin dom E2 ->
      sub_env_ext E X C D E1 E2 ->
      sub_env_ext E X C D
        (Y ~ bind_sub_lb (subst_tt X (typ_label X (open_tt D X)) T) ++ E1)
        (Y ~ bind_sub_lb (subst_tt X (typ_mu D) T) ++ E2)
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
  -
    inversion H2;subst...
    { inversion H3;subst. }
    destruct (IHsub_env_ext a U) as [[T' [Hbinds Heq]] | [T' [Hbinds Heq]]]...
    * left. exists T'...
    * right. exists T'...
  -
    inversion H2;subst...
    { inversion H3;subst. }
    destruct (IHsub_env_ext a U) as [[T' [Hbinds Heq]] | [T' [Hbinds Heq]]]...
    * left. exists T'...
    * right. exists T'...
Qed.


Lemma sub_env_ext_sem_lb: forall E X C D F G,
  sub_env_ext E X C D F G ->
  forall a U, 
  a <> X ->
  binds a (bind_sub_lb U) F ->
  (exists T, 
    binds a (bind_sub_lb (subst_tt X (typ_mu C) T)) G /\
    U = subst_tt X (typ_label X (open_tt C X)) T) \/
  (exists T,
    binds a (bind_sub_lb (subst_tt X (typ_mu D) T)) G /\
    U = subst_tt X (typ_label X (open_tt D X)) T).
Proof with auto.
  intros E X C D F G H.
  induction H;intros.
  -
    left.
    exists U.
    inversion H2;subst. { inversion H3;subst... }
    assert (X `notin` fv_tt U).
    { apply notin_fv_tt_fv_env_lb with (E:=E) (Y:=a)...
      rewrite fv_env_ls_dom... }
    rewrite <- subst_tt_fresh...
    rewrite <- subst_tt_fresh...
  -
    inversion H2;subst...
    { inversion H3;subst. }
    destruct (IHsub_env_ext a U) as [[T' [Hbinds Heq]] | [T' [Hbinds Heq]]]...
    * left. exists T'...
    * right. exists T'...
  -
    inversion H2;subst...
    { inversion H3;subst. }
    destruct (IHsub_env_ext a U) as [[T' [Hbinds Heq]] | [T' [Hbinds Heq]]]...
    * left. exists T'...
    * right. exists T'...
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
  - apply sub_env_ext_cons_lb_2...
  - apply sub_env_ext_cons_lb_1...
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
  - destruct IHsub_env_ext as [G' eq]; subst.
    exists ( Y ~ bind_sub_lb (subst_tt X (typ_mu C) T) ++ G')...
  - destruct IHsub_env_ext as [G' eq]; subst.
    exists ( Y ~ bind_sub_lb (subst_tt X (typ_mu D) T) ++ G')...
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
  - destruct IHsub_env_ext as [F' eq]; subst.
    exists ( Y ~ bind_sub_lb (subst_tt X (typ_label X (open_tt C X)) T) ++ F')...
  - destruct IHsub_env_ext as [F' eq]; subst.
    exists ( Y ~ bind_sub_lb (subst_tt X (typ_label X (open_tt D X)) T) ++ F')...
Qed.


(* Lemma subst_tt_single_compatible_rev: forall X C A B,
  Compatible (subst_tt X (typ_single X C) A) (subst_tt X (typ_single X C) B) ->
  Compatible A B.
Proof with auto.
(* Generally not true
   e.g. A = X, B = {l : Y}
   Compat {X : C} {l : Y} -\-> Compat X {l : Y}
   Another reason on why we should distinguish single and label? *)
Qed. *)


Lemma subst_tt_label_compatible_rev: forall X C D A B,
  Compatible (subst_tt X (typ_label X C) A) (subst_tt X (typ_label X D) B) ->
  Compatible A B.
Proof with auto.
  intros. dependent induction H.
  - destruct A; try inversion x1; destruct B; try inversion x.
    + destruct (a==X); inversion H1.
    + destruct (a==X); inversion H1.
    + destruct (a0==X); inversion H3.
    + subst. apply Comp_NE...
  - destruct A; try inversion x.
    + destruct (a==X); inversion H2.
    + apply Comp_L. simpl in x.
      * eapply IHCompatible1. apply H2. auto.
      * eapply IHCompatible2. apply H3. auto.
  - destruct B; try inversion x.
    + destruct (a==X); inversion H2.
    + apply Comp_R. simpl in x.
      * eapply IHCompatible1. 2: apply H2. auto.
      * eapply IHCompatible2. 2: apply H3. auto.


    (* - destruct B; try inversion x.
    + destruct (a==X); inversion H0.
    + destruct A; try inversion x1.
      * apply Comp_TopL.
      * destruct (a0==X); inversion H2.
  - destruct A; try inversion x1.
    + destruct (a==X); inversion H0.
    + destruct B; try inversion x.
      * apply Comp_TopR.
      * destruct (a0==X); inversion H2.
  - destruct A; try inversion x1.
    + destruct (a==X);inversion H2.
    + subst.
      destruct B;try inversion x;subst.
      * destruct (a0 == X);inversion H2.
      * destruct B1;try inversion H2;subst.
        { destruct (a0 == X);inversion H3. }
        { constructor...
          eapply IHCompatible with (X0:=X) (C0:=C) (D0:=D)... }
     destruct B; try inversion x.
    + apply Comp_TopTop.
    + destruct (a==X); inversion H0.
    + destruct (a==X); inversion H0.
    + destruct (a==X); inversion H0. *)
Qed.

Lemma sub_env_ext_WF_subst: forall m E X C D F G A,
  sub_env_ext E X C D F G ->
  WF E (typ_mu (choose m C D)) ->
  WF F (subst_tt X (typ_label X (open_tt (choose m C D) X)) A) ->
  WF G (subst_tt X (typ_mu (choose m C D)) A) .
Proof with auto.
  intros m E X C D F G A Hsub Hwfc Hwf.
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
  -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
  -
    destruct A; try solve [inversion x].
    simpl in *. destruct (a==X);subst;inversion x;subst.
    pose proof (sub_env_ext_sem Hsub _ n H).
    destruct H0 as [[T [Hbinds Heq]]|[T [Hbinds Heq]]];subst.
    { apply (WF_var _ _ _ Hbinds). }
    { apply (WF_var _ _ _ Hbinds). }
  -
    destruct A; try solve [inversion x].
    simpl in *. destruct (a==X);subst;inversion x;subst.
    pose proof (sub_env_ext_sem_lb Hsub _ n H).
    destruct H0 as [[T [Hbinds Heq]]|[T [Hbinds Heq]]];subst.
    { apply (WF_var_lb _ _ _ Hbinds). }
    { apply (WF_var_lb _ _ _ Hbinds). }
  -
    destruct A; try solve [inversion x
    |simpl in *;destruct (a==X);inversion x]...
    simpl in x. inversion x. subst.
    simpl. constructor...
  -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl in x. inversion x. subst.
    pose proof WF_type Hwfc.
    inversion H1;subst. 
    simpl. apply WF_all with (L:=L \u {{X}}\u L0 \u fv_tt C \u dom G)...
    intros. specialize_x_and_L X0 L.
    rewrite subst_tt_open_tt_var...
    { apply H0...
      + rewrite <- subst_tt_open_tt_var...
      + destruct m; constructor...
    }
  -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl in x. inversion x. subst.
    pose proof WF_type Hwfc.
    inversion H1;subst. 
    simpl. apply WF_all_lb with (L:=L \u {{X}}\u L0 \u fv_tt C \u dom G)...
    intros. specialize_x_and_L X0 L.
    rewrite subst_tt_open_tt_var...
    { apply H0...
      + rewrite <- subst_tt_open_tt_var...
      + destruct m; constructor...
    }
  -
    destruct A; try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl in x. inversion x. subst.
    pose proof WF_type Hwfc.
    inversion H3;subst.
    simpl. apply WF_rec with (L:=L \u {{X}}\u L0 \u fv_tt C \u dom G)...
    +
      intros. specialize_x_and_L X0 L.
      rewrite subst_tt_open_tt_var...
      apply H0...
      *
        rewrite <- subst_tt_open_tt_var...
      *
        replace (X0 ~ bind_sub typ_top ++ E0)
            with (X0 ~ bind_sub (subst_tt X (typ_label X (open_tt D X)) typ_top) ++ E0)...
        replace (X0 ~ bind_sub typ_top ++ G)
            with (X0 ~ bind_sub (subst_tt X (typ_mu D) typ_top) ++ G)...
        constructor...
    +
      intros. specialize_x_and_L X0 L.
      rewrite <- subst_tt_open_tt_twice...
      apply H2...
      *
        rewrite  subst_tt_open_tt_twice...
      *
        replace (X0 ~ bind_sub typ_top ++ E0)
            with (X0 ~ bind_sub (subst_tt X (typ_label X (open_tt D X)) typ_top) ++ E0)...
        replace (X0 ~ bind_sub typ_top ++ G)
            with (X0 ~ bind_sub (subst_tt X (typ_mu D) typ_top) ++ G)...
        constructor...
  - 
    destruct A; try solve [inversion x].
    + simpl in *. destruct (a==X);inversion x;subst...
      pose proof sub_env_ext_app Hsub as [G' eq].
      subst. add_nil. apply WF_weakening...
    + simpl in *. destruct (a==X);inversion x;subst...
  -
    destruct A; try solve [inversion x
    |simpl in *;destruct (a==X);inversion x]...
    simpl in x. inversion x. subst.
    simpl. constructor...   
  -
    destruct A; try solve [inversion x
    |simpl in *;destruct (a==X);inversion x]...
    simpl in x. inversion x. subst.
    simpl. constructor... destruct m; subst; simpl in *; apply subst_tt_label_compatible_rev in H...
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
  + fsetdec.
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
      * pose proof (sub_env_ext_sem Henv _ n0 H3).
        destruct H1 as [[T [Hbinds Heq]]|[T [Hbinds Heq]]];subst.
        { apply (WF_var _ _ _ Hbinds). }
        { apply (WF_var _ _ _ Hbinds). }
      * pose proof (sub_env_ext_sem_lb Henv _ n0 H3).
        destruct H1 as [[T [Hbinds Heq]]|[T [Hbinds Heq]]];subst.
        { apply (WF_var_lb _ _ _ Hbinds). }
        { apply (WF_var_lb _ _ _ Hbinds). }
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
  
  -
    (* Bot <: A *)
    (* eapply equiv_env_sub. apply Heqenv. *)
    dependent destruction A;try solve [inversion x
      |simpl in *;destruct (a==X);inversion x]...
    simpl. apply sa_bot...
      destruct m, n, r;get_well_form;simpl in *;
      try solve 
      [apply sub_env_ext_WF_subst with (m:=Pos) (C:=C) (D:=D) (E:=E) (F:=E0);auto|
      apply sub_env_ext_WF_subst with (m:=Neg) (C:=C) (D:=D) (E:=E) (F:=E0);auto]...
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
    destruct n; cbn [choose] in *.
    *
      (* A <: B <: X  unfolding lemma part *)
      destruct B; try solve [inversion x].
      simpl in x. simpl. destruct (a == X);subst;inversion x;subst.

      pose proof sub_env_ext_sem_lb Henv _  n H.

      destruct H0 as [[T [Hbinds Heq]]|[T [Hbinds Heq]]];
      subst U;
      apply (sa_trans_tvar_lb _ _ _ _ Hbinds).
        

      +
        apply IHHsub with (r:=Pos) (n:=Neg) (m:=m) (D:=D)...
        { solve_notin.
          apply notin_fl_env_lb with (Y:= X) in Hbinds...
          rewrite <- fl_tt_subst_tt in Hbinds...
        }
      +
        apply IHHsub with (m:=m) (n:=Pos) (r:=r)...
        { solve_notin. 
          apply notin_fl_env_lb with (Y:= X) in Hbinds...
          rewrite <- fl_tt_subst_tt in Hbinds...
        }
    *
      (* subst lemma part *)
      destruct B; try solve [inversion x].
      simpl in x. simpl. destruct (a == X);subst;inversion x;subst.

      pose proof sub_env_ext_sem_lb Henv _  n H.

      destruct H0 as [[T [Hbinds Heq]]|[T [Hbinds Heq]]];
      subst U;
      apply (sa_trans_tvar_lb _ _ _ _ Hbinds).
      +
        destruct r;simpl.
        {
          apply IHHsub with (m:=m) (n:=Neg) (r:=Pos) (D0:=D)...
          {  solve_notin.
            apply notin_fl_env_lb with (Y:= X) in Hbinds...
            rewrite <- fl_tt_subst_tt in Hbinds...
          }
        }
        {
          apply IHHsub with (m:=flip m) (n:=Pos) (r:=Pos)...
          { apply sub_env_ext_flip... }
          { solve_notin.           
            apply notin_fl_env_lb with (Y:= X) in Hbinds...
            rewrite <- fl_tt_subst_tt in Hbinds...
          }
          { destruct m... }
        }
      +
        destruct r;simpl.
        { apply IHHsub with (m:=m) (n:=Pos) (r:=Pos)...
          { solve_notin.
            apply notin_fl_env_lb with (Y:= X) in Hbinds...
            rewrite <- fl_tt_subst_tt in Hbinds...
          }
        }
        { apply IHHsub with (m:=m) (n:=Neg) (r:=Neg) (C0:=C)...
          { solve_notin.
            apply notin_fl_env_lb with (Y:= X) in Hbinds...
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
        { simpl in Hx. solve_notin. }
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
        { simpl in Hx. solve_notin. }
      +
        apply IHHsub2 with (m:=m) (n:=Neg) (r0:=r)...
        { simpl in Hx. solve_notin. }
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
          destruct m, r;simpl in *; get_well_form... }
        { simpl in Hx. solve_notin. 
          rewrite fl_tt_subst_tt2.
          destruct r... }


  -
    (* all_lb *)
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



      apply sa_all_lb with (L:=L \u {{ X}} \u dom G \u dom E0 \u L1 \u L0 \u fv_tt C \u fv_tt D) ...
      +
        apply IHHsub1 with (m:=m) (n:=Pos) (r:=r)...
        { simpl in Hx. solve_notin. }
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

      apply sa_all_lb with (L:=L \u {{ X}} \u dom G \u dom E0 \u L1 \u L0 \u fv_tt C \u fv_tt D) ...
      +
        apply IHHsub1 with (m:=m) (n:=Neg) (r0:=r)...
        { simpl in Hx. solve_notin. }
      +
        apply IHHsub2 with (m:=m) (n:=Neg) (r0:=r)...
        { simpl in Hx. solve_notin. }
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
          destruct m, r;simpl in *; get_well_form... }
        { simpl in Hx. solve_notin. 
          rewrite fl_tt_subst_tt2.
          destruct r... }


  -
    (* rec *)
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
    (* label *)
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

      inversion Hcd;subst.
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
    (* single *)
    destruct B; try solve [inversion x];
    destruct A; try solve [inversion x0].
    +
      simpl in x. destruct (a == X);subst;inversion x;subst.
    +
      simpl in x. destruct (a == X);subst;inversion x;subst.
    +
      simpl in x0. destruct (a0 == X);subst;inversion x0;subst.
    +
      simpl in *; inversion x0; subst; inversion x; subst.
      constructor. apply IHHsub with (m:=m)...


  -
    (* sa_and_a *)
    destruct A; try solve [inversion x].
    { simpl in x. destruct (a == X);subst;inversion x;subst. }
    inversion x; subst.
    destruct n; cbn [choose] in *.
    *
      simpl. apply sa_and_a.
      +
        assert (WF E (typ_mu C)) by (get_well_form; destruct m; auto).
        pose proof (sub_env_ext_WF_subst Pos) as WF_aux; simpl in WF_aux.
        apply WF_aux with (E:=E) (D:=D) (F:=E0)...
      +
        apply IHHsub with (m:= m) (n:=Pos) (r:=r)...
        { simpl in Hx. solve_notin. }
      +
        apply subst_tt_label_compatible_rev in H0...
    *
      simpl. apply sa_and_a.
      +
        assert (WF E (typ_mu C)) by (get_well_form; destruct m; auto).
        assert (WF E (typ_mu D)) by (get_well_form; destruct m; auto).
        apply sub_env_ext_WF_subst with (E:=E) (F:=E0)...
        destruct r...
      +
        apply IHHsub with (m:= m) (n:=Neg)...
        { simpl in Hx. solve_notin. }
      +
        apply subst_tt_label_compatible_rev in H0...

  -
    (* sa_and_b *)
    destruct A; try solve [inversion x].
    { simpl in x. destruct (a == X);subst;inversion x;subst. }
    inversion x; subst.
    destruct n; cbn [choose] in *.
    *
      simpl. apply sa_and_b.
      +
        assert (WF E (typ_mu C)) by (get_well_form; destruct m; auto).
        pose proof (sub_env_ext_WF_subst Pos) as WF_aux; simpl in WF_aux.
        apply WF_aux with (E:=E) (D:=D) (F:=E0)...
      +
        apply IHHsub with (m:= m) (n:=Pos) (r:=r)...
        { simpl in Hx. solve_notin. }
      +
        apply subst_tt_label_compatible_rev in H0...
    *
      simpl. apply sa_and_b.
      +
        assert (WF E (typ_mu C)) by (get_well_form; destruct m; auto).
        assert (WF E (typ_mu D)) by (get_well_form; destruct m; auto).
        apply sub_env_ext_WF_subst with (E:=E) (F:=E0)...
        destruct r...
      +
        apply IHHsub with (m:= m) (n:=Neg)...
        { simpl in Hx. solve_notin. }
      +
        apply subst_tt_label_compatible_rev in H0...

  -
    (* sa_and_both *)
    destruct B; try solve [inversion x].
    { simpl in x. destruct (a == X);subst;inversion x;subst. }
    inversion x; subst.
    destruct n; cbn [choose] in *.
    *
      simpl. apply sa_and_both.
      +
        apply IHHsub1 with (m:= m) (n:=Pos) (r:=r)...
        { simpl in Hx. solve_notin. }
      +
        apply IHHsub2 with (m:= m) (n:=Pos) (r:=r)...
        { simpl in Hx. solve_notin. }
      +
        apply subst_tt_label_compatible_rev in H...
    *
      simpl. apply sa_and_both.
      +
        apply IHHsub1 with (m:= m) (n:=Neg)...
        { simpl in Hx. solve_notin. }
      +
        apply IHHsub2 with (m:= m) (n:=Neg)...
        { simpl in Hx. solve_notin. }
      +
        apply subst_tt_label_compatible_rev in H...
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
Qed.
