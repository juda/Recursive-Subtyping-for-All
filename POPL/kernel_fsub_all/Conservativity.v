Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Fsub.
Require Export Coq.micromega.Lia.


Hint Constructors Algo.typing.



Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : typ => fl_tt x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : env => fv_env x) in
  let H := gather_atoms_with (fun x : env => fl_env x) in
  let A1 := gather_atoms_with (fun x : exp => fv_te x) in
  let A2 := gather_atoms_with (fun x : exp => fv_ee x) in
  let A3 := gather_atoms_with (fun x : list (var * nat) => dom x) in
  let CF := gather_atoms_with (fun x : list (var * Fsub.typ) => dom x) in
  let DF := gather_atoms_with (fun x : Fsub.typ => Fsub.fl_tt x) in
  let EF := gather_atoms_with (fun x : Fsub.typ => Fsub.fv_tt x) in
  let FF := gather_atoms_with (fun x : Fsub.env => dom x) in
  let GF := gather_atoms_with (fun x : Fsub.env => Fsub.fv_env x) in
  let HF := gather_atoms_with (fun x : Fsub.env => Fsub.fl_env x) in
  let A1F := gather_atoms_with (fun x : Fsub.exp => Fsub.fv_te x) in
  let A2F := gather_atoms_with (fun x : Fsub.exp => Fsub.fv_ee x) in
  let A3F := gather_atoms_with (fun x : list (var * nat) => dom x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u A1 \u A2 \u A3
  \u CF \u DF \u EF \u FF \u GF \u HF \u A1F \u A2F \u A3F).


Coercion Fsub.typ_bvar : nat >-> Fsub.typ.
Coercion Fsub.typ_fvar : atom >-> Fsub.typ.


Module ExtDefs.


Inductive typ_ext : Fsub.typ -> typ -> Prop :=
| typ_ext_nat : typ_ext Fsub.typ_nat typ_nat
| typ_ext_top : typ_ext Fsub.typ_top typ_top
| typ_ext_bvar : forall (n : nat),
    typ_ext (Fsub.typ_bvar n) (typ_bvar n)
| typ_ext_fvar : forall (x : atom),
    typ_ext (Fsub.typ_fvar x) (typ_fvar x)
| typ_ext_arrow : forall (T1 T2 : Fsub.typ) T1' T2',
    typ_ext T1 T1' -> typ_ext T2 T2' -> 
    typ_ext (Fsub.typ_arrow T1 T2) (typ_arrow T1' T2')
| typ_ext_all : forall (T1 T2 : Fsub.typ) T1' T2',
    typ_ext T1 T1' -> typ_ext T2 T2' -> 
    typ_ext (Fsub.typ_all T1 T2) (typ_all T1' T2')
.

Inductive exp_ext : Fsub.exp -> exp -> Prop :=
| exp_ext_nat : 
    exp_ext Fsub.exp_nat exp_nat
| exp_ext_bvar : forall i, 
    exp_ext (Fsub.exp_bvar i) (exp_bvar i)
| exp_ext_fvar : forall x, 
    exp_ext (Fsub.exp_fvar x) (exp_fvar x)
| exp_ext_abs : forall T T' e e',
    typ_ext T T' ->
    exp_ext e e' ->
    exp_ext (Fsub.exp_abs T e) (exp_abs T' e')
| exp_ext_app : forall e1 e2 e1' e2',
    exp_ext e1 e1' ->
    exp_ext e2 e2' ->
    exp_ext (Fsub.exp_app e1 e2) (exp_app e1' e2')
| exp_ext_tabs : forall T T' e e',
    typ_ext T T' ->
    exp_ext e e' ->
    exp_ext (Fsub.exp_tabs T e) (exp_tabs T' e')
| exp_ext_tapp : forall T T' e  e',
    exp_ext e e' ->
    typ_ext T T' ->
    exp_ext (Fsub.exp_tapp e T) (exp_tapp e' T')
.

Inductive binding_ext : Fsub.binding -> binding -> Prop :=
| binding_sub_ext: forall T T',
    typ_ext T T' ->
    binding_ext (Fsub.bind_sub T) (bind_sub T')
| binding_typ_ext: forall T T',
    typ_ext T T' ->
    binding_ext (Fsub.bind_typ T) (bind_typ T')
.

Inductive env_ext: Fsub.env -> env -> Prop :=
| env_ext_empty : env_ext nil nil
| env_ext_cons : forall (x : atom) b b' E E',
    env_ext E E' ->
    binding_ext b b' ->
    env_ext ((x, b) :: E) ((x, b') :: E').


Hint Constructors typ_ext exp_ext binding_ext env_ext.


Ltac inv_rt :=
  (* try (solve
   [ repeat match goal with
	        | H:rt_type ?T |- _ => inversion H; clear H
            end ]). *)
    (* try solve [exfalso;eapply bind_sub_conserv_lb;eauto]; *)
            idtac.

Ltac inv H := inversion H; subst;inv_rt.

Lemma typ_ext_inj1: forall { T T1' T2' },
  typ_ext T T1' -> typ_ext T T2' ->
  T1' = T2'.
Proof with auto.
  intros T. induction T;intros T1' T2' E1 E2;
  try solve [inv E1; inv E2; inv_rt; auto];inv_rt.
  - inv E1;inv_rt. inv E2;inv_rt...
    rewrite (IHT1 T1'0 T1')...
    rewrite (IHT2 T2'0 T2'1)...
  - inv E1. inv E2...
    rewrite (IHT1 T1'0 T1')...
    rewrite (IHT2 T2'0 T2'1)...
Qed.

Lemma typ_ext_inj2: forall { T' T1 T2 }, 
  typ_ext T1 T' -> typ_ext T2 T' ->
  T1 = T2.
Proof with auto.
  intros T. induction T;intros T1' T2' E1 E2;
  try solve [inv E1; inv E2; auto].
  - inv E1. inv E2...
    rewrite (IHT1 T0 T4)...
    rewrite (IHT2 T3 T5)...
  - inv E1. inv E2...
    rewrite (IHT1 T0 T4)...
    rewrite (IHT2 T3 T5)...
  Qed.

Lemma typ_ext_ex: forall T ,
  exists T', typ_ext T T'.
Proof with auto.
  intros T. induction T;
  try solve [eexists; constructor; auto]...
  - destruct IHT1. destruct IHT2.
    exists (typ_arrow x x0)...
  - destruct IHT1. destruct IHT2.
    exists (typ_all x x0)...
Qed.


End ExtDefs.



Theorem bind_sub_conserv_lb: forall E E' X U,
ExtDefs.env_ext E E' ->
binds X (bind_sub_lb U) E' ->
False.
Proof with auto.
  intros.
  induction H.
  - inv H0.
  - inv H0.
    + inv H2. inv H1.
    + apply IHenv_ext in H2. destruct H2.
Qed. 


Ltac inv_rt :=
  (* try (solve
   [ repeat match goal with
	        | H:rt_type ?T |- _ => inversion H; clear H
            end ]). *)
    try solve [exfalso;eapply bind_sub_conserv_lb;eauto];
            idtac.

Ltac inv H := inversion H; subst;inv_rt.


Lemma env_ext_dom : forall { E E' },
  ExtDefs.env_ext E E' -> dom E = dom E'.
Proof with auto.
  intros.
  induction H...
  simpl. rewrite IHenv_ext...
Qed.




Theorem bind_sub_conserv: forall E E' X U,
ExtDefs.env_ext E E' ->
binds X (Fsub.bind_sub U) E ->
exists U', binds X (bind_sub U') E' /\ 
    ExtDefs.typ_ext U U'.
Proof with auto.
  intros.
  induction H.
  - inv H0.
  - inv H0.
    + inv H2. inv H1.
      exists T'. split...
    + apply IHenv_ext in H2. destruct H2 as [U' [? ?]].
      exists U'...
Qed. 

Theorem bind_typ_conserv: forall E E' X U,
ExtDefs.env_ext E E' ->
binds X (Fsub.bind_typ U) E ->
exists U', binds X (bind_typ U') E' /\ 
    ExtDefs.typ_ext U U'.
Proof with auto.
  intros.
  induction H.
  - inv H0.
  - inv H0.
    + inv H2. inv H1.
      exists T'. split...
    + apply IHenv_ext in H2. destruct H2 as [U' [? ?]].
      exists U'...
Qed. 

Lemma open_tt_conserv: forall T T' U U',
ExtDefs.typ_ext T T' ->
ExtDefs.typ_ext U U' -> forall n,
ExtDefs.typ_ext (Fsub.open_tt_rec n U T) (open_tt_rec n U' T').
Proof with auto.
  intros. unfold open_tt.
  unfold Fsub.open_tt.  revert n.
  induction H...
  - intros. simpl. destruct (n0==n)...
  - intros. simpl...
  - intros. simpl... 
  - intros. simpl... 
Qed.

Lemma open_close_tt_conserv_rec: forall T T' (X:atom) n,
X \notin fv_tt T ->
ExtDefs.typ_ext T' (open_tt_rec n X T) ->
ExtDefs.typ_ext (Fsub.close_tt_rec n X T') T.
Proof with auto.
  induction T; induction T'; intros; try solve [inv H0];simpl...
  - simpl in H0. destruct (n0 == n)... inv H0.
  - simpl in H0. destruct (n0 == n)... inv H0.
  - simpl in H0. destruct (n1 == n)... inv H0.
  - simpl in H0. destruct (n0 == n)...
    + inv H0. destruct (X == X)... exfalso...
    + inv H0.
  - simpl in H0. destruct (n0 == n)... inv H0.
    inv H0.
  - simpl in H0. destruct (n0 == n)... inv H0.
    inv H0.
  - simpl in H0. destruct (a0 == X)... subst. inv H0.
    simpl in H. exfalso...
  - simpl in H0, H. inv H0...
  - simpl in H0, H. inv H0...
Qed.

Lemma open_close_tt_conserv: forall T T' (X:atom),
X \notin fv_tt T ->
ExtDefs.typ_ext T' (open_tt T X) ->
ExtDefs.typ_ext (Fsub.close_tt T' X) T.
Proof with auto.
  intros.
  apply open_close_tt_conserv_rec...
Qed.



Lemma open_ee_conserv: forall e e' u u',
ExtDefs.exp_ext e e' ->
ExtDefs.exp_ext u u' ->
ExtDefs.exp_ext (Fsub.open_ee e u) (open_ee e' u').
Proof with auto.
  intros. unfold open_ee.
  unfold Fsub.open_ee. generalize 0.
  induction H...
  - intros. simpl. destruct (n==i)...
  - intros. simpl...
  - intros. simpl... 
  - intros. simpl...
  - intros. simpl...
  - intros. simpl...
Qed. 


Lemma open_te_conserv: forall e e' u u',
ExtDefs.exp_ext e e' ->
ExtDefs.typ_ext u u' ->
ExtDefs.exp_ext (Fsub.open_te e u) (open_te e' u').
Proof with auto.
  intros. unfold open_te.
  unfold Fsub.open_te. generalize 0.
  induction H;try solve[intros;simpl;auto]...
  - simpl. intros. constructor...
    apply open_tt_conserv...
  - simpl. intros. constructor...
    apply open_tt_conserv...
  - simpl. intros. constructor...
    apply open_tt_conserv...
Qed.

Module Fsub2Ext.
(* T |- e : A -> T |-ext e : A  *)

Theorem wf_conserv:
forall E T,
Fsub.WF E T -> 
forall  E' T', 
ExtDefs.env_ext E E' ->
ExtDefs.typ_ext T T' ->
WF E' T'.
Proof with auto.
  intros E T H0.
  induction H0;intros. 
  - inversion H0...
  - inversion H0...
  - inversion H1;subst...
    eapply bind_sub_conserv in H;eauto.
    destruct H as [U' [? ?]]...
    apply WF_var with (U:=U')...
  - inv H0...
  - inv H3... apply WF_all with (L:=L)...
    intros. specialize_x_and_L X L.
    apply H1...
    { constructor... }
    { apply open_tt_conserv... }
Qed.


Theorem wf_env_conserv:
forall E E', 
ExtDefs.env_ext E E' ->
Fsub.wf_env E -> wf_env E'.
Proof with auto.
  intros. generalize dependent E'.
  induction H0;intros. 
  - inversion H;subst...
  - inversion H2;subst.
    inversion H8;subst.
    rewrite_env ([(X, bind_sub T')] ++ E'0).
    constructor...
    { eapply wf_conserv;eassumption. }
    { rewrite <- (env_ext_dom H7)... }
  - inv H2. inv H8.
    rewrite_env ([(x, bind_typ T')] ++ E'0).
    constructor...
    { eapply wf_conserv;eassumption. }
    { rewrite <- (env_ext_dom H7)... }
Qed.

Theorem sub_conserv:
forall E E' T1 T2 T1' T2',
ExtDefs.env_ext E E' ->
ExtDefs.typ_ext T1 T1' ->
ExtDefs.typ_ext T2 T2' ->
Fsub.sub E T1 T2 -> sub E' T1' T2'.
Proof with auto.
  intros.
  generalize dependent E'.
  generalize dependent T1'.
  generalize dependent T2'.
  induction H2;intros.
  - inv H1. inv H0... 
    apply sa_nat. 
    eapply wf_env_conserv;eassumption...
  - inv H1. inv H2... 
    apply sa_fvar. 
    eapply wf_env_conserv;eassumption...
    eapply wf_conserv;eassumption...
  - inv H1.
    apply sa_top.
    eapply wf_env_conserv;eassumption...
    eapply wf_conserv;eassumption...
  - inv H0...
    eapply bind_sub_conserv in H;try eassumption...
    destruct H as [? [? ?]].
    eapply sa_trans_tvar...
    { apply H... }
    { apply IHsub... }
  - inv H1... inv H0...
  - 
    assert (Hwfe: Fsub.wf_env E).
    { pick_fresh X. specialize_x_and_L X L.
      apply Fsub.sub_regular in H0.
      destruct_hypos... inv H0... }
    inv H2... inv H3...
    rewrite (ExtDefs.typ_ext_inj1 H7 H8) in *...
    apply sa_all with (L:=L)...
    { apply Reflexivity... 
      eapply wf_conserv;eassumption.
      eapply wf_env_conserv;eassumption. }
    { apply Reflexivity... 
      eapply wf_conserv;eassumption.
      eapply wf_env_conserv;eassumption. }
    { intros. specialize_x_and_L x L.
      apply H1...
      { apply open_tt_conserv... }
      { apply open_tt_conserv... }
      { constructor... }
    }
Qed.


Theorem typing_conserv:
forall E E' e e' t t', 
ExtDefs.env_ext E E' ->
ExtDefs.exp_ext e e' ->
ExtDefs.typ_ext t t' ->
Fsub.typing E e t -> typing E' e' t'.
Proof with auto.
  intros. 
  generalize dependent E'.
  generalize dependent e'.
  generalize dependent t'.
  induction H2;intros.
  - inv H0. inv H1.
    apply typing_nat.
    eapply wf_env_conserv;eassumption...
  - inv H2.
    apply typing_var.
    { eapply wf_env_conserv;eassumption... }
    { eapply bind_typ_conserv in H3;eauto.
      destruct H3 as [U' [? ?]]...
      rewrite (ExtDefs.typ_ext_inj1 H1 H4)... }
  - inv H2. inv H1.
    rewrite (ExtDefs.typ_ext_inj1 H6 H7) in *...
    apply typing_abs with (L:=L).
    intros. specialize_x_and_L x L.
    apply H0...
    { apply open_ee_conserv... }
    { constructor... }
  - inv H0.
  (* TODO: MIGHT TROUBLESOME in the reverse direction *)
    destruct (ExtDefs.typ_ext_ex T1).
    apply typing_app with (T1:=x)...
  - inv H1. inv H2.
    rewrite (ExtDefs.typ_ext_inj1 H6 H7) in *...
    apply typing_tabs with (L:=L).
    intros. specialize_x_and_L x L.
    apply H0...
    { apply open_tt_conserv... }
    { apply open_te_conserv... }
    { constructor... }
  - inv H0.
    destruct (ExtDefs.typ_ext_ex T2) as [T2' ?].
    pose proof open_tt_conserv H4 H8 0.
    rewrite (ExtDefs.typ_ext_inj1 H1 H5) in *.
    destruct (ExtDefs.typ_ext_ex T1) as [T1' ?].
    apply typing_tapp with (T1:=T1')...
    { eapply sub_conserv;try eassumption... }
  - destruct (ExtDefs.typ_ext_ex S) as [S' ?].
    apply typing_sub with (S:=S')...
    eapply sub_conserv;try eassumption...
Qed.


End Fsub2Ext.

Module Ext2Fsub.

(* T |-ext e : A -> Fsub e -> Fsub A -> Fsub T -> T |- e : A  *)

Theorem bind_sub_conserv: forall E E' X U,
ExtDefs.env_ext E E' ->
binds X (bind_sub U) E' ->
exists U', binds X (Fsub.bind_sub U') E /\ 
    ExtDefs.typ_ext U' U.
Proof with auto.
  intros.
  induction H.
  - inv H0.
  - inv H0.
    + inv H2. inv H1.
      exists T. split...
    + apply IHenv_ext in H2. destruct H2 as [U' [? ?]].
      exists U'...
Qed. 

Theorem bind_typ_conserv: forall E E' X U,
ExtDefs.env_ext E E' ->
binds X (bind_typ U) E' ->
exists U', binds X (Fsub.bind_typ U') E /\ 
    ExtDefs.typ_ext U' U.
Proof with auto.
  intros.
  induction H.
  - inv H0.
  - inv H0.
    + inv H2. inv H1.
      exists T. split...
    + apply IHenv_ext in H2. destruct H2 as [U' [? ?]].
      exists U'...
Qed. 


Theorem wf_conserv:
forall E' T',
WF E' T' -> 
forall  E T, 
ExtDefs.env_ext E E' ->
ExtDefs.typ_ext T T' ->
Fsub.WF E T.
Proof with auto.
  intros E' T' H0.
  induction H0;intros. 
  - inversion H0...
  - inversion H0...
  - inversion H0... 
  - inversion H1;subst...
    eapply bind_sub_conserv in H;eauto.
    destruct H as [U' [? ?]]...
    apply Fsub.WF_var with (U:=U')...
  - exfalso. eapply bind_sub_conserv_lb;eassumption.
  - inv H0...
  - inv H3... apply Fsub.WF_all with (L:=L)...
    intros. specialize_x_and_L X L.
    apply H1...
    { constructor... }
    { apply open_tt_conserv... }
  - inv H3.
  - inv H4.
  - inv H1.
  (* - inv H0.
  - inv H2. *)
Qed.


Theorem wf_env_conserv:
forall E E', 
ExtDefs.env_ext E E' ->
wf_env E' -> Fsub.wf_env E.
Proof with auto.
  intros. generalize dependent E.
  induction H0;intros. 
  - inversion H;subst...
  - inversion H2;subst.
    inversion H8;subst.
    rewrite_env ([(X, Fsub.bind_sub T0)] ++ E1).
    constructor...
    { eapply wf_conserv;eassumption. }
    { rewrite  (env_ext_dom H6)... }
  - inv H2. inv H8.
  - inv H2. inv H8.
    rewrite_env ([(x, Fsub.bind_typ T0)] ++ E1).
    constructor...
    { eapply wf_conserv;eassumption. }
    { rewrite (env_ext_dom H6)... }
Qed.

Lemma sub_bot_ex: forall E (X:atom),
  sub E X typ_bot ->
  exists X', binds X' (bind_sub typ_bot) E.
Proof.
  intros. dependent induction H...
  inversion H0;subst.
  + exists X. auto.
  + apply IHsub with (X:=X0);auto.
Qed.


Theorem sub_antisym:
  forall E S1 S2,
  WF E S1 -> WF E S2 ->
  sub E S1 S2 ->
  sub E S2 S1 ->
  forall E' S1' S2',
  ExtDefs.env_ext E' E ->
  ExtDefs.typ_ext S1' S1 ->
  ExtDefs.typ_ext S2' S2 ->
  S1' = S2'.
Proof with auto.
  intros E S1 S2 Hwf1 Hwf2.
  generalize dependent S2.
  dependent induction Hwf1;intros...
  -
    inv H2...
    dependent destruction H;inv_rt...
    { inv H4... }
  -
    inv H2...
  -
    dependent induction H;try solve [inversion H1;inv_rt|inversion H2;inv_rt]...
    inv H2. inv H3...
  -
    dependent induction H1;try solve [inversion H2;inv_rt|
    inversion H3;inv_rt|
    inversion H4;inv_rt|inversion H5;inv_rt|
    inversion H6;inv_rt]...
    { inv H4. inv H5... }
    inv H4.
    destruct (X==X0);subst... { inv H5... }
    assert (Ht:=H).
    apply binds_split in Ht.
    destruct_hypos.
    rename x into E1.
    rename x0 into E2.
    rewrite H6 in H0.

    apply suba_sub_tvar_chain in H0. destruct H0 as [[W1 H0]|H0].
    + assert (sub E X0 X). { apply sa_trans_tvar with (U:=U0)... }
      rewrite H6 in H7.
      apply suba_sub_tvar_chain in H7. 
      destruct H7 as [[W2 H7]|H7].
      { pose proof sub_tvar_chain_antisym H0 H7.
        inv H5... }
      { destruct H7 as [?|[?|[?|?]]].
        * destruct H7. inv H7.
          simpl in *. rewrite <- H8 in *.
          assert (binds X (bind_sub_lb X2) 
            (E0 ++ (X, bind_sub_lb X2) :: E3))...
          inv_rt.
        * destruct H7 as [? [? [? ?]]]. rewrite H6 in *. inv_rt.
        * inv H7.
        * subst E. apply sub_bot_ex in H7. destruct_hypos.
          apply bind_sub_conserv with (E:=E') in H6...
          destruct_hypos. inv H7.
       }
    + destruct H0 as [?|[?|[?|?]]].
      * destruct H0. inv H0.
        simpl in *. rewrite <- H7 in *.
        assert (binds X (bind_sub_lb X2) 
          (E0 ++ (X, bind_sub_lb X2) :: E3))...
        inv_rt.
      * destruct H0 as [? [? [? ?]]]. rewrite H6 in *. inv_rt.
      * inv H0.
      * subst E. apply sub_bot_ex in H0. destruct_hypos.
        apply bind_sub_conserv with (E:=E') in H0...
        destruct_hypos. inv H6.
  -
    inv_rt.
  -
    dependent induction H;try solve [inversion H2;inv_rt|
    inversion H3;inv_rt|
    inversion H4;inv_rt|inversion H5;inv_rt|
    inversion H6;inv_rt]... { inv H1;inv_rt. }
    inv H3. inv H4.
    dependent destruction Hwf2.
    dependent destruction H1;inv_rt.
    rewrite IHHwf1_1 with (S2:=B1) (S2':=T0) (E':=E')(S1':=T1)...
    rewrite IHHwf1_2 with (S2:=B2) (S2':=T3) (E':=E')(S1':=T2)...
  -
    dependent induction H1;try solve [
      inversion H1;inv_rt|
      inversion H2;inv_rt|
    inversion H3;inv_rt|
    inversion H4;inv_rt|inversion H5;inv_rt|
    inversion H6;inv_rt]...
    dependent destruction Hwf2.
    dependent destruction H4;inv_rt...
    inv H6. inv H7.
    f_equal...
    + pick fresh X.
      specialize_x_and_L X L1.
      specialize_x_and_L X L2.
      apply IHHwf1 with (E':=E') (S2:=S2)...
    + pick fresh X.
      specialize_x_and_L X L0.
      specialize_x_and_L X L1.
      specialize_x_and_L X L2.
      apply Fsub.open_tt_var_rev with (X:=X)...
      eapply H0 with (X:=X) (E':=X~Fsub.bind_sub T0 ++E') (S2:=open_tt T3 X)...
      * get_well_form...
      * add_nil. apply sub_narrowing with (Q:=S2)...
      * constructor...
      * apply open_tt_conserv...
      * apply open_tt_conserv...
  -
    inv H4. 
  -
    inv H6.
  -
    inv H2.
  (* -
    inv H2.
  -
    inv H4. *)
Qed.


Theorem sub_conserv:
forall E E' T1 T2 T1' T2',
ExtDefs.env_ext E E' ->
ExtDefs.typ_ext T1 T1' ->
ExtDefs.typ_ext T2 T2' ->
sub E' T1' T2' -> Fsub.sub E T1 T2.
Proof with auto.
  intros.
  generalize dependent E.
  generalize dependent T1.
  generalize dependent T2.
  induction H2;intros.
  - inv H1. inv H0... 
    apply Fsub.sa_nat. 
    eapply wf_env_conserv;eassumption...
  - inv H1. inv H2... 
    apply Fsub.sa_fvar. 
    eapply wf_env_conserv;eassumption...
    eapply wf_conserv;eassumption...
  - inv H1.
    apply Fsub.sa_top.
    eapply wf_env_conserv;eassumption...
    eapply wf_conserv;eassumption...
  - inv H2.
  - inv H0...
    eapply bind_sub_conserv in H;try eassumption...
    destruct H as [? [? ?]].
    eapply Fsub.sa_trans_tvar...
    { apply H... }
    { apply IHsub... }
  - inv_rt.
  - inv H1... inv H0...
  - inv H2... inv H1...
    assert (T4 = T3).
    { eapply sub_antisym;[..|apply H3|apply H7|apply H9]...
      get_well_form... get_well_form... }
    subst.
    (* rewrite (ExtDefs.typ_ext_inj2 H8 H10) in *... *)
    apply Fsub.sa_all with (L:=L)...
    { get_well_form.
      eapply wf_conserv;eassumption... }
    { intros. specialize_x_and_L x L.
      apply H0...
      { apply open_tt_conserv... }
      { apply open_tt_conserv... }
      { constructor... }
    }
  - inv H1...
  - inv H3...
  - inv H0...
  (* - destruct H0;inv H8. *)
Qed.


Lemma typ_ext_env_ex:
forall E E' X  T',
  ExtDefs.env_ext E E' ->
  binds X (bind_sub T') E' ->
  exists T, binds X (Fsub.bind_sub T) E /\ ExtDefs.typ_ext T T'.
Proof with auto.
  intros. induction H.
  - inv H0.
  - inv H0.
    + inv H2. inv H1. exists T. split...
    + destruct IHenv_ext as [T [? ?]]...
      exists T. split...
Qed.


Lemma exposure_ext_ex2:
forall E E' t t' s',
  ExtDefs.env_ext E E' ->
  ExtDefs.typ_ext t t' ->
  Algo.exposure E' t' s' ->
  exists s, ExtDefs.typ_ext s s'.
Proof with auto.
  intros. generalize dependent E.
  generalize dependent t.
  induction H1;intros.
  - exists Fsub.typ_nat...
  - exists Fsub.typ_top...
  - inv H0.
  - inv H0. destruct (typ_ext_env_ex _ _ H2 H) as [U' ?].
    destruct_hypos. 
    destruct IHexposure with (t:=U') (E0:=E0)...
    exists x...
  - inv_rt.
  - inv H0... exists (Fsub.typ_arrow T1 T2)...
  - inv H0. exists (Fsub.typ_all T1 T2)...
  - inv H0.
  - inv H0.
  - inv H0.
  (* - inv H.
    + inv H0.
    + inv H0. *)
Qed.

Lemma exposure_lb_false_ext: forall E T' T T11 T12 E0,
  Algo.exposure E T (typ_all_lb T11 T12) ->
  ExtDefs.typ_ext T' T ->
  ExtDefs.env_ext E0 E ->
  False.
Proof with auto.
  intros. generalize dependent T'. dependent induction H;intros...
  - pose proof bind_sub_conserv _ _ H1 H.
    destruct_hypos.
    apply (IHexposure T11 T12) with (T':=x)...
  - inv H0. 
Qed.


Lemma typ_ext_ex2:
forall E E' e e' t',
  ExtDefs.env_ext E E' ->
  ExtDefs.exp_ext e e' ->
  Algo.typing E' e' t' ->
  exists t, Fsub.typing E e t /\ ExtDefs.typ_ext t t'.
Proof with auto.
  intros.
  generalize dependent E.
  generalize dependent e.
  dependent induction H1;intros.
  - inv H0... exists Fsub.typ_nat. split...
    constructor. 
    eapply wf_env_conserv;eassumption.
  - inv H1. eapply bind_typ_conserv in H0.
    2:{ apply H2. } destruct H0 as [? [? ?]].
    exists x0... split...
    constructor...
    eapply wf_env_conserv;eassumption.
  - inv H1. 
    pick_fresh X.
    specialize_x_and_L X L.
    destruct H0 with (e:= Fsub.open_ee e0 (Fsub.exp_fvar X))
    (E0 := X ~ Fsub.bind_typ T ++ E0) as [T1' [? ?]]...
    { apply open_ee_conserv... }
    { constructor... }
    { exists (Fsub.typ_arrow T T1'). split...
      + apply Fsub.typing_abs with (L:={{X}} \u (union L
      (union (Fsub.fl_tt T)
         (union (Fsub.fv_tt T)
            (union (dom E0)
               (union (Fsub.fv_env E0)
                  (union (Fsub.fl_env E0)
                     (union (Fsub.fv_te e0) (Fsub.fv_ee e0))))))))).
        intros.
        rewrite_env (nil ++ X ~ Fsub.bind_typ T ++ E0) in H3.
        rewrite Fsub.subst_ee_intro with (x:=X)...
        apply Fsub.typing_replacing with (Y:=x) in H3...
        { apply Algo.typing_regular in H. destruct_hypos.
          inv H. constructor...
          eapply wf_env_conserv; eassumption.
          eapply wf_conserv;eassumption.
        }
    }
  - inv H1.
    destruct IHtyping1 with (e:=e0) (E0:=E0) as [T1' [? ?]]...
    destruct IHtyping2 with (e:=e3) (E0:=E0) as [T2' [? ?]]...
    pose proof (Algo.typing_regular H1_). destruct_hypos.
    destruct (exposure_ext_ex2 H2 H4 H) as [Tarr' ?].
    inv H12. 
    apply Algo.exposure_sound in H...
    pose proof sub_conserv H2 H4 H12 H.
    exists T3.
    split...
    + apply Fsub.typing_app with (T1:=T0)...
      { eapply Fsub.typing_sub with (S:=T1')... }
      { apply Fsub.typing_sub with (S:=T2')...
        pose proof sub_conserv H2 H8 H16 H0... }
  - pose proof (Algo.typing_regular H1_). destruct_hypos.
    apply Algo.exposure_sound in H...
    inversion H;subst.
    + inv H0.
      destruct (IHtyping1) with (e:=e0) (E0:=E0)...
      destruct_hypos. inv H8.
    + apply sub_bot_ex in H. destruct H.
      apply bind_sub_conserv with (E:=E0) in H...
      destruct_hypos. inv H7.
  - inv H1.
    pick_fresh X.
    specialize_x_and_L X L.
    destruct H0 with (e:= Fsub.open_te e0 (Fsub.typ_fvar X))
    (E0 := X ~ Fsub.bind_sub T ++ E0) as [T1' [? ?]]...
    { apply open_te_conserv... }
    { constructor... }
    { exists (Fsub.typ_all T (Fsub.close_tt T1' X)). split...
      + apply Fsub.typing_tabs with (L:={{X}} \u (union L
      (union (Fsub.fl_tt T)
         (union (Fsub.fv_tt T)
            (union (dom E0)
               (union (Fsub.fv_env E0)
                  (union (Fsub.fl_env E0)
                     (union (Fsub.fv_te e0) (Fsub.fv_ee e0))))))))\u Fsub.fv_tt T1').
        intros.
        rewrite_env (nil ++ X ~ Fsub.bind_sub T ++ E0) in H3.
        rewrite Fsub.subst_te_intro with (X:=X)...
        apply Fsub.typing_replacing2 with (Y:=X0) in H3...
        2:{ apply Algo.typing_regular in H. destruct_hypos.
          inv H. constructor...
          eapply wf_env_conserv; eassumption.
          eapply wf_conserv;eassumption.
        }
        { rewrite <- Fsub.open_close_reverse...
          { apply Fsub.typing_regular in H3. destruct_hypos.
            apply Fsub.WF_type in H9.
            rewrite Fsub.subst_tt_twice with (X:=X0) (Y:=X)...
            apply Fsub.subst_tt_type...
          }
        }
      + constructor...
        apply open_close_tt_conserv...
    }
  - inv H1.
  - inv H2.
    destruct IHtyping with (e:=e0) (E0:=E0) as [Tall' [? ?]]...
    destruct (exposure_ext_ex2 H3 H5 H) as [Tall'' ?].
    inv H6.
    exists (Fsub.open_tt T3 T). split...
    2:{ eapply open_tt_conserv... }
    apply Fsub.typing_tapp with (T1:=T0)...
    { apply Fsub.typing_sub with (S:=Tall')... 
      pose proof (Algo.typing_regular H1). destruct_hypos.
      apply Algo.exposure_sound in H...
      eapply sub_conserv;[..|apply H]...
    }
    { eapply sub_conserv;[..|apply H0]... }
  - exfalso.
    inv H2. 
    destruct IHtyping with (e:=e0) (E0:=E0) as [Tall' [? ?]]...
    eapply exposure_lb_false_ext;eauto.
  - pose proof (Algo.typing_regular H1). destruct_hypos.
    apply Algo.exposure_sound in H...
    inversion H;subst.
    + inv H2. destruct (IHtyping) with (e:=e0) (E0:=E0)...
      destruct_hypos. inv H10.
    + apply sub_bot_ex in H. destruct H.
      apply bind_sub_conserv with (E:=E0) in H...
      destruct_hypos. inv H9.
  - inv H3.
  - inv H2.
  - inv H2.
  - inv H2.
    (* destruct IHtyping with (e0:=e1) (E:=E) as [Trcd' [? ?]]...
    destruct (exposure_ext_ex2 H3 H5 H) as [Trcd'' ?].
    epose proof Tlookup_conserv H7 H0.
    destruct H8 as [Ti']. destruct_hypos.
    exists Ti'. split...
    + eapply Fsub.typing_proj with (T:=Trcd'')...
      apply Fsub.typing_sub with (S:=Trcd')...
      pose proof (Algo.typing_regular H1). destruct_hypos.
      apply Algo.exposure_sound in H...
      eapply sub_conserv;[..|apply H]... *)
  (* - inv H0. *)
   (* exists Fsub.typ_rcd_nil. split...
    constructor... apply wf_env_conserv with (E':=G)... *)
  (* - inv H2.  *)
    (* destruct IHtyping1 with (e:=e0) (E:=E) as [T1' [? ?]]...
    destruct IHtyping2 with (e:=e3) (E:=E) as [T2' [? ?]]...
    exists (Fsub.typ_rcd_cons i T1' T2')...
    split...
    constructor...
    + apply rt_type_conserv in H8. tauto.
    + apply rt_expr_conserv in H9. tauto.
    + apply collectLabele_conserv in H9...
      rewrite H9... *)
Qed.

Theorem typing_algo_conserv:
forall E E' e e' t t', 
ExtDefs.env_ext E E' ->
ExtDefs.exp_ext e e' ->
ExtDefs.typ_ext t t' ->
Algo.typing E' e' t' -> Fsub.typing E e t.
Proof with auto.
  intros. 
  generalize dependent E.
  generalize dependent e.
  generalize dependent t.
  induction H2;intros.
  - inv H0. inv H1.
    apply Fsub.typing_nat.
    eapply wf_env_conserv;eassumption...
  - inv H2.
    apply Fsub.typing_var.
    { eapply wf_env_conserv;eassumption... }
    { eapply bind_typ_conserv in H3;eauto.
      destruct H3 as [U' [? ?]]...
      rewrite (ExtDefs.typ_ext_inj2 H1 H4)... }
  - inv H2. inv H1.
    rewrite (ExtDefs.typ_ext_inj2 H9 H7) in *...
    apply Fsub.typing_abs with (L:=L).
    intros. specialize_x_and_L x L.
    apply H0...
    { apply open_ee_conserv... }
    { constructor... }
  - inv H2.
    destruct (typ_ext_ex2 H3 H7 H2_)
    as [T1' [? ?]].
    destruct (exposure_ext_ex2 H3 H5 H) as [Tarr' ?].
    inv H6.
    rewrite (ExtDefs.typ_ext_inj2 H13 H1) in *...
    apply Fsub.typing_app with (T1:=T0).
    { apply Fsub.typing_sub with (S:=T1')...
      pose proof (Algo.typing_regular H2_). destruct_hypos.
      apply Algo.exposure_sound in H...
      eapply sub_conserv;[..|apply H]...
    }
    { destruct (typ_ext_ex2 H3 H8 H2_0) as [T2' ?].
      destruct_hypos.
      apply Fsub.typing_sub with (S:=T2')...
      eapply sub_conserv;[..|apply H0]... }
  - inv H1.
  - inv H1. inv H2.
    rewrite (ExtDefs.typ_ext_inj2 H9 H7) in *...
    apply Fsub.typing_tabs with (L:=L).
    intros. specialize_x_and_L x L.
    apply H0...
    { apply open_tt_conserv... }
    { apply open_te_conserv... }
    { constructor... }
  - inv H2.
  - inv H3.
    destruct (typ_ext_ex2 H4 H8 H2) as [Tall' [? ?]].
    destruct (exposure_ext_ex2 H4 H6 H) as [Tall'' ?].
    inv H7.
    pose proof open_tt_conserv H14 H9 0.
    rewrite (ExtDefs.typ_ext_inj2 H1 H10) in *...
    apply Fsub.typing_tapp with (T1:=T0)...
    { eapply Fsub.typing_sub with (S:=Tall')...
      pose proof (Algo.typing_regular H2). destruct_hypos.
      apply Algo.exposure_sound in H...
      eapply sub_conserv;[..|apply H]...
    }
    { eapply sub_conserv;[..|apply H0]... }
  - inv H3.
    destruct (typ_ext_ex2 H4 H8 H2) as [Tall' [? ?]].
    destruct (exposure_ext_ex2 H4 H6 H) as [Tall'' ?].
    inv H7.
  - inv H1.
  - inv H4.
  - inv H3.

  
  - inv H3.
  - inv H1.
    (* destruct (typ_ext_ex2 H4 H7 H2) as [Trcd' ?]. destruct_hypos.
    destruct (exposure_ext_ex2 H4 H6 H) as [Trcd'' ?].
    epose proof Tlookup_conserv H8 H0.
    destruct H9 as [Ti']. destruct_hypos.
    rewrite (ExtDefs.typ_ext_inj2 H1 H10) in *.
    apply Fsub.typing_proj with (T:=Trcd'')...
    apply Fsub.typing_sub with (S:=Trcd')...
    pose proof (Algo.typing_regular H2). destruct_hypos.
    apply Algo.exposure_sound in H...
    eapply sub_conserv;[..|apply H]... *)
  (* - inv H1. *)
   (* inv H0. constructor.
    apply wf_env_conserv with (E':=G)... *)
  (* - inv H2. *)
   (* inv H3. constructor...
    + apply rt_type_conserv in H10. tauto.
    + apply rt_expr_conserv in H12. tauto.
    + apply collectLabele_conserv in H12...
      rewrite H12... *)
Qed.


Theorem typing_conserv:
forall E E' e e' t t', 
ExtDefs.env_ext E E' ->
ExtDefs.exp_ext e e' ->
ExtDefs.typ_ext t t' ->
typing E' e' t' -> Fsub.typing E e t.
Proof with auto.
  intros.
  destruct (minimum_typing H2) as [s' ?].
  destruct_hypos.
  destruct (typ_ext_ex2 H H0 H3) as [s ?].
  destruct_hypos.
  pose proof typing_algo_conserv H H0 H6 H3.
  eapply Fsub.typing_sub with (S:=s)...
  eapply sub_conserv;[..|apply H4]...
Qed.

End Ext2Fsub.