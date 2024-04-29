Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Rules.


Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with congruence || eauto.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
    destruct (j === n)... destruct (i === n)...
Qed.


Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  unfold open_tt in *.
  pick fresh X.
  apply open_tt_rec_type_aux with (j:=0) (V:=(typ_fvar X))...
  unfold open_tt in *.
  pick fresh Y.
  apply open_tt_rec_type_aux with (j:=0) (V:=(typ_fvar Y))...
Qed.


Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt T ->
   T = subst_tt Z U T.
Proof with auto.
  induction T; simpl; intro H; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
    contradict H; fsetdec.
Qed.

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "typ_bvar".
    destruct (k === n); subst...
  Case "typ_fvar".
    destruct (a == X); subst... apply open_tt_rec_type...
Qed.

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with congruence || auto.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (typ_fvar X) T2).
Proof with congruence || auto.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "typ_bvar".
    destruct (k === n)... simpl. destruct (X == X)...
  Case "typ_fvar".
    destruct (a == X)... contradict Fr; fsetdec.
Qed.

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.

Lemma open_te_rec_expr_aux : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof with congruence || eauto.
  induction e; intros j u i P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_te_rec_type_aux : forall e j Q i P,
  i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_tt_rec_type_aux.
Qed.

Lemma open_te_rec_expr : forall e U k,
  expr e ->
  e = open_te_rec k U e.
Proof.
  intros e U k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_tt_rec_type;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_te_rec_expr_aux with (j := 0) (u := exp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_te_rec_type_aux with (j := 0) (Q := typ_fvar X);
    auto
  ].
Qed.

Lemma subst_te_fresh : forall X U e,
  X `notin` fv_te e ->
  e = subst_te X U e.
Proof.
  induction e; simpl; intros; f_equal; auto using subst_tt_fresh.
Qed.

Lemma subst_te_open_te_rec : forall e T X U k,
  type U ->
  subst_te X U (open_te_rec k T e) =
    open_te_rec k (subst_tt X U T) (subst_te X U e).
Proof.
  intros e T X U k WU. revert k.
  induction e; intros k; simpl; f_equal; auto using subst_tt_open_tt_rec.
Qed.

Lemma subst_te_open_te : forall e T X U,
  type U ->
  subst_te X U (open_te e T) = open_te (subst_te X U e) (subst_tt X U T).
Proof with auto.
  intros.
  unfold open_te.
  apply subst_te_open_te_rec...
Qed.

Lemma subst_te_open_te_var : forall (X Y:atom) U e,
  Y <> X ->
  type U ->
  open_te (subst_te X U e) Y = subst_te X U (open_te e Y).
Proof with congruence || auto.
  intros X Y U e Neq WU.
  unfold open_te.
  rewrite subst_te_open_te_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_te_intro_rec : forall X e U k,
  X `notin` fv_te e ->
  open_te_rec k U e = subst_te X U (open_te_rec k (typ_fvar X) e).
Proof.
  induction e; intros U k Fr; simpl in *; f_equal;
    auto using subst_tt_intro_rec.
Qed.

Lemma subst_te_intro : forall X e U,
  X `notin` fv_te e ->
  open_te e U = subst_te X U (open_te e X).
Proof with auto.
  intros.
  unfold open_te.
  apply subst_te_intro_rec...
Qed.

Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof with congruence || eauto.
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...
  Case "exp_bvar".
    destruct (j===n)... destruct (i===n)...
Qed.

Lemma open_ee_rec_type_aux : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; intros j V u i H; simpl; inversion H; f_equal; eauto.
Qed.

Lemma open_ee_rec_expr : forall u e k,
  expr e ->
  e = open_ee_rec k u e.
Proof with auto.
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := exp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_fvar X);
    auto
  ].
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_ee e ->
  e = subst_ee x u e.
Proof with auto.
  intros x u e; induction e; simpl; intro H; f_equal...
  Case "exp_fvar".
    destruct (a==x)...
    contradict H; fsetdec.
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  expr u ->
  subst_ee x u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x u e2) (subst_ee x u e1).
Proof with auto.
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n); subst...
  Case "exp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x u e) y = subst_ee x u (open_ee e y).
Proof with congruence || auto.
  intros x y u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
Qed.

Lemma subst_te_open_ee_rec : forall e1 e2 Z P k,
  subst_te Z P (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_te Z P e2) (subst_te Z P e1).
Proof with auto.
  induction e1; intros e2 Z P k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
Qed.

Lemma subst_te_open_ee : forall e1 e2 Z P,
  subst_te Z P (open_ee e1 e2) = open_ee (subst_te Z P e1) (subst_te Z P e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_te_open_ee_rec...
Qed.

Lemma subst_te_open_ee_var : forall Z (x:atom) P e,
  open_ee (subst_te Z P e) x = subst_te Z P (open_ee e x).
Proof with auto.
  intros.
  rewrite subst_te_open_ee...
Qed.

Lemma subst_ee_open_te_rec : forall e P z u k,
  expr u ->
  subst_ee z u (open_te_rec k P e) = open_te_rec k P (subst_ee z u e).
Proof with auto.
  induction e; intros P z u k H; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == z)... apply open_te_rec_expr...
Qed.

Lemma subst_ee_open_te : forall e P z u,
  expr u ->
  subst_ee z u (open_te e P) = open_te (subst_ee z u e) P.
Proof with auto.
  intros.
  unfold open_te.
  apply subst_ee_open_te_rec...
Qed.

Lemma subst_ee_open_te_var : forall z (X:atom) u e,
  expr u ->
  open_te (subst_ee z u e) X = subst_ee z u (open_te e X).
Proof with auto.
  intros z X u e H.
  rewrite subst_ee_open_te...
Qed.

Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_ee e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (exp_fvar x) e).
Proof with congruence || auto.
  induction e; intros u k Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (k === n)... simpl. destruct (x == x)...
  Case "exp_fvar".
    destruct (a == x)... contradict Fr; fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u,
  x `notin` fv_ee e ->
  open_ee e u = subst_ee x u (open_ee e x).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.


Lemma subst_tt_rt_type : forall Z P T,
  rt_type T ->
  type P ->
  rt_type (subst_tt Z P T).
Proof with auto.
  intros.
  induction H...
  constructor...
Qed.

Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T).
Proof with auto.
  intros Z P T HT HP.
  induction HT; simpl...
  destruct (X == Z)...
  pick fresh Y.
  apply type_mu with (L:=L \u {{Z}})...
  intros.
  rewrite subst_tt_open_tt_var...
  pick fresh Y.
  apply type_all with (L:=L \u {{Z}})...
  intros.
  rewrite subst_tt_open_tt_var...
  {
    (* typ_rcd_cons *)
    constructor... apply subst_tt_rt_type...
  }
Qed.

Lemma notin_fv_tt_open : forall X U T,
    X `notin` fv_tt T ->
    X \notin fv_tt U ->
    X `notin` fv_tt (open_tt T U).
Proof with auto.
  intros.
  simpl.
  unfold open_tt.
  unfold open_tt_rec.
  generalize 0.
  induction T;simpl in *;intros...
  destruct (n0==n)...
Qed.


Lemma notin_union: forall X A B,
    X `notin` (union A B) <->
    X `notin` A /\ X `notin` B.
Proof with auto.
  split.
  intros;split...
  intros;destruct H...
Qed.

Lemma notin_fv_subst2: forall X A B Y,
    X \notin fv_tt A ->
    X \notin fv_tt B ->
    X <> Y ->
    X \notin fv_tt (subst_tt Y A B).
Proof with auto.
  intros.
  induction B...
  -
    simpl.
    destruct (a == Y)...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
  - (* typ_rcd_cons *)
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0...
Qed.

Lemma notin_fv_subst: forall X A B,
    X \notin fv_tt A ->
    X \notin fv_tt B ->
    X \notin fv_tt (subst_tt X A B).
Proof with auto.
  intros.
  induction B...
  -
    simpl.
    destruct (a == X)...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
  -
    simpl in *.
    apply notin_union.
    apply notin_union in H0.
    destruct H0.
    split...
Qed.

Lemma notin_fv_env: forall E1 E2 X,
    X \notin fv_env E1 ->
    X \notin fv_env E2 ->
    X \notin fv_env (E1++E2).
Proof with auto.
  induction E1;intros...
  destruct a.
  destruct b;simpl in *...
Qed.

Lemma notin_fl_env: forall E1 E2 X,
    X \notin fl_env E1 ->
    X \notin fl_env E2 ->
    X \notin fl_env (E1++E2).
Proof with auto.
  induction E1;intros...
  destruct a.
  destruct b;simpl in *...
Qed.

Lemma notin_fl_tt_open : forall X U T,
    X `notin` fl_tt T ->
    X \notin fl_tt U ->
    X `notin` fl_tt (open_tt T U).
Proof with auto.
  intros.
  unfold open_tt.
  unfold open_tt_rec.
  generalize 0.
  induction T;simpl in *;intros...
  destruct (n0==n)...
Qed.

Lemma notin_fv_open_inv: forall A X B,
    X \notin fv_tt (open_tt A B) ->
    X \notin fv_tt A.
Proof with eauto.
  intro A.
  unfold open_tt.
  generalize 0.
  induction A;intros;simpl in *...
Qed.

Lemma In_lemmaR : forall {X: Type} (E1:list X) A  E2,
    In A E2 -> In A (E1 ++ E2).
Proof.
  induction E1; intros. simpl. auto.
  rewrite <- app_comm_cons.
  apply in_cons.
  apply  IHE1.
  assumption.
Qed.

Lemma In_lemmaL : forall {X: Type}  E2 (E1:list X) A,
    In A E1 -> In A ( E1 ++ E2).
Proof.
  induction E2;intros.
  -
    rewrite app_nil_r.
    assumption.
  -
    rewrite cons_app_one.
    rewrite <- app_assoc.
    apply IHE2.
    apply in_split in H.
    destruct H.
    destruct H.
    rewrite H.
    rewrite app_assoc.
    apply In_lemmaR.
    rewrite cons_app_one.
    rewrite app_assoc.
    rewrite <-cons_app_one.
    apply in_eq.
Qed.

Ltac destruct_hypos :=
  repeat
    match goal with
    | [H : _ /\ _ |- _ ] => destruct H
    | [H : exists _,_ |- _ ] => destruct H                                  
    end.

Ltac specialize_x_and_L X L :=
  repeat match goal with
         | [H : forall _, _ \notin L -> _, Q : X \notin L |- _ ] => specialize (H _ Q); clear Q
         | [H : forall _, _ \notin L -> _ |- _ ] => assert (X \notin L) by auto
         end.


Ltac add_nil :=
    match goal with
    | [ |- WF ?E _ ] => rewrite_alist (nil ++ E)                               
    | [ |- sub ?E _ _ ] => rewrite_alist (nil ++ E)                                  
    end.

Ltac solve_notin :=
  repeat
    match goal with
    | [H : _ |- _ \notin fv_tt (open_tt _ _) ] => apply notin_fv_tt_open
    | [H : _ |- _ \notin fl_tt (open_tt _ _) ] => apply notin_fl_tt_open
    | [H : _ |- _ \notin fv_tt (subst_tt _ _ _) ] => apply notin_fv_subst
    | [H : _ |- _ \notin fv_env (_ ++ _) ] => apply notin_fv_env
    | [H : _ |- _ \notin fl_env (_ ++ _) ] => apply notin_fl_env
    | [H : _ |- _ \notin (_ \u _) ] => apply notin_union;split
    | [H : _ |- _ \notin _ ] => simpl;auto               
    end.

Ltac solve_notin_self X :=
  repeat match goal with
         | [H : X \notin (singleton X) |- _ ] => apply notin_singleton_1 in H;destruct H;auto
         | [H : _ \notin _ \u _ |- _ ] => apply notin_union in H;destruct H
         end. 


(* Record *)


Lemma union_empty: forall A i,
    union (singleton i) A [<=] Metatheory.empty -> False.
Proof with eauto.
  intros.
  unfold "[<=]" in H.
  eapply empty_iff...
Qed.

Ltac collect_nil H := simpl in H;apply union_empty in H;destruct H.

Lemma label_belong: forall i A B,
    Tlookup i A = Some B -> i \in collectLabel A.
Proof with auto.
  intros.
  dependent induction A;simpl in *;try solve [inversion H]...
  destruct (a==i)...
  apply IHA2 in H...
Qed.

Lemma label_trans: forall i A B,
    i \in  A -> A [<=] B -> i \in  B .
Proof with auto.
  intros.
  unfold "[<=]" in H0...
Qed.

Lemma lookup_some: forall i T,
    i \in collectLabel T ->
    exists S, Tlookup i T = Some S.
Proof with auto.
  intros.
  induction T;simpl in *;try solve [apply empty_iff in H;destruct H]...
  apply AtomSetImpl.union_1 in H...
  destruct H...
  apply KeySetFacts.singleton_iff in H.
  exists T1...
  destruct (a==i)...
  destruct n...
  apply IHT2 in H...
  destruct H.
  destruct (a==i)...
  exists T1...
  exists x...
Qed.  
  
(* Lemma rcd_types_match : forall S T E i Ti,
  sub E S T ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si /\ sub E Si Ti.
Proof with auto.
  intros.
  dependent induction H;simpl in *;try solve [inversion H1|inversion H0|inversion H3]...
  - specialize (IHsub H1). destruct_hypos.
  induction H1...
  simpl in H7;inversion H7.
  induction H0...
  simpl in H2.
  apply union_empty in H2...
  destruct H2.
  assert (Ht:=H7).
  apply label_belong in Ht.
  apply label_trans with (B:=collectLabel (typ_rcd_cons i1 T0 T3)) in Ht...
  apply lookup_some in Ht.
  destruct Ht.
  specialize (H5 i x Ti H0 H7)...
  exists x...
Qed.   *)

Lemma rcd_inversion: forall A B E,
    sub E A B ->
    rt_type A ->
    rt_type B ->
    (forall i t1 t2, Tlookup i A = Some t1 ->  Tlookup i B = Some t2 -> sub E t1 t2).
Proof with auto.
  intros.
  induction H;try solve [inversion H0|inversion H1]...
  apply H9 with (i:=i)...
Qed.

Fixpoint dropLabel (Z : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (dropLabel Z  T1) (dropLabel Z  T2)
  | typ_mu T => typ_mu (dropLabel Z  T)
  | typ_all T1 T2 => typ_all (dropLabel Z  T1) (dropLabel Z  T2)
  | typ_label i T => typ_label i (dropLabel Z  T)
  | typ_rcd_nil     => typ_rcd_nil
  | typ_rcd_cons i T1 T2  => if (i==Z) then (dropLabel Z T2) else (typ_rcd_cons i T1 (dropLabel Z T2))
  end.

Lemma rt_type_drop: forall E A i,
    WF E A ->
    rt_type A -> rt_type (dropLabel i A).
Proof with auto.
  intros.
  induction H;try solve [inversion H0]...
  simpl.
  destruct (i0==i)...
Qed.

Lemma union_subset_x: forall a b c,
    b [<=] c ->
    union a b [<=] union a c.
Proof with auto.
  intros.
  apply AtomSetProperties.union_subset_3...
  apply AtomSetProperties.union_subset_1...
  apply KeySetProperties.subset_trans with (s2:=c)...
  apply AtomSetProperties.union_subset_2...
Qed.

Lemma drop_collect: forall A i,
    collectLabel A [<=] {{i}} \u collectLabel (dropLabel i A).
Proof with auto.
  intros.
  induction A;simpl;try solve [apply AtomSetProperties.union_subset_2]...
  destruct (a==i)...
  subst.
  apply AtomSetProperties.union_subset_3 with (s:={{i}}) in IHA2...
  apply AtomSetProperties.union_subset_1.
  simpl.
  rewrite <- AtomSetProperties.union_assoc...
  assert (union (singleton i) (singleton a) [=] {{a}} \u {{i}}).
  rewrite  KeySetProperties.union_sym...
  apply KeySetProperties.equal_refl...
  rewrite H.
  rewrite  AtomSetProperties.union_assoc...
  apply union_subset_x...
Qed.

Lemma drop_coolect_less: forall A i,
    collectLabel (dropLabel i A) [<=] collectLabel A.
Proof with auto.
  intros.
  induction A;simpl in *;try solve [apply F.Subset_refl]...
  destruct (a==i)...
  apply KeySetProperties.subset_trans with (s2:=collectLabel A2)...
  apply AtomSetProperties.union_subset_2.
  simpl...
  apply union_subset_x...
Qed.

Lemma drop_collect_flip: forall A i,
    i \in collectLabel A ->
    {{i}} \u collectLabel (dropLabel i A) [<=] collectLabel A.
Proof with auto.
  intros.
  induction A;simpl in *;try solve [apply KeySetFacts.empty_iff in H;destruct H]...
  apply F.union_iff in H.
  destruct H...
  apply AtomSetImpl.singleton_1 in H...
  destruct (a==i)...
  subst.
  apply union_subset_x...
  apply drop_coolect_less...
  destruct n...
  destruct (a==i)...
  subst.
  apply union_subset_x...
  apply drop_coolect_less...
  apply IHA2 in H.
  simpl...
  rewrite <- AtomSetProperties.union_assoc...
  assert (union (singleton i) (singleton a) [=] {{a}} \u {{i}}).
  rewrite  KeySetProperties.union_sym...
  apply KeySetProperties.equal_refl...
  rewrite H0.
  rewrite  AtomSetProperties.union_assoc...
  apply union_subset_x...
Qed.

Lemma union_subset_x2: forall a b c,
    union {{a}} b [<=] union {{a}} c ->
    a \notin b ->
    b [<=] c.
Proof with auto.
  intros.
  unfold "[<=]" in *.
  intros.
  assert (Ht:=H1).
  apply AtomSetImpl.union_3 with (s:={{a}}) in Ht.
  specialize (H _ Ht).
  apply AtomSetImpl.union_1 in H.
  destruct H...
  apply AtomSetImpl.singleton_1 in H...
  subst.
  assert (False).
  apply H0...
  destruct H.
Qed.

Lemma open_tt_drop_var: forall A (X i : atom)  k,
    (open_tt_rec k X (dropLabel i A) ) = dropLabel i (open_tt_rec k X A).
Proof with auto.
  intro.
  induction A;intros;simpl in *;try solve [f_equal;auto]...
  destruct (k==n)...
  destruct (a==i)...
  simpl.
  f_equal...
Qed.


Lemma subst_tt_collect: forall T E i X A,
    i `notin` collectLabel T ->
    rt_type T ->
    WF E T ->
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
  

Lemma notin_drop_fv: forall X A i,
    X \notin fv_tt A ->
    X `notin` fv_tt (dropLabel i A).
Proof with auto.
  intros.
  induction A;simpl in *...
  destruct (a==i)...
Qed.

Lemma notin_drop_collect: forall X A i,
    X \notin collectLabel A ->
    X `notin` collectLabel (dropLabel i A).
Proof with auto.
  intros.
  induction A;simpl in *...
  destruct (a==i)...
Qed.

Lemma notin_drop_collect_self: forall  A i,
    i \notin collectLabel A ->
   collectLabel A [=] collectLabel (dropLabel i A).
Proof with auto.
  intros.
  induction A;simpl in *;try solve [apply KeySetProperties.equal_refl]...
  destruct (a==i)...
  apply notin_union in H.
  destruct H.
  subst.
  apply notin_singleton_1 in H.
  destruct H...
  simpl...
  apply notin_union in H.
  destruct H...
  apply KeySetProperties.union_equal_2...
Qed.

Lemma notin_drop_self: forall j A,
    j `notin` collectLabel (dropLabel j A).
Proof with auto.
  intros.
  induction A...
  simpl.
  destruct (a==j)...
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

Lemma Tlookup_fv_tt: forall i A t,
  Tlookup i A = Some t ->
  fv_tt t [<=] fv_tt A.
Proof with auto.
  intros. induction A;try solve [inversion H]...
  - simpl in *. destruct (a==i)...
    + inversion H... intro x. intros. apply union_iff...
    + apply IHA2 in H. intro x. intros. apply union_iff...
Qed.
  