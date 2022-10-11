Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export AlgoTyping.
Require Export Coq.micromega.Lia.

Module Fsub.

(*********************************************************)
(*********************************************************)
(********************** Definitions **********************)
(*********************************************************)
(*********************************************************)

Inductive typ : Set :=
  | typ_nat : typ
  | typ_top : typ
  | typ_bvar : nat -> typ
  | typ_fvar : var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
.


Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_nat : exp
.

Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat      
  | typ_top         => typ_top
  | typ_bvar J      => if K === J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X 
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  end.


Definition open_tt T U := open_tt_rec 0 U T.

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_nat :
      type typ_nat
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X, X `notin` L -> type (open_tt T2 (typ_fvar X))) ->
      type (typ_all T1 T2)
.



Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T1 T2 => typ_all (subst_tt Z U T1) (subst_tt Z U T2)                    
  end.

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bvar J => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_all T1 T2 => (fv_tt T1) `union` (fv_tt T2)
end.

Inductive binding : Set :=
| bind_sub : typ -> binding               
| bind_typ : typ -> binding.

Definition env := list (atom * binding).
Notation empty := (@nil (atom * binding)).


Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.

Inductive WF : env -> typ -> Prop :=
| WF_top : forall E, WF E typ_top
| WF_nat : forall E, WF E typ_nat
| WF_var: forall U E (X : atom),
      binds X (bind_sub U) E ->
      WF E (typ_fvar X)
| WF_arrow : forall E A B,
    WF E A ->
    WF E B ->
    WF E (typ_arrow A B)
| WF_all : forall L E T1 T2,
      WF E T1 ->
      (forall X : atom, X `notin` L ->
        WF (X ~ bind_sub T1 ++ E) (open_tt T2 X)) ->
      WF E (typ_all T1 T2)
.

Fixpoint fl_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bvar J => {}
  | typ_fvar X => {}
  | typ_arrow T1 T2 => (fl_tt T1) `union` (fl_tt T2)
  | typ_all T1 T2 => (fl_tt T1) \u (fl_tt T2)
  end.

Fixpoint fv_env (E:env) : atoms :=
  match E with
  | nil => {}
  | (x,bind_sub y)::E' => (fv_tt y) \u (fv_env E')
  | (x,bind_typ y)::E' => (fv_tt y) \u (fv_env E')
  end.

Fixpoint fl_env (E:env) : atoms :=
  match E with
  | nil => {}
  | (x,bind_sub y)::E' => (fl_tt y) \u (fl_env E')
  | (x,bind_typ y)::E' => (fl_tt y) \u (fl_env E')
  end.

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E ->
      WF E T ->
      X `notin` dom E ->
      wf_env (X ~ bind_sub T ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      WF E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).

Inductive sub : env -> typ -> typ -> Prop :=
| sa_nat: forall E,
    wf_env E ->
    sub E typ_nat typ_nat
| sa_fvar: forall E X,
    wf_env E ->
    WF E (typ_fvar X) ->
    sub E (typ_fvar X) (typ_fvar X)
| sa_top : forall E A,
    wf_env E ->
    WF E A -> 
    sub E A typ_top
| sa_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T
| sa_arrow: forall E A1 A2 B1 B2,
    sub E B1 A1 ->
    sub E A2 B2 ->
    sub E (typ_arrow A1 A2) (typ_arrow B1 B2)
| sa_all : forall L E S T1 T2,
    WF E S ->
      (forall X : atom, X `notin` L ->
          sub (X ~ bind_sub S ++ E) (open_tt T1 X) (open_tt T2 X)) ->
      sub E (typ_all S T1) (typ_all S T2)
.


Definition subst_tb (Z : atom) (P : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_tt Z P T)
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_nat => exp_nat
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs V e1 => exp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_nat => exp_nat
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_tabs V e1 => exp_tabs V (open_ee_rec k f e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f e1) V
  end.

Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.

Inductive expr : exp -> Prop :=
  | expr_nat : expr exp_nat
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L T e1,
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs T e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
.

Definition body_e (e : exp) :=
  exists L, forall x : atom, x `notin` L -> expr (open_ee e x).


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
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (exp_app e1 e2) T2
  | typing_tabs : forall L E V e1 T1,
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_sub V ++ E) (open_te e1 X) (open_tt T1 X)) ->
      typing E (exp_tabs V e1) (typ_all V T1)
  | typing_tapp : forall T1 E e1 T T2,
      typing E e1 (typ_all T1 T2) ->
      sub E T T1 ->
      typing E (exp_tapp e1 T) (open_tt T2 T)
  | typing_sub : forall S E e T,
      typing E e S ->
      sub E S T ->
      typing E e T
.

Inductive value : exp -> Prop :=
  | value_abs : forall t1 T, 
      expr (exp_abs T t1) ->
      value (exp_abs T t1)
  | value_tabs : forall t1 T, 
      expr (exp_tabs T t1) ->
      value (exp_tabs T t1)
  | value_nat:
      value exp_nat
.

Inductive step : exp -> exp -> Prop :=
 | step_beta : forall (e1 e2:exp) T,
     expr (exp_abs T e1) ->
     value e2 ->
     step (exp_app  (exp_abs T e1) e2)  (open_ee e1 e2)
 | step_app1 : forall (e1 e2 e1':exp),
     expr e2 ->
     step e1 e1' ->
     step (exp_app e1 e2) (exp_app e1' e2)
 | step_app2 : forall v1 e2 e2',
     value v1 ->
     step e2 e2' ->
     step (exp_app v1 e2) (exp_app v1 e2')
 | step_tapp : forall e1 e1' V,
      type V ->
      step e1 e1' ->
      step (exp_tapp e1 V) (exp_tapp e1' V)
 | step_tabs : forall T1 e1 T2,
      expr (exp_tabs T1 e1) ->
      type T2 ->
      step (exp_tapp (exp_tabs T1 e1) T2) (open_te e1 T2)
.

Hint Constructors type WF wf_env sub expr typing step value: core.


Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_nat => {}
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_abs V e1  => (fv_tt V) `union` (fv_te e1)
  | exp_app e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_tabs V e1 => (fv_tt V) `union` (fv_te e1)
  | exp_tapp e1 V => (fv_tt V) `union` (fv_te e1)
  end.

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_nat => {}
  | exp_bvar i => {}
  | exp_fvar x => {{ x }}
  | exp_abs V e1 => (fv_ee e1)
  | exp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_tabs V e1 => (fv_ee e1)
  | exp_tapp e1 V => (fv_ee e1)
  end.

Fixpoint subst_te (Z : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_nat => exp_nat
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | exp_app e1 e2 => exp_app  (subst_te Z U e1) (subst_te Z U e2)
  | exp_tabs V e1 => exp_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | exp_tapp e1 V => exp_tapp (subst_te Z U e1) (subst_tt Z U V)
  end.

Fixpoint subst_ee (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_nat => exp_nat
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then u else e
  | exp_abs V e1 => exp_abs V (subst_ee z u e1)
  | exp_app e1 e2 => exp_app (subst_ee z u e1) (subst_ee z u e2)
  | exp_tabs V e1 => exp_tabs V (subst_ee z u e1)
  | exp_tapp e1 V => exp_tapp (subst_ee z u e1) V
  end.

Definition equiv E A B := sub E A B /\ sub E B A.

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
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u A1 \u A2 \u A3).



(*********************************************************)
(*********************************************************)
(******************** Infrastructures ********************)
(*********************************************************)
(*********************************************************)


Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
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


Ltac add_nil_fsub :=
    match goal with
    | [ |- WF ?E _ ] => rewrite_alist (nil ++ E)                               
    | [ |- sub ?E _ _ ] => rewrite_alist (nil ++ E)                                  
    end.

    

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


Fixpoint close_tt_rec (K : nat) (Z : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat      
  | typ_top         => typ_top              
  | typ_bvar J      => typ_bvar J
  | typ_fvar X      => if X == Z then typ_bvar K else typ_fvar X 
  | typ_arrow T1 T2 => typ_arrow (close_tt_rec K Z T1) (close_tt_rec K Z T2)
  | typ_all A B     => typ_all (close_tt_rec K Z A) 
                                (close_tt_rec (S K) Z B)
  end.

Definition close_tt T X := close_tt_rec 0 X T.

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
| WD_all: forall A B n,
    WFD A n ->
    WFD B (S n) ->
    WFD (typ_all A B) n
.

Hint Constructors WFC WFD WFE: core.


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

Lemma close_type_wfd: forall A,
    type A -> WFD A 0.
Proof with auto.
  intros.
  induction H;intros...
  - (* WFD_all *)
    constructor...
    pick_fresh X.
    specialize_x_and_L X L.
    apply close_wfd with (X:=X) in H1.
    rewrite <- close_open_reverse in H1...
Qed.

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


Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T).
Proof with auto.
  intros Z P T HT HP.
  induction HT; simpl...
  destruct (X == Z)...
  pick fresh Y.
  apply type_all with (L:=L \u {{Z}})...
  intros.
  rewrite subst_tt_open_tt_var...
Qed.

Lemma subst_tt_twice: forall (X Y:atom) T,
  X \notin fv_tt T ->
  T = subst_tt X Y (subst_tt Y X T).
Proof with auto.
  induction T;intros;simpl in *;try f_equal...
  +
    destruct (a == Y);simpl...
    destruct (X == X);simpl;try f_equal...
    tauto.
    destruct (a == X);simpl;try f_equal...
    exfalso. simpl in H...
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


Lemma fv_open_tt_notin_inv: forall T S (X:atom),
    X \notin fv_tt T ->
    fv_tt (open_tt T X) [<=] add X S ->
    fv_tt T [<=] S.
Proof with auto.
  intro T.
  unfold open_tt in *.
  generalize 0.
  induction T;intros;simpl in *;try solve [apply KeySetProperties.subset_empty]...
  -
    unfold "[<=]" in *.
    intros...
    apply AtomSetNotin.D.F.singleton_iff in H1...
    subst.
    assert (a0 `in` singleton a0) by auto.
    specialize (H0 a0 H1)...
    apply AtomSetImpl.add_3 in H0...
  -
    apply union_subset_7 in H0.
    apply notin_union in H.
    destruct_hypos.
    apply KeySetProperties.union_subset_3...    
    apply IHT1 with (X:=X) (n:=n)...
    apply IHT2 with (X:=X) (n:=n)...
  -
    apply union_subset_7 in H0.
    apply notin_union in H.
    destruct_hypos.
    apply KeySetProperties.union_subset_3...    
    apply IHT1 with (X:=X) (n:=n)...
    apply IHT2 with (X:=X) (n:=(Datatypes.S n))...
Qed.


Lemma open_tt_var_rev: forall A B (X:atom),
    X \notin fv_tt A \u fv_tt B ->
    open_tt A X = open_tt B X ->
    A = B.
Proof with auto.
  unfold open_tt.
  generalize 0.
  intros n A B.
  generalize dependent n.
  generalize dependent B.
  induction A;induction B;intros;simpl in *;try solve [inversion H0|destruct (n0==n);subst;inversion H0]...
  -
    destruct (n1==n);destruct (n1==n0);subst...
    inversion H0.
    inversion H0.
  -
    destruct (n0==n);subst...
    inversion H0.
    rewrite <- H2 in H.
    solve_notin_self X.
  -
    destruct (n0==n);subst...
    inversion H0.
    rewrite  H2 in H.
    solve_notin_self X.
  -
    inversion H0.
    apply IHA1 in H2...
    apply IHA2 in H3...
    subst...
  -
    inversion H0.
    apply IHA1 in H2...
    apply IHA2 in H3...
    subst...
Qed.


(*********************************************************)
(*********************************************************)
(******************** Regularity *************************)
(*********************************************************)
(*********************************************************)


Lemma wf_typ_strengthening : forall E F x U T,
 WF (F ++ x ~ bind_typ U ++ E) T ->
 WF (F ++ E) T.
Proof with eauto.
  intros. 
  dependent induction H...
  -
    analyze_binds H...
  -
    apply WF_all with (L:=L);intros...
    rewrite_env (((X~ bind_sub T1) ++ F) ++ E)...
    apply H1 with (x0:=x) (U0:=U)...
Qed.



Lemma WF_weakening: forall E1 E2 T E,
    WF (E1 ++ E2) T ->
    WF (E1 ++ E ++ E2) T.
Proof with eauto.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    apply WF_all with (L:=L)...
    intros.
    rewrite_alist (([(X, bind_sub T1)] ++ E1) ++ E ++ E2).
    apply H1...
Qed.


Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  WF E U.
Proof with auto.
  induction 1; intros J; analyze_binds J...
  -
    apply IHwf_env in BindsTac...
    add_nil_fsub.
    apply WF_weakening...
  -
    inversion BindsTacVal;subst.
    add_nil_fsub.
    apply WF_weakening...
  -
    apply IHwf_env in BindsTac...
    add_nil_fsub.
    apply WF_weakening...
Qed.



Lemma WF_type: forall E T,
    WF E T -> type T.
Proof with auto.
  intros.
  induction H...
  apply type_all with (L:=L)...
Qed.

Lemma sub_regular : forall E A B,
    sub E A B -> wf_env E /\ WF E A /\ WF E B.
Proof with auto.
  intros.
  induction H;destruct_hypos...
  -
    repeat split...
    apply WF_var with (U:=U)...
  -
    pick fresh Z.
    assert ( wf_env (Z ~ bind_sub S ++ E)).
    specialize_x_and_L Z L.
    destruct_hypos.
    dependent destruction H1...
    dependent destruction H2.
    repeat split...
    apply WF_all with (L:=L);intros...
    eapply H1...
    apply WF_all with (L:=L);intros...
    eapply H1...
Qed.


Lemma binds_map_free: forall F X  Y U  P,
    In (X, bind_sub U) F ->
    X <> Y ->
    In (X, bind_sub (subst_tt Y P U)) (map (subst_tb Y P) F).
Proof with auto.
  induction F;intros...
  apply in_inv in H.
  destruct H...
  -
    destruct a.
    inversion H;subst.
    simpl...
  -
    simpl...
Qed.

Lemma subst_tb_wf : forall F Q E Z P T,
  WF (F ++ Z ~ Q ++ E) T ->
  WF E P ->
  WF (map (subst_tb Z P) F ++ E) (subst_tt Z P T).
Proof with eauto.
  intros.
  generalize dependent P.
  dependent induction H;intros;simpl in *...
  -
    destruct (X==Z);subst...
    add_nil_fsub.
    apply WF_weakening...
    analyze_binds H...
    apply WF_var with (U:=(subst_tt Z P U))...
    unfold binds in *.
    apply In_lemmaL.
    apply binds_map_free...
  -
    apply WF_all with (L:=L \u {{Z}})...
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) (X ~ bind_sub T1 ++ F) ++ E).
    apply H1 with (Q0:=Q)...
    apply WF_type in H2...
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
      add_nil_fsub.
      apply wf_typ_strengthening with (x:=Y) (U:=V)...
  - 
    inv H6...
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
    inv H3...
    repeat split...
    + constructor... apply WF_type with (E:=E).
      apply sub_regular in H0. destruct_hypos...
    +
      pick fresh X.
      rewrite subst_tt_intro with (X:=X)...
      rewrite_env (map (subst_tb X  T) nil ++ E).
      apply subst_tb_wf with (Q:=bind_sub T1)...
      apply H8...
      apply sub_regular in H0. destruct_hypos...
  -
    repeat split...
    apply sub_regular in H0. destruct_hypos...
Qed.



(*********************************************************)
(*********************************************************)
(******************** Reflexivity ************************)
(*********************************************************)
(*********************************************************)



Lemma Reflexivity: forall E A,
    WF E A ->
    wf_env E ->
    sub E A A.
Proof with auto.
  intros.
  induction H...
  -
    constructor...
    apply WF_var with (U:=U)...
  -
    apply sa_all with (L:=L \u dom E \u fv_env E \u fl_env E)...
Qed.



(*********************************************************)
(*********************************************************)
(*********** Context Strengthen/weakening ****************)
(*********************************************************)
(*********************************************************)


Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ x ~ bind_typ T ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma Sub_typ_strengthening : forall E F x U A B,
 sub (F ++ x ~ bind_typ U ++ E) A B ->
 sub (F ++ E) A B.
Proof with eauto using wf_env_strengthening, wf_typ_strengthening.
  intros. 
  dependent induction H...
  -
    apply sa_trans_tvar with (U:=U0)...
    analyze_binds H...
  -
    apply sa_all with (L:=L);intros...
    rewrite_env (((X~ bind_sub S) ++ F) ++ E)...
    apply H1 with (x0:=x) (U0:=U)...
Qed.


Lemma Sub_weakening: forall E1 E2 A B E,
    sub (E1 ++ E2) A B ->
    wf_env (E1 ++ E ++ E2) ->
    sub (E1 ++ E ++ E2) A B.
Proof with eauto using WF_weakening.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    apply sa_all with (L:=L \u dom E1 \u dom E2 \u dom E \u fv_env (E1++E++E2) \u fl_env (E1++E++E2))...
    intros.
    rewrite_alist (([(X, bind_sub S)] ++ E1) ++ E ++ E2).
    apply H1...
    rewrite_alist ([(X, bind_sub S)] ++ E1 ++ E ++ E2)...
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


Lemma wf_env_cons: forall E1 E2,
    wf_env (E1++E2) ->
    wf_env E2.
Proof with auto.
  induction E1;intros...
  destruct a...
  dependent destruction H...
Qed.


Lemma WF_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_sub U) E ->
  WF E U.
Proof with auto.
  induction 1; intros J; analyze_binds J...
  -
    inversion BindsTacVal;subst.
    add_nil_fsub.
    apply WF_weakening...
  -
    add_nil_fsub.
    apply WF_weakening...
 -
    add_nil_fsub.
    apply WF_weakening...
Qed.


Lemma in_binds: forall x a U x0,
    a `in` dom (x ++ (a, bind_sub U) :: x0).
Proof with auto.
  induction x;intros...
  simpl...
  simpl...
  destruct a...
Qed.



Lemma WF_imply_dom: forall E A,
    WF E A ->
    fv_tt A [<=] dom E.
Proof with auto.
  intros.
  induction H;simpl in *;try solve [apply KeySetProperties.subset_empty]...
  -
    unfold binds in H...
    unfold "[<=]".
    intros.
    apply KeySetFacts.singleton_iff in H0.
    subst.
    apply in_split in H.
    destruct_hypos.
    rewrite H...
    apply in_binds...
  -
    apply KeySetProperties.union_subset_3...
  -
    apply KeySetProperties.union_subset_3...
    pick fresh X.
    specialize_x_and_L X L.
    apply fv_open_tt_notin_inv in H1...
Qed.


(*********************************************************)
(*********************************************************)
(******************** Replacing **************************)
(*********************************************************)
(*********************************************************)


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
  - apply typing_app with (T1:=T1)...
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
  - simpl. apply typing_tapp with (T1:=T1)...
    apply IHtyping...
    { apply Sub_typ_strengthening in H0.
      rewrite_env (E1 ++ Y  ~ bind_typ U ++ E2).
      apply Sub_weakening...
    }
  - apply typing_sub with (S:=S)...
    { apply Sub_typ_strengthening in H0.
      rewrite_env (E1 ++ Y  ~ bind_typ U ++ E2).
      apply Sub_weakening...
    }
Qed.


Lemma WF_replacing: forall E1 E2 T U (X Y:atom),
    WF ( E1 ++ X ~ bind_sub U ++E2) T ->
    Y <> X ->
    WF (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++E2) (subst_tt X Y T).
Proof with auto.
  intros.
  dependent induction H;intros;simpl;try solve [rewrite_alist (map (subst_tb X Y) E1  ++ Y ~ bind_sub U ++ E2);constructor;auto]...
  -
    destruct (X0==X)...
    { subst. apply WF_var with (U:=U)... }
    { apply binds_app_iff in H. destruct H.
      + apply WF_var with (U:=(subst_tt X Y U0))...
        apply binds_app_iff. left.
        apply binds_map_free...
      + apply WF_var with (U:=U0)...
        simpl. analyze_binds H. }
  - apply WF_all with (L:= L \u {{X}});intros...
    + apply IHWF...
    + rewrite_alist ((map (subst_tb X Y) ((X0 ~ bind_sub T1) ++ E1)) ++ Y ~ bind_sub U ++ E2).
      rewrite  subst_tt_open_tt_var...
Qed.


Lemma maps_subst_tb_free: forall E X U,
    X \notin fv_env E ->
    map (subst_tb X U) E = E.
Proof with auto.
  induction E;intros...
  destruct a.
  destruct b.
  -
    simpl in *.
    f_equal...
    f_equal...
    f_equal...
    rewrite <- subst_tt_fresh...
  -
    simpl in *.
    f_equal...
    f_equal...
    f_equal...
    rewrite <- subst_tt_fresh...
Qed.


Lemma fv_env_ls_dom: forall E,
    wf_env E ->
    fv_env E [<=] dom E.
Proof with auto.
  induction E;intros;simpl in *...
  -
    apply AtomSetProperties.subset_empty...
  -
    destruct a.
    destruct b.
    +
      dependent destruction H.
      apply KeySetProperties.subset_add_2...
      apply AtomSetProperties.union_subset_3...
      apply WF_imply_dom...
    +
      dependent destruction H.
      apply KeySetProperties.subset_add_2...
      apply AtomSetProperties.union_subset_3...
      apply WF_imply_dom...
Qed.


Lemma notin_from_wf_env: forall E1 X T E2,
    wf_env (E1 ++ (X, bind_sub T) :: E2) ->
    X \notin fv_tt T \u dom E2 \u dom E1 \u fv_env E2.
Proof with auto.
  induction E1;intros...
  -
    dependent destruction H...
    apply WF_imply_dom in H0...
    apply fv_env_ls_dom in H...    
  -
    dependent destruction H...
    simpl in *...
    apply IHE1 in H...
    simpl in *...
    apply IHE1 in H...
Qed.

Lemma binds_map_free_sub: forall E1 E2 X Y U S Q,
    Y \notin {{X}}  ->
    wf_env (E1 ++ (Y, bind_sub Q) :: E2) ->
    binds X (bind_sub U) (E1 ++ (Y, bind_sub Q) :: E2) ->
    binds X (bind_sub (subst_tt Y S U)) (map (subst_tb Y S) E1 ++  E2).
Proof with auto.
  intros.
  analyze_binds H1...
  -
    unfold binds in *.
    apply In_lemmaL.
    apply binds_map_free...
  -
    unfold binds in *.
    apply In_lemmaR.
    rewrite <- maps_subst_tb_free with (X:=Y) (U:=S)...
    apply binds_map_free...
    apply notin_from_wf_env in H0...
Qed.


Lemma sub_replacing: forall E1 E2 A B U X Y,
    sub (E1++ X ~ bind_sub U ++E2) A B ->
    X <> Y ->
    wf_env (map (subst_tb X Y)  E1 ++ Y ~ bind_sub U ++ E2) ->
    sub (map (subst_tb X Y) E1 ++ Y ~ bind_sub U ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros;simpl;try solve [rewrite_alist (map (subst_tb X Y) E1 ++ [(Y, bind_sub U)] ++ E2);constructor;auto;apply WF_replacing;auto]...
  -
    destruct (X0==X)...
    constructor... apply WF_var with (U:=U)...
    constructor...
    dependent destruction H0.
    apply binds_map_free_sub with (S:=Y) in H0...
    apply WF_var with (U:=(subst_tt X Y U0))...
    analyze_binds H0.
  -
    destruct (X0==X);subst...
    +
      apply sa_trans_tvar with (U:=subst_tt X Y U0)...
      analyze_binds_uniq H...
      apply uniq_from_wf_env...
      { apply sub_regular in H0. destruct_hypos... }
      inversion BindsTacVal;subst.
      apply sub_regular in H0. destruct_hypos...
      apply notin_from_wf_env in H0.
      rewrite <- subst_tt_fresh...
      apply IHsub...
    +
      apply sa_trans_tvar with (U:=subst_tt X Y U0)...
      analyze_binds H.
      *
        unfold binds in *.
        apply In_lemmaL.
        apply binds_map_free...
      *
        assert (Ht:=BindsTac0).
        apply WF_from_binds_typ in Ht...
        apply WF_imply_dom in Ht.
        apply sub_regular in H0. destruct_hypos.
        get_well_form.
        apply notin_from_wf_env in H.
        rewrite <- subst_tt_fresh...
        apply notin_partial with (E2:=dom E2)...
        apply wf_env_cons in H2.
        apply wf_env_cons in H2...
      *
        apply IHsub...
  -
    apply sa_all with (L:=L \u {{X}} \u dom (map (subst_tb X Y) E1 ++ (Y, bind_sub U) :: E2));intros...
    apply WF_replacing...
    rewrite_env (map (subst_tb X Y) (X0~bind_sub S ++ E1) ++ (Y, bind_sub U) :: E2).
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    apply H1...
    simpl...
    constructor...
    apply WF_replacing...
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
  - simpl. apply typing_app with (T2:=subst_tt X Y T2) (T1:=subst_tt X Y T1)...
    + apply IHtyping1...
    + apply IHtyping2...
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
    apply typing_tapp with  (T2:=subst_tt X Y T2) (T1:=subst_tt X Y  T1)...
    + apply IHtyping...
    + apply sub_replacing...
  - apply typing_sub with (S:= subst_tt X Y S)...
    apply sub_replacing...
Qed.


End Fsub.