Require Export Metalib.Metatheory.
Require Export String.

Inductive typ : Set :=
  | typ_nat : typ
  | typ_top : typ
  | typ_bvar : nat -> typ
  | typ_fvar : var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
  | typ_mu : typ -> typ
  | typ_label : var -> typ -> typ                  
.

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_nat : exp
  | exp_unfold : typ -> exp -> exp
  | exp_fold : typ -> exp -> exp
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
  | typ_mu T        => typ_mu (open_tt_rec (S K) U T)
  | typ_label l T        => typ_label l (open_tt_rec K U T)                            
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
  | type_mu : forall L T,
      (forall X, X \notin L -> type (open_tt T (typ_fvar X))) ->
      type (typ_mu T)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X, X `notin` L -> type (open_tt T2 (typ_fvar X))) ->
      type (typ_all T1 T2)
  | type_label: forall l A,
      type A ->
      type (typ_label l A)
.



Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_mu T => typ_mu (subst_tt Z U T)
  | typ_label l T => typ_label l (subst_tt Z U T)                     
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
  | typ_mu T => (fv_tt T)
  | typ_label l T => (fv_tt T)
  end.

Inductive binding : Set :=
| bind_sub : typ -> binding               
| bind_typ : typ -> binding.

Definition env := list (atom * binding).
Notation empty := (@nil (atom * binding)).

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
| WF_rec : forall L E A,
      (forall X, X \notin L -> 
                 WF (X ~ bind_sub typ_top ++ E) (open_tt A X)) ->
      (forall X, X \notin L -> 
                 WF (X ~ bind_sub typ_top ++ E) (open_tt A (typ_label X (open_tt A X)))) ->
      WF E (typ_mu A)
| WF_label: forall E A X,
    WF E A ->
    WF E (typ_label X A)
.

Fixpoint fl_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_nat => {}
  | typ_bvar J => {}
  | typ_fvar X => {}
  | typ_arrow T1 T2 => (fl_tt T1) `union` (fl_tt T2)
  | typ_mu T => (fl_tt T)
  | typ_label X T => {{ X }} `union` fl_tt T
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
| sa_rec: forall L A1 A2 E,
    (forall X,
        X \notin L ->
        WF (X ~ bind_sub typ_top ++ E) (open_tt A1 X)) ->
    (forall X,
        X \notin L ->
        WF (X ~ bind_sub typ_top ++ E) (open_tt A2 X)) ->
    (forall X,
        X \notin L ->
        sub (X ~ bind_sub typ_top ++ E) (open_tt A1 (typ_label X (open_tt A1 X))) (open_tt A2 (typ_label X (open_tt A2 X)))) ->
    sub E (typ_mu A1) (typ_mu A2)
| sa_label: forall E X A B,
    sub E A B ->
    sub E (typ_label X A) (typ_label X B)
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
  | exp_unfold V e => exp_unfold (open_tt_rec K U V) (open_te_rec K U e)
  | exp_fold V e => exp_fold (open_tt_rec K U V) (open_te_rec K U e)
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
  | exp_unfold V e => exp_unfold V (open_ee_rec k f e)
  | exp_fold V e => exp_fold V (open_ee_rec k f e)                            
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
  | expr_unfold: forall T e,
     type T ->
     expr e ->
     expr (exp_unfold T e)
  | expr_fold: forall T e,
     type T ->
     expr e ->
     expr (exp_fold T e)
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
  | typing_fold : forall G A e ,
     typing G e  (open_tt A  (typ_mu A))    ->
     WF G (typ_mu A) ->
     typing G (exp_fold (typ_mu A) e) (typ_mu A)
 | typing_unfold : forall G T e,
     typing G e (typ_mu T) ->
     typing G (exp_unfold (typ_mu T) e)  (open_tt T  (typ_mu T))
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
  | value_fold: forall T e,
      type T ->
      value e ->
      value (exp_fold T e)
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
 | step_fld: forall S T v,
     value v ->
     type T ->
     type S ->
     step (exp_unfold S (exp_fold T v)) v
 | step_fold: forall e e' T,
     step e e' ->
     type T ->
     step (exp_fold T e) (exp_fold T e')
 | step_unfold: forall e e' T,
     step e e' ->
     type T ->
     step (exp_unfold T e) (exp_unfold T e')
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
  | exp_fold V e => fv_tt V \u fv_te e
  | exp_unfold V e => fv_tt V \u fv_te e
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
  | exp_fold V e => fv_ee e
  | exp_unfold V e => fv_ee e                        
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
  | exp_fold V e => exp_fold (subst_tt Z U V) (subst_te Z U e)
  | exp_unfold V e => exp_unfold (subst_tt Z U V) (subst_te Z U e)                           
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
  | exp_fold V e => exp_fold V (subst_ee z u e)
  | exp_unfold V e => exp_unfold V (subst_ee z u e)                                
  end.

Inductive Mode := Pos | Neg. 

Definition choose (m : Mode)  (C : typ) (D : typ) :=
  match m with
  | Pos => C
  | Neg => D
  end.

Definition flip (m : Mode) : Mode :=
  match m with
  | Pos => Neg
  | Neg => Pos
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
