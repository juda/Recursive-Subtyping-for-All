Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Progress.
Require Export Coq.micromega.Lia.

(* The first one is for recursive,
the second one is for universal. *)
Definition menv := list (nat * nat).
Notation empty_menv := (@nil (nat * nat)).

Definition genv  := list (atom * nat).

Fixpoint find  (n:nat) (E: list (nat * nat)) :=
  match E with
  | (k, v) :: E' =>
        if (n == k) then Some v else find n E'
  | nil => None
  end.

Fixpoint findX  (x:var) (G: list (atom * nat)) :=
  match G with
  | (k, v) :: E' =>
        if (x == k) then Some v else findX x E'
  | nil => None
  end.

Fixpoint bindings_rec (G:genv) (E: menv) (n: nat) (T:typ) : nat :=
  match T with
  | typ_nat => 1
  | typ_top => 1
  | typ_fvar x => 1 + match findX x G with
                      | Some k => k
                      | None => 1
                      end
  | typ_bvar m => 1 + match find (n - m) E with
                      | Some k => k
                      | None => 1 
                      end 
  | typ_arrow A B => S (bindings_rec G E n A) + (bindings_rec G E n B)
  | typ_label _ A => S (bindings_rec G E n A)
  | typ_all A B =>
    let i := bindings_rec G E n A in
    S (i + (bindings_rec G ((S n, i) :: E) (S n) B))
  | typ_mu A => 
       let i := bindings_rec G ((S n , 1) :: E) (S n) A in
       S (bindings_rec G ((S n, i) :: E) (S n) A)
  | typ_rcd_nil => 1
  | typ_rcd_cons i T1 T2 =>
      S (bindings_rec G E n T1) + (bindings_rec G E n T2)
  end.

Fixpoint mk_benv (E:env) : genv :=
  match E with
  | nil => nil
  | (_, bind_typ _)::E' => mk_benv E'
  | (X, bind_sub U)::E' => 
        let G := mk_benv E' in 
        (X, bindings_rec G nil 0 U) :: G
  end.

Definition bindings E T := bindings_rec (mk_benv E) nil 0 T.



Definition zero := 0.

Lemma bindings_find_in: forall (E1 E2:menv) k,
    find 0 (E1 ++ E2) = None ->
    find 0 (E1 ++ (0, k) :: E2) = Some k.
Proof with auto.
  induction E1...
  intros.
  destruct a.
  simpl in *.
  destruct n;simpl in *...
  inversion H.
Qed.

Lemma bindings_find_notin: forall (E1 E2:menv) k (n:nat),
    find (S n) (E1 ++ (0, k) :: E2) = find (S n) (E1++E2).
Proof with auto.
  induction E1;intros...
  -
    destruct a...
    simpl...
    destruct (S n == n0)...
Qed.

(* WFC typ n : type with <= k binded variables *)
Inductive WFC :  typ -> nat -> Prop :=
| WC_nat: forall k,
    WFC typ_nat k
| WC_top: forall k,
    WFC typ_top k
| WC_fvar: forall X k,
    WFC (typ_fvar X) k
| WC_bvar: forall b k,
    b <= k ->
    WFC (typ_bvar b) k
| WC_arrow: forall A B k,
    WFC A k ->
    WFC B k ->
    WFC (typ_arrow A B) k
| WC_all : forall A B n,
    WFC A n ->
    WFC B (S n) ->
    WFC (typ_all A B) n
| WC_rec: forall A n,
    WFC A (S n) ->
    WFC (typ_mu A) n
| WC_label: forall l A k,
    WFC A k ->
    WFC (typ_label l A) k
| WC_nil: forall k,
    WFC typ_rcd_nil k
| WC_cons: forall i A B k,
    WFC A k ->
    WFC B k ->
    WFC (typ_rcd_cons i A B) k
.

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

Inductive WFE : menv -> nat -> Prop :=
| WFE_empty:
    WFE nil 0
| WFE_cons: forall  b E k,
    WFE E k ->
    find (S k) E = None ->
    WFE ((S k,b)::E) (S k).

Hint Constructors WFC WFD WFE: core.


Fixpoint minusk (E:menv) (k:nat): menv :=
  match E with
  | nil => nil
  | (a,b)::E' => (a - k,b)::(minusk E' k)
  end.

Fixpoint maxfst (E:menv) : nat :=
  match E with
  | nil => 0
  | (a,_)::E' => max a (maxfst E')
  end.

Lemma WFE_maxfst : forall E k,
    WFE E k ->
    maxfst E <= k.
Proof with auto.
  induction 1...
  simpl...
  destruct (maxfst E)...
  lia.
Qed.

Lemma maxfst_find_none: forall E k,
    maxfst E <= k ->
    find (S k) E = None.
Proof with auto.
  induction E;intros...
  destruct a.
  simpl in *...
  destruct (S k == n)...
  lia.
  apply IHE...
  lia.
Qed.

Lemma WFE_find_none: forall k E,
    WFE E k ->
    find (S k) E = None.
Proof with auto.
  intros.
  apply maxfst_find_none...
  apply WFE_maxfst...
Qed.

Lemma WFE_S_n:forall E n k,
  WFE E n ->
  WFE ((S n, k)::E) (S n).
Proof with auto.
  induction E;intros...
  constructor...
  apply WFE_find_none...
Qed.

Lemma neq_minus: forall k n,
    n <= k ->
    n <> k ->
    exists q, k - n = S q.
Proof with auto.
  induction k;intros...
  inversion H...
  destruct H0...
  induction n...
  exists k...
  destruct IHk with (n:=n)...
  lia.
  exists x...
Qed.



Lemma neq_minus_v2: forall k n,
    n < k ->
    exists q, k - n = S q.
Proof with auto.
  induction k;intros...
  inversion H...
  induction n...
  exists k...
  destruct IHk with (n:=n)...
  lia.
  exists x...
Qed.

Fixpoint addone (E:menv) : menv :=
  match E with
  | nil => nil
  | (a,b)::E' => (S a,b)::(addone E')
  end.

Lemma find_add_eq: forall E k,
    find k E = find (S k) (addone E).
Proof with auto.
  induction E;intros...
  destruct a...
  simpl...
  destruct (k == n) ...
  destruct (S k == S n)...
  destruct n1...
  destruct (S k == S n)...
  destruct n1...
Qed.

Lemma find_add: forall E k b,
    k >= b ->
    find (k - b) E = find (S k - b) (addone E).
Proof with auto using find_add_eq.
  induction E;intros...
  -
    destruct a...
    assert (addone ((n, n0) :: E) = (S n, n0) :: addone E) by auto.
    rewrite H0.
    assert (S k - b = S (k-b)) by lia.
    rewrite H1.
    destruct (k-b);simpl...
    destruct (0==n)...
    destruct (1== S n)...
    destruct n1...
    destruct (1== S n)...
    destruct n1...
    destruct (S n1 == n)...
    destruct (S (S n1) == S n)...
    destruct n2...
    destruct (S (S n1) == S n)...
    destruct n2...
Qed.

    
Lemma bindings_add : forall E n A G,
    WFC A n ->
    bindings_rec G E n A = bindings_rec G (addone E) (S n) A.
Proof with auto.
  intros.
  generalize dependent E.
  induction H;intros;try solve [simpl;auto]...
  -
    simpl.
    rewrite find_add...
  -
    (* all *)
    simpl. f_equal.
    rewrite <- IHWFC1.
    replace ((S (S n), bindings_rec G E n A) :: addone E)
    with (addone ((S n, bindings_rec G E n A) :: E))...
  -
    simpl...
    f_equal...
    assert (bindings_rec G ((S (S n), 1) :: addone E) (S (S n)) A =
            bindings_rec G (addone ((S n, 1)::E)) (S (S n)) A) by auto.
    rewrite H0...
    rewrite <- IHWFC ...
    remember ((bindings_rec G ((S n, 1) :: E) (S n) A)).
    assert ((S (S n), n0) :: addone E = addone ((S n,n0)::E)) by auto.
    rewrite H1.
    rewrite <- IHWFC...
Qed.

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

Lemma close_wfc : forall A X,
    WFC A 0 ->
    WFC (close_tt A X) 0.
Proof with auto.  
  intros A.
  unfold close_tt.
  generalize 0.
  induction A;intros;try solve [dependent destruction H;simpl in *;auto]...
  -
    simpl...
    destruct (a==X)...
Qed.

Lemma WFC_add_one : forall A k,
    WFC A k -> WFC A (S k).
Proof with auto.
  intros.
  induction H...
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

Lemma close_type_wfc: forall A,
    type A -> WFC A 0.
Proof with auto.
  intros.
  induction H;intros...
  - constructor...
    apply WFC_add_one.
    pick fresh X.
    specialize_x_and_L X L.
    apply close_wfc with (X:=X) in H0.
    rewrite <- close_open_reverse in H0...
  - (* WFC_all *)
    constructor...
    apply WFC_add_one.
    pick_fresh X.
    specialize_x_and_L X L.
    apply close_wfc with (X:=X) in H1.
    rewrite <- close_open_reverse in H1...
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


Lemma type_open_tt_WFC :forall T X,
    X \notin fv_tt T ->
    type (open_tt T X) ->
    WFC T 0.
Proof with auto.
  intros.
  apply close_type_wfc in H0.
  apply close_wfc with (X:=X) in H0...
  rewrite <- close_open_reverse in H0... 
Qed.

Lemma WFE_find_in: forall E k,
    WFE E k ->
    forall q n, 0 < n -> 
    q < n ->
    find n E = find (n - q) (minusk E q).
Proof with auto.
  intros E k H.
  induction H;intros...
  remember (n-q).
  assert (minusk ((S k, b) :: E) q = (S k - q, b) :: (minusk E q)) as W by (simpl;auto).
  rewrite W.
  remember (S k - q).
  simpl...
  destruct (n==S k);destruct (n0==n1)...
  lia.
  lia.
  subst.
  apply IHWFE...
Qed.  

Lemma bindings_WFD_drop: forall E n b q G, 
    WFE E n -> q < n - b ->
    bindings_rec G E n b = bindings_rec G (minusk E q) (n - q) b.
Proof with auto.
  induction E;intros...
  dependent destruction H.
  assert (minusk ((S k, b0) :: E) q = (S k - q, b0) :: (minusk E q)) as W1 by (simpl;auto).
  rewrite W1...
  remember (S k - q).
  remember (S k).
  simpl...
  destruct (n-b == n);destruct (n0-b==n0)...
  lia.
  lia.
  subst.
  assert (S k - q - b = (S k - b) - q) as W2 by lia.
  rewrite W2.
  assert (0 < S k - b) as W3 by lia.
  remember (S k - b).
  rewrite <- WFE_find_in with (k:=k)...
Qed.

Lemma bindings_WFD_WFE: forall A k n E q G,
    WFD A k->  WFE E n -> k <= n - q -> q <= n ->
    bindings_rec G E n A = bindings_rec G (minusk E q) (n-q) A.
Proof with auto using WFE_S_n.
  intros.
  generalize dependent E.
  generalize dependent n.
  generalize dependent q.
  induction H;intros;try solve [simpl in *;auto]...
  -
    assert (q < n-b). lia.
    apply bindings_WFD_drop...
  - (* typ_mu *)
    simpl...
    f_equal.
    remember (bindings_rec G ((S (n0 - q), 1) :: minusk E q) (S (n0 - q)) A).
    assert (S (n0 - q) = (S n0) - q) as W by  lia.
    rewrite W.
    assert  ( ((S n0 - q, n1) :: minusk E q) = minusk ((S n0, n1)::E) q) as W2 by (simpl;auto).
    rewrite W2.
    rewrite <- IHWFD...
    f_equal...
    f_equal...
    f_equal...
    f_equal...
    subst.
    rewrite W.
    assert ((S n0 - q, 1) :: minusk E q = minusk ((S n0, 1)::E) q) as W3 by (simpl;auto).
    rewrite W3.
    rewrite <- IHWFD...
    lia.
    lia.
  - (* typ_all *)
    simpl...
    f_equal.
    rewrite <- IHWFD1... f_equal.
    replace (S (n0 - q)) with (S n0 - q) by lia.
    assert  ( ((S n0 - q, bindings_rec G E n0 A) :: minusk E q) = minusk ((S n0, bindings_rec G E n0 A)::E) q) as W2 by (simpl;auto).
    rewrite W2.
    rewrite <- IHWFD2... lia.
Qed.

Lemma find_former: forall (E2 E1:list (nat * nat)) (k:nat),
    (exists p, In (k,p) E1) ->
    find k E1 = find k (E1++E2).
Proof with auto.
  induction E1;intros...
  -
    inversion H...
    inversion H0.
  -
    destruct a.
    destruct H.
    destruct (k==n);subst...
    +
      simpl...
      destruct (n==n)...
      destruct n1...
    +
      simpl.
      destruct (k == n)...
      apply in_inv in H.
      destruct H...
      dependent destruction H...
      destruct n1...
      apply IHE1...
      exists x...
Qed.


Lemma minus_in_for_bindings: forall E ( n k:nat),
    (forall q, exists p, q < n -> In (n - q, p) E) ->
    (forall q, exists p, q < S n -> In (S n - q, p) ((S n, k) :: E)).
Proof with auto.
  intros.
  destruct n.
  -
    destruct q.
    exists k...
    intros.
    simpl...
    exists 0...
    intros.
    lia.
  -
    destruct q...
    exists k.
    intros.
    simpl...
    destruct H with (q:=q)...
    exists x.
    intros.
    assert (S (S n) - S q = S n - q).
    lia.
    rewrite H2.
    apply in_cons...
    apply H0...
    lia.
Qed.    

Lemma bindings_close_env_aux: forall G A k,
    WFD A k->    forall E1 E2 ,
    (forall q, exists p, q < k -> In (k-q,p) E1) -> 
    bindings_rec G (E1++E2) k A = bindings_rec G E1 k A.
Proof with eauto.
  intros G A k H.
  induction H;intros;try solve [simpl in *;auto]...
  -
    simpl...
    assert (find (k - b) E1 = find (k - b) (E1++E2)).
    {
      rewrite find_former with (E2:=E2)...
      destruct H0 with (q:=b)...
    }
    rewrite H1...
  -
    simpl.
    f_equal.
    remember (bindings_rec G ((S n, 1) :: E1 ++ E2) (S n) A).
    rewrite_env (((S n, n0) :: E1) ++ E2).
    rewrite IHWFD...
    subst.
    rewrite_env (((S n, 1) :: E1) ++ E2).
    rewrite IHWFD...
    intros.
    apply minus_in_for_bindings...
    intros.
    apply minus_in_for_bindings...
  -
    simpl. f_equal.
    rewrite IHWFD1... f_equal.
    remember (bindings_rec G E1 n A).
    rewrite_env (((S n, n0) :: E1) ++ E2).
    rewrite IHWFD2...
    intros.
    apply minus_in_for_bindings...
Qed.


Lemma bindings_close_env: forall A E G,
    type A-> 
    bindings_rec G E 0 A = bindings_rec G nil 0 A.
Proof with eauto.
  intros.
  rewrite_env (nil++E).
  rewrite_env (nil ++ empty_menv).
  apply bindings_close_env_aux...
  apply close_type_wfd...
  intros.
  exists 0.
  intros.
  lia.
Qed.

Lemma bindings_local_close: forall B E n G,
  type B -> WFE E n ->
  bindings_rec G E n B = bindings_rec G nil 0 B.
Proof with auto.
  intros.
  rewrite bindings_WFD_WFE with (k:=0) (q:=n)...
  assert (0=n-n ) by lia.
  rewrite <- H1.
  rewrite bindings_close_env...
  apply close_type_wfd...
  lia.
Qed.


Lemma bindings_close : forall B a G E n,
    type B -> WFE E n ->
    bindings_rec G E n B = bindings_rec G ((S n, a) :: E) (S n) B.
Proof with auto.
  intros.
  rewrite bindings_local_close...
  remember (bindings_rec G empty_menv 0 B).
  rewrite bindings_local_close...
  apply WFE_S_n...
Qed.  

Lemma bindings_rec_ge_1: forall G E n A,
  bindings_rec G E n A >= 1.
Proof.
  intros. revert E n.
  induction A;intros;simpl;try solve[lia]...
Qed.


Lemma findX_extend: forall Q G E X T n,
  WFD Q n ->
  X \notin fv_tt Q ->
  WFE E n ->
  bindings_rec (mk_benv G) E n Q = 
  bindings_rec (mk_benv (X ~ T ++ G)) E n Q.
Proof with auto.
  intros. generalize dependent E.
  induction H;try solve [simpl in H0;simpl;intros;auto];intros...
  - simpl. destruct T...
    simpl. destruct (X0==X)...
    subst. exfalso.
    apply H0. simpl...
  - simpl. f_equal. destruct T...
    rewrite IHWFD... 2:{ constructor... apply WFE_find_none... }
    simpl. f_equal. f_equal. f_equal.
    rewrite IHWFD... { constructor... apply WFE_find_none... }
  - simpl. f_equal. destruct T... simpl in H0.
    rewrite IHWFD1... f_equal.
    rewrite IHWFD2... { constructor... apply WFE_find_none... }
Qed.   


Lemma findX_extend_spec: forall Q E X T,
  type Q ->
  X \notin fv_tt Q ->
  bindings_rec (mk_benv E) nil 0 Q = 
  bindings_rec (mk_benv (X ~ T ++ E)) nil 0 Q.
Proof with auto.
  intros.
  apply findX_extend...
  apply close_type_wfd...
Qed.


Lemma findX_sem: forall E X Q,
  wf_env E ->
  binds X (bind_sub Q) E ->
  findX X (mk_benv E) = Some (bindings_rec (mk_benv E) nil 0 Q).
Proof with auto.
  induction E.
  - intros. inversion H0.
  - intros. destruct H0.
    + destruct a. inversion H0;subst.
      simpl. rewrite eq_dec_refl.
      f_equal. rewrite_alist (mk_benv (X ~ bind_sub Q ++ E)).
      apply findX_extend_spec...
      { inversion H;subst. apply WF_type in H5... }
      rewrite_env (nil ++ X ~ bind_sub Q ++ E) in H.
      apply notin_from_wf_env in H...
    + destruct a. simpl. destruct b...
      * simpl. destruct (X == a)...
        { subst. inversion H;subst.
          exfalso. apply H6.
          apply in_split in H0. destruct H0 as [E1 [E2 H1]].
          rewrite H1. rewrite dom_app. simpl... }
        { rewrite IHE with (Q:= Q)... 2:{ inversion H... }
          rewrite_alist (mk_benv (a ~ bind_sub t ++ E)). f_equal.
          apply findX_extend_spec...
          { inversion H;subst. apply in_split in H0. destruct H0 as [? [? ?]].
            rewrite H0 in H4. apply WF_from_binds_typ_strong in H4.
            apply WF_type in H4... }
          { rewrite_env (nil ++ a ~ bind_sub t ++ E) in H.
            apply notin_from_wf_env in H.
            assert (binds X (bind_sub Q) E)...
            apply notin_fv_tt_fv_env with (E:=E) (Y:=X)...
          }
        }
      * inversion H...
Qed.


Lemma bindings_find: forall A G E1 E2 B,
    find zero (E1++E2) = None ->
    type B ->
    WFC A 0 ->
    WFE (E1++E2)  0 ->
    (bindings_rec G (E1++E2) 0 (open_tt A B)) =
    bindings_rec G (E1 ++ (zero, (bindings_rec G (E1++E2) 0 B) - 1) :: E2) 0 A.
Proof with auto.
  intro A.
  unfold open_tt. remember 1 as one.
  generalize 0.
  unfold zero. subst one.
  induction A;intros;try solve [dependent destruction H1;simpl;auto]...
  - destruct (n0==n);subst...
    +
      assert (open_tt_rec n B n = B) as Q.
      {
        simpl...
        destruct (n==n)...
        destruct n0...
      }
      rewrite Q.
      simpl.
      rewrite Nat.sub_diag.
      rewrite bindings_find_in...
      pose proof bindings_rec_ge_1 G (E1 ++ E2) n B.
      lia.
    +
      assert (open_tt_rec n0 B n = n) as Q.
      {
        simpl...
        destruct (n0==n)...
        destruct e...
        destruct n1...
      }
      rewrite Q.
      simpl.
      dependent destruction H1.
      apply neq_minus in H1...
      destruct H1...
      rewrite H1.
      erewrite <- bindings_find_notin... 
  - (* all *)
    dependent destruction H1.
    simpl. f_equal.
    rewrite IHA1... f_equal.
    remember ((S n,
    bindings_rec G (E1 ++ (0, bindings_rec G (E1 ++ E2) n B - 1) :: E2) n A1)) as R1.
    assert (bindings_rec G (E1++E2) n B = bindings_rec G (R1 :: E1++E2) (S n) B) as Q1.
    subst.
    apply bindings_close...
    rewrite Q1.    
    rewrite_alist ((R1 :: E1) ++ (0, bindings_rec G ((R1 :: E1) ++ E2) (S n) B - 1) :: E2).
    rewrite <- IHA2...
    rewrite_alist (R1 :: E1 ++E2)...
    subst...
    rewrite_env (R1 :: E1 ++ E2).
    subst.
    apply WFE_S_n...

  -
    dependent destruction H1...
    simpl.
    f_equal.
    remember (S n, 
      (bindings_rec G
         ((S n, 1) :: E1 ++ (0, bindings_rec G (E1 ++ E2) n B - 1) :: E2) 
         (S n) A)) as R1.
    assert (bindings_rec G (E1++E2) n B = bindings_rec G (R1 :: E1++E2) (S n) B) as Q1.
    subst.
    apply bindings_close...
    rewrite Q1.
    rewrite_alist ((R1 :: E1) ++ (0, bindings_rec G ((R1 :: E1) ++ E2) (S n) B - 1) :: E2).
    rewrite <- IHA...
    f_equal...
    remember (bindings_rec G ((S n, 1) :: E1 ++ E2) (S n) (open_tt_rec (S n) B A)) as R2.
    rewrite_alist (R1 :: E1 ++ E2).
    f_equal.
    subst.
    f_equal...
    (* f_equal. *)
    assert (bindings_rec G (E1++E2) n B = bindings_rec G (((S n, 1) :: E1)++E2) (S n) B) as Q2.
    apply bindings_close...
    rewrite Q2.
    rewrite_alist (((S n, 1) :: E1) ++ (0, bindings_rec G (((S n, 1) :: E1) ++ E2) (S n) B - 1) :: E2).
    rewrite <- IHA...
    rewrite_env ((S n, 1) :: E1 ++ E2).
    apply WFE_S_n...
    rewrite_alist (R1 :: E1 ++E2)...
    subst...
    rewrite_env (R1 :: E1 ++ E2).
    subst.
    apply WFE_S_n...
Qed.

Lemma bindings_find_spec: forall A G E B,
  find zero E = None ->
  type B ->
  WFC A 0 ->
  WFE E 0 ->
  bindings_rec 
    (mk_benv G) E 0 (open_tt A B) =
  bindings_rec 
    (mk_benv G) ((zero, (bindings_rec (mk_benv G) E 0 B - 1)) :: E) 0 A.
Proof with auto.
  intros. 
  rewrite_env (nil ++ (zero, (bindings_rec (mk_benv G) E 0 B - 1)) :: E).
  rewrite_env (nil ++ E).
  apply bindings_find...
Qed.

(* minus one because we add one to each lookup *)
Lemma bindings_find_spec': forall A G B,
  type B ->
  WFC A 0 ->
  bindings_rec 
    (mk_benv G) empty_menv 0 (open_tt A B) =
  bindings_rec 
    (mk_benv G) ((1, (bindings_rec (mk_benv G) empty_menv 0 B - 1)) :: empty_menv) 1 A.
Proof with auto.
  intros.
  rewrite bindings_find_spec...
  rewrite bindings_add...
Qed.



Lemma bindings_fvar: forall A G E1 E2 X B,
    WFC A 0 ->
    X \notin fv_tt A ->
    wf_env (X ~ bind_sub B ++ G) ->
    find zero (E1++E2) = None ->
    type B ->
    WFE (E1 ++ E2) 0 ->
    bindings_rec (mk_benv (X ~ bind_sub B ++ G)) (E1 ++ E2) 0 (open_tt A X) =
    bindings_rec (mk_benv G)
    (E1 ++ [(zero, bindings_rec (mk_benv G) (E1 ++ E2) 0 B )] ++ E2) 0 A.
Proof with auto.
  intro A.
  unfold open_tt.
  generalize 0.
  unfold zero.
  induction A;intros;try solve [dependent destruction H;simpl;auto]...

  - 
    destruct (n0==n);subst...
    +
      assert (open_tt_rec n X n = X) as Q.
      {
        simpl...
        destruct (n==n)...
        destruct n0...
      }
      rewrite Q.
      simpl. destruct (X == X)... 2:{ exfalso... }
      rewrite Nat.sub_diag.
      rewrite bindings_find_in...
      rewrite <- bindings_local_close with (E:=E1 ++ E2) (n:=n)...
    
    +
      assert (open_tt_rec n0 X n = n) as Q.
      {
        simpl...
        destruct (n0==n)...
        destruct e...
        destruct n1...
      }
      rewrite Q.
      simpl.
      dependent destruction H.
      apply neq_minus in H...
      destruct H...
      rewrite H.
      erewrite <- bindings_find_notin...
      
  -
    simpl. destruct (a == X)...
    subst X. exfalso. apply H0... simpl...
  
  -
    simpl.
    dependent destruction H. simpl in H1.
    simpl in IHA1. rewrite IHA1...
    simpl in IHA2. rewrite IHA2...

  -
    simpl.
    dependent destruction H. simpl in H1.
    simpl in IHA1. rewrite IHA1... f_equal. f_equal.

    remember (bindings_rec (mk_benv G) (E1 ++ (0, bindings_rec (mk_benv G) (E1 ++ E2) n B) :: E2) n A1) as K.

    rewrite_env (
      ((S n, K)
      :: E1) ++ E2
    ).
    simpl in IHA2. rewrite IHA2 at 1...

    2:{ constructor... apply WFE_find_none... }

    rewrite_alist ((S n, K) :: (E1 ++ E2)).
    rewrite <- bindings_close with (B:=B)...

  -
    simpl.
    dependent destruction H. simpl in H0.
    f_equal.

    remember ((bindings_rec ((X, bindings_rec (mk_benv G) empty_menv 0 B) :: mk_benv G) ((S n, 1) :: E1 ++ E2) (S n) (open_tt_rec (S n) X A))) as K1.

    remember (
    (bindings_rec (mk_benv G)
       ((S n, 1) :: E1 ++ (0, bindings_rec (mk_benv G) (E1 ++ E2) n B) :: E2)
       (S n) A))  as K2.


    rewrite_env (
      ((S n, K1)
      :: E1) ++ E2
    ). simpl in IHA. rewrite IHA...
    2:{ constructor... apply WFE_find_none... }


    rewrite_alist ((S n, K1) :: (E1 ++ E2)).
    rewrite <- bindings_close with (B:=B)... simpl.
    f_equal. f_equal. f_equal. subst K1 K2.
    (* f_equal. *)

    rewrite_alist (((S n, 1) :: E1) ++ E2).
    rewrite IHA...
    2:{ constructor... apply WFE_find_none... }


    rewrite_alist ((S n, 1) :: (E1 ++ E2)).
    rewrite <- bindings_close with (B:=B)...
    
    
  - simpl. f_equal. simpl in IHA. simpl in H0.
    rewrite IHA... inversion H...
  -
    inversion H;subst. simpl in H0.
    simpl. f_equal. simpl in IHA1. simpl in IHA2.
    rewrite IHA1... 
Qed.



Lemma bindings_fvar_spec: forall G A X B,
    WFC A 0 ->
    X \notin fv_tt A ->
    wf_env (X ~ bind_sub B ++ G) ->
    (* find zero (E1++E2) = None -> *)
    type B ->
    bindings_rec (mk_benv (X ~ bind_sub B ++ G)) empty_menv 0 (open_tt A X) =
    bindings_rec (mk_benv G)
    ((1, bindings_rec (mk_benv G) empty_menv 0 B ) :: empty_menv) 1 A.
Proof with auto.
  intros.
  rewrite_env (X ~ bind_sub B ++ G).
  rewrite_env (empty_menv ++ empty_menv).
  rewrite bindings_fvar...
  { simpl. rewrite bindings_add... }
Qed.

Lemma binds_key_dec: forall (E: env) X,
  {Q | binds X Q E} + {forall Q, ~ binds X Q E}.
Proof with auto.
induction E...
intros.
destruct a.
destruct (X==a)...
-
  subst. left. exists b. simpl...
-
  destruct IHE with (X:=X)...
  + destruct s. left. exists x. simpl...
  + right. intros. intros C. destruct C.
    * inversion H...
    * apply n0 with (Q:=Q)...
Qed.


Lemma WFC_WFD_S : forall A k,
    WFC A k -> WFD A (S k).
Proof with auto.
  intros.
  induction H...
  constructor. lia.
Qed.

Inductive sub_menv: menv -> menv -> Prop :=
| sub_menv_nil : sub_menv empty_menv empty_menv
| sub_menv_cons : forall n v1 v2 R1 R2,
    v1 <= v2 ->
    sub_menv R1 R2 ->
    sub_menv ((n, v1) :: R1) ((n, v2) :: R2).

Hint Constructors sub_menv : core.

Lemma sub_menv_find : forall R1 R2 n,
  sub_menv R1 R2 ->
  match find n R1 with
| Some k => k
| None => 1
  end <= match find n R2 with
       | Some k => k
       | None => 1
  end.
Proof with auto.
  intros.
  induction H.
  - simpl...
  - simpl in *. destruct (n == n0)...
Qed.

Lemma sub_menv_sem: forall G R1 R2 n A,
  sub_menv R1 R2 ->
  bindings_rec G R1 n A <= bindings_rec G R2 n A.
Proof with auto.
  intros. revert n R1 R2 H.
  induction A;intros...
  - simpl. apply le_n_S. apply sub_menv_find...
  - simpl. specialize (IHA1 n _ _ H).
    specialize (IHA2 n _ _ H). lia.
  - simpl.
    specialize (IHA1 n _ _ H).
    assert (sub_menv
      ((S n, (bindings_rec G R1 n A1)) :: R1)
      ((S n, (bindings_rec G R2 n A1)) :: R2)).
    { constructor... }
    specialize (IHA2 (S n) _ _ H0).
    lia.
  - simpl.
    assert (sub_menv ((S n, 1) :: R1) ((S n, 1) :: R2))...
    pose proof IHA (S n) _ _ H0.
    assert (sub_menv
    (((S n, (bindings_rec G ((S n, 1) :: R1) (S n) A)) :: R1))
    (((S n, (bindings_rec G ((S n, 1) :: R2) (S n) A)) :: R2))
    )...
    pose proof IHA (S n) _ _ H2. lia.
  - simpl. specialize (IHA n _ _ H). lia.
  - simpl. specialize (IHA1 n _ _ H). specialize (IHA2 n _ _ H).
    lia.
Qed.


Ltac solve_right_dec := right;intro v;inversion v;try inv_rt;auto.


Lemma WFC_dec : forall m A,
  {WFC A m} + {~ WFC A m}.
Proof with auto.
  intros. revert m.
  induction A;intros...
  - destruct (le_gt_dec n m)...
    right. intros C. inversion C;lia.
  - destruct (IHA1 m); try solve [solve_right_dec].
    destruct (IHA2 m); try solve [solve_right_dec]...
  - destruct (IHA1 m); try solve [solve_right_dec].
    destruct (IHA2 (S m)); try solve [solve_right_dec]...
  - destruct (IHA (S m)); try solve [solve_right_dec]...
  - destruct (IHA m); try solve [solve_right_dec]...
  - destruct (IHA1 m); try solve [solve_right_dec].
    destruct (IHA2 (m)); try solve [solve_right_dec]...
Qed.

Lemma wf_fvar_dec: forall E (a:atom), 
  uniq E ->
  {WF E a} + {~ WF E a}.
Proof with auto.
  intros.
  pose proof binds_key_dec E a.
  destruct H0.
  { destruct s. destruct x.
    * left. apply WF_var with (U:=t)...
    * right. intros C. inversion C;subst.
      pose proof binds_unique _ _ _ _ _ b H2 H.
      inversion H0.
  }
  { right. intros C.
    inversion C;subst.
    apply n with (Q:=bind_sub U)...
  }
Qed.



Lemma findX_notin: forall G X,
    X \notin dom G ->
    findX X G = None.
Proof with auto.
  induction G;intros...
  simpl in *.
  destruct a.
  destruct (X==a)...
  apply notin_add_1 in H.
  destruct H...
Qed.  

Lemma rt_type_dec: forall A,
  { rt_type A } + { ~ rt_type A }.
Proof with auto.
  intros. destruct A;try solve [left;constructor|right;intros C;inversion C].
Qed.

Lemma collectLabelDec: forall i A,
  { i `in` collectLabel A } + { i `notin` collectLabel A }.
Proof with auto.
  intros. induction A;try solve [right;simpl;apply notin_empty_1].
  - simpl. destruct IHA2.
    + left. apply union_iff. right...
    + destruct (i == a)...
Qed.


Lemma wf_dec_aux : forall G k A E,
  uniq E -> 
  (* new constraint,
    to show (binds a typ) -> (binds a sub) -> False

    uniq should be decidable, indeed
  *)
    bindings_rec G nil 0 A <= k ->
    {WF E A} + {~ WF E A}.
Proof with auto.
  induction k.
  -
    induction A;intros;try solve [simpl in *;exfalso;lia]...
(*     
    + (* bvar *)
      right. intros C. inversion C.
    + (* fvar *)
      apply wf_fvar_dec...
       *)
  -
    unfold bindings in *.
    induction A;intros;try solve [ solve_right_dec]...
    + (* fvar *)
      apply wf_fvar_dec...
    
    + (* arrow *)     
      simpl in H0.
      destruct IHA1 with (E:=E);destruct IHA2 with (E:=E);try solve [lia|solve_right_dec]...

    + (* all *)
      simpl in H0.
      destruct IHA1 with (E:=E);try solve [lia|solve_right_dec]...
      assert (type A1). { apply WF_type with (E:=E)... }
      destruct (WFC_dec 0 A2).
      2:{ right. intros C. apply WF_type in C.
          inversion C;subst. apply n.
          pick_fresh X.
          apply type_open_tt_WFC with (X:=X)... }

      pick fresh X.
      remember (open_tt A2 X) as Q1.
      destruct IHk with (A:=Q1) (E:= X ~ bind_sub A1 ++ E)...
      { subst. rewrite_alist (empty_menv ++ empty_menv).
        rewrite bindings_find...
        rewrite bindings_add... unfold zero. simpl.
        simpl.
        
        eapply le_trans.
        { apply sub_menv_sem with 
            (R2:=((1, bindings_rec G empty_menv 0 A1) :: empty_menv)). 
          constructor...
          rewrite findX_notin...
          simpl.
          apply bindings_rec_ge_1. }
        lia.
      }
      * (* A2 is well formed *)
        left. apply WF_all with (L:={{X}} \u fv_tt A2 \u dom E)...
        intros. subst Q1.
        apply WF_replacing_var with (X:=X)...

      * (* A2 is not well formed *)
        right. intros C. apply n. subst Q1.
        dependent destruction C. pick_fresh Y.
        specialize_x_and_L Y L.
        apply WF_replacing_var with (X:=Y)...

    + (* mu *)
      simpl in H0.

      destruct (WFC_dec 0 A).
      2:{ right. intros C. apply WF_type in C.
          inversion C;subst. apply n.
          pick_fresh X.
          apply type_open_tt_WFC with (X:=X)... }

      pick fresh X.
      remember (open_tt A X) as Q1.
      remember (open_tt A (typ_label X (open_tt A X))) as Q2.
      destruct IHk with (A:=Q1) (E:= X ~ bind_sub typ_top ++ E)...
      { subst. rewrite_alist (empty_menv ++ empty_menv).
        rewrite bindings_find...
        rewrite bindings_add... unfold zero. simpl.
        rewrite findX_notin...
        simpl.
        eapply le_trans.
        { apply sub_menv_sem with 
            (R2:=((1, (bindings_rec G ((1, 1) :: empty_menv) 1 A)) :: empty_menv)). 
          constructor...
          apply bindings_rec_ge_1. }
        lia. }
      
      * (* open_tt A X is well-formed  *)
        destruct IHk with (A:=Q2) (E:= X ~ bind_sub typ_top ++ E)...
        { subst. rewrite_alist (empty_menv ++ empty_menv).
          rewrite bindings_find...
          2:{ apply WF_type in w0... }
          simpl.
          replace (bindings_rec G empty_menv 0 (open_tt A X))
          with (bindings_rec G ((1,  match findX X G with
          | Some k => k | None => 1 end )::empty_menv) 1 A).
          2:{ rewrite_alist (empty_menv ++ empty_menv).
            rewrite bindings_find... simpl.
            rewrite bindings_add with (n:=0)... unfold zero...
            rewrite Nat.sub_0_r... }
          rewrite bindings_add with (n:=0)...
          simpl. unfold zero.
          apply le_S_n in H0.
          eapply le_trans. 2:{ apply H0. }
          apply sub_menv_sem.
          constructor...
          rewrite findX_notin...
          lia. }
        
          ** (*  A [X |-> {x: A}] is well-formed *)
           left. subst Q1 Q2.
           apply WF_rec with (L:={{X}} \u fv_tt A \u dom E \u fl_tt A);intros...
           apply WF_replacing_var with (X:=X)...

           apply WF_replacing' with (Y:=X0) in w1...
           rewrite subst_tt_open_tt in w1... simpl in w1.
           rewrite subst_tt_open_tt in w1... simpl in w1.
           rewrite eq_dec_refl in w1.
           rewrite <- subst_tt_fresh in w1...
           (* stuck: how to get 
           WF (X0 ~ bind_sub typ_top ++ E) 
              (open_tt A (typ_label X0 (open_tt A X0)))

           from 

           WF ((X0, bind_sub typ_top) :: E)
             (open_tt A (typ_label X (open_tt A X0)))           
            *)
           apply WF_renaming_tl with (X:=X) (Y:=X0) in w1...
           rewrite label_transform in w1...
           solve_notin.
        ** (* A [X |-> {x: A}] is not well-formed *)
           right. intros C. apply n. subst Q1 Q2.
           inversion C;subst.
           pick_fresh Y.
           specialize_x_and_L Y L.
           apply WF_renaming_unfolding with (X:=Y)...
           (* Same issue as above case *)
      
      * (* open_tt A X is not well-formed *)
        right. intros C. apply n. subst Q1.
        inversion C. subst.
        pick_fresh Y.
        specialize_x_and_L Y L.
        apply WF_replacing_var with (X:=Y)...
    
  + (* label *)
    simpl in H0.
    destruct IHA with (E:=E);try solve [lia|solve_right_dec]...

  + (* rcd *)
    simpl in H0.
    destruct IHA1 with (E:=E);try solve [lia|solve_right_dec]...
    destruct IHA2 with (E:=E);try solve [lia|solve_right_dec]...
    destruct (rt_type_dec A2);try solve [lia|solve_right_dec]...
    destruct (collectLabelDec a A2);try solve [lia|solve_right_dec]...
Qed.


Lemma wf_dec : forall  A E,
  uniq E -> 
    {WF E A} + {~ WF E A}.
Proof with auto.
  intros.
  apply wf_dec_aux with (k:=bindings_rec nil nil 0 A) (G:=nil)...
Qed.



Lemma binds_key_dom_dec: forall (E: env) X,
  {X \in dom E} + {X \notin dom E}.
Proof with auto.
induction E...
intros.
destruct a.
destruct (X==a)...
-
  subst. left. simpl...
-
  destruct IHE with (X:=X)...
  left. simpl...
Qed.

Lemma wf_env_dec: forall E,
    {wf_env E} + {~wf_env E}.
Proof with auto.  
  induction E...
  destruct IHE.
  -
    pose proof wf_dec.
    assert (Ht:=w).
    apply uniq_from_wf_env in Ht.
    pose proof binds_key_dom_dec.
    destruct a.
    destruct b.
    +
      destruct H with (E:=E) (A:=t)...
      destruct H0 with (E:=E) (X:=a)...
      *
        right.
        intros v.
        dependent destruction v...
      *
        left.
        constructor...
      *
        right.
        intros v.
        dependent destruction v...
    +
      destruct H with (E:=E) (A:=t)...
      destruct H0 with (E:=E) (X:=a)...
      *
        right.
        intros v.
        dependent destruction v...
      *
        left.
        constructor...
      *
        right.
        intros v.
        dependent destruction v...
  -
    right.
    intros v.
    dependent destruction v;
      apply n...
Qed.


Ltac solve_top_dec E := 
  pose wf_env_dec as Q;destruct Q with (E:=E) as [Ql|Qr];try solve [
  left;auto |
  solve_right_dec  ].
Ltac solve_top_wfs_dec E A := 
  match goal with
  | H : wf_env E |- _ =>    
    destruct (wf_dec A (uniq_from_wf_env H)); 
    try solve [left;auto|right;intros v;dependent destruction v;auto]
  | _ => idtac
  end.

Lemma find_var_one: forall Q G X E n,
  X \notin dom G ->
  bindings_rec ( G) E n Q = 
  bindings_rec (X ~ 1 ++  G) E n Q.
Proof with auto.
  intros Q G X.
  induction Q;intros...
  + simpl. destruct (a == X)...
    subst.
    rewrite (findX_notin _ H)...
  + simpl. rewrite IHQ1...
  + simpl. rewrite IHQ1...
  + simpl. rewrite IHQ...
    f_equal. f_equal. f_equal.
    f_equal. rewrite IHQ...
  + simpl...
  + simpl. rewrite IHQ1...
Qed.

Lemma mk_benv_dom: forall X G,
  X `notin` dom G -> X `notin` dom (mk_benv G).
Proof with auto.
  induction G;intros...
  + intros. destruct a. simpl. destruct b...
Qed.

Lemma bindings_drop_label: forall T E G t i,
WF E T ->
Tlookup i T = Some t ->
S (bindings_rec (mk_benv E) G 0 t + bindings_rec (mk_benv E) G 0 (dropLabel i T)) =
bindings_rec (mk_benv E) G 0 T.
Proof with auto.
  intros T.
  induction T;intros;try solve [inversion H0]...
  + simpl. simpl in H0. destruct (a == i).
    * inversion H0. subst. inversion H;subst...
      rewrite dropLable_notin with (E:=E)...
    * inversion H;subst...
      rewrite <- IHT2 with (t:=t) (i:=i)...
      simpl. lia.
Qed.

Lemma subset_dec: forall A B, { A [<=] B} + { ~ A [<=] B}.
Proof with auto.
  intros. destruct (AtomSetImpl.subset A B) eqn:E'.
  + apply subset_iff in E'...
  + right. intros C. apply subset_iff in C...
    rewrite C in E'. inversion E'.
Qed.



Lemma equiv_trans: forall E P Q R,
  equiv E P Q -> equiv E Q R -> equiv E P R.
Proof.
  intros.
  destruct H. destruct H0.
  split;apply sub_transitivity with (Q:=Q);auto.
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


Lemma equiv_rcd_proper: forall E a T1 T2 T1' T2',
  equiv E T1 T1' ->
  equiv E T2 T2' -> 
  rt_type T2 -> rt_type T2' ->
  a `notin` collectLabel T2 ->
  equiv E (typ_rcd_cons a T1 T2) (typ_rcd_cons a T1' T2').
Proof with auto.
  intros. destruct H as [H H'], H0 as [H0 H0'].
  split.
  { apply sub_rcd_proper... }
  { apply sub_rcd_proper...
    inversion H0;subst;inv_rt...
  }
Qed.


Lemma sub_rcd_first_permute: forall E a b T1 T2 T3,
  wf_env E -> WF E  (typ_rcd_cons a T1 (typ_rcd_cons b T2 T3)) ->
  sub E (typ_rcd_cons a T1 (typ_rcd_cons b T2 T3)) 
  (typ_rcd_cons b T2 (typ_rcd_cons a T1 T3)).
Proof with auto.
  intros.
  { apply sa_rcd...
    + simpl. rewrite <- !KeySetProperties.union_assoc.
      rewrite KeySetProperties.union_sym with (s:= singleton a). reflexivity.
    + inversion H0;subst. inversion H6;subst.
      constructor... 2:{ simpl in H8... }
      constructor... { simpl in H8 ... }
    + intros. simpl in H1, H2.
      assert (a <> b). { inversion H0;subst. simpl in H10... }
      destruct (a==i), (b==i);try inversion H1; try inversion H2;subst...
      * congruence.
      * apply Reflexivity... inversion H0...
      * apply Reflexivity... inversion H0... inversion H9...
      * assert (t1 = t2) by congruence. subst.
        apply Reflexivity... apply wf_rcd_lookup with (E:=E) in H1...
        inversion H0... inversion H11...
  }
Qed.


Lemma equiv_rcd_first_permute: forall E a b T1 T2 T3,
  wf_env E -> WF E  (typ_rcd_cons a T1 (typ_rcd_cons b T2 T3)) ->
  equiv E (typ_rcd_cons a T1 (typ_rcd_cons b T2 T3)) 
  (typ_rcd_cons b T2 (typ_rcd_cons a T1 T3)).
Proof with auto.
  intros.
  split.
  { apply sub_rcd_first_permute... }
  { apply sub_rcd_first_permute...
    inversion H0;subst.
    inversion H6;subst.
    constructor... 2:{ simpl in H8... }
    constructor... { simpl in H8 ... }
  }
Qed.



Lemma record_permutation_exists:
  forall j E T,
  wf_env E -> 
  j `in` collectLabel T ->
  { A' |
    equiv E (typ_rcd_cons j A' ((dropLabel j T))) T} + {~ WF E T}.
Proof with auto.
  intros.
  induction T;try solve [apply empty_iff in H0;destruct H0].
  - simpl in H0.
    destruct (Atom.eq_dec j a).
    + subst j. 
      solve_top_wfs_dec E (typ_rcd_cons a T1 T2).
      left. exists T1.
      rewrite dropLabel_first_element with (E:=E)...
      apply equiv_reflexivity...
    + solve_top_wfs_dec E (typ_rcd_cons a T1 T2).
      destruct (collectLabelDec j T2).
      2:{ assert (j `notin` union (singleton a) (collectLabel T2))... }
      destruct (IHT2 i);try solve [solve_right_dec].
      left. destruct s. exists x.
      simpl. destruct (a ==j);try solve [exfalso;auto]...
      apply equiv_trans with 
        (Q:= (typ_rcd_cons a T1 (typ_rcd_cons j x (dropLabel j T2)))).
      * apply equiv_rcd_first_permute...
        { destruct e. get_well_form.
          inversion H5;subst.
          inversion w;subst. constructor...
          constructor... apply notin_drop_collect... } 
      * apply equiv_rcd_proper...
        { apply equiv_reflexivity...
          { inversion w;subst... }
        }
        { inversion w;subst... }
        { simpl. solve_notin. apply notin_drop_collect...
          inversion w... }
Qed.

Lemma equiv_measure: forall A,
  type4rec A -> forall B, type4rec B -> forall E,
  sub E A B -> sub E B A ->
  bindings_rec (mk_benv E) nil 0 A = bindings_rec (mk_benv E) nil 0 B.
Proof with auto.
  intros A HA;induction HA.
  - intros B HB;induction HB;intros;
    try solve [simpl; lia| inversion H;inv_rt|inversion H0;inv_rt|
    inversion H1;inv_rt|
      inversion H2;inv_rt|inversion H3;inv_rt].
  - intros B HB;induction HB;intros;
  try solve [simpl; lia| inversion H;inv_rt|inversion H0;inv_rt|
  inversion H1;inv_rt|
    inversion H2;inv_rt|inversion H3;inv_rt].
  - intros B HB;induction HB;intros;
  try solve [simpl; lia| inversion H;inv_rt|inversion H0;inv_rt|
  inversion H1;inv_rt|
    inversion H2;inv_rt|inversion H3;inv_rt| inversion H4;inv_rt].
    apply suba_sub_tvar_chain in H.
    apply suba_sub_tvar_chain in H0.
    destruct H as [W1], H0 as [W2].
    pose proof sub_tvar_chain_antisym H H0. subst. lia.
  - intros. dependent destruction H0.
    { dependent destruction H2. inv_rt. }
    2:{ inv_rt. }
    dependent destruction H1.
    2:{ inv_rt. }
    simpl. 
    rewrite IHHA1 with (B:=B1)...
    2:{ apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
    rewrite IHHA2 with (B:=B2)...
    { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
  - intros. rename T into A1.
    dependent destruction H4.
    { dependent destruction H6. inv_rt. }
    2:{ inv_rt. }
    dependent destruction H7.
    2:{ inv_rt. }
    dependent destruction H3.
    pick_fresh X.
    specialize_x_and_L X L.
    specialize_x_and_L X L0.
    specialize_x_and_L X L1.
    specialize_x_and_L X L2.


    assert (Eh1: sub (X ~ bind_sub typ_top ++ E) (open_tt A1 X) (open_tt A2 X)).
    { apply sub_nominal_inversion... }
    assert (Eh2: sub (X ~ bind_sub typ_top ++ E) (open_tt A2 X) (open_tt A1 X)).
    { apply sub_nominal_inversion... }
    simpl.

    specialize (H2 _ H4 ((X ~ bind_sub typ_top) ++ E) Eh1 Eh2).
    assert (WFC A2 0).
    { apply type_open_tt_WFC with (X:=X)... 
        apply type4rec_to_type... }
    assert (WFC A1 0).
    { apply type_open_tt_WFC with (X:=X)... 
        apply type4rec_to_type... }


    rewrite_env (empty_menv ++ empty_menv) in H2...
    pose proof H2 as H2'. simpl in H2'.
    rewrite bindings_find in H2... 
    rewrite bindings_add in H2... 
    rewrite bindings_find in H2... 
    rewrite bindings_add with (A:=A2) in H2... 
    unfold zero in H2. simpl in H2. rewrite eq_dec_refl in H2.
    replace (1-0) with 1 in H2...
    rewrite_env (X ~ 1 ++ mk_benv E) in H2.
    rewrite <- find_var_one with (X:=X) in H2...
    2:{ apply mk_benv_dom... }
    rewrite <- find_var_one with (X:=X) in H2...
    2:{ apply mk_benv_dom... }
    rewrite H2. f_equal...



    specialize (H0 _ H3 ((X ~ bind_sub typ_top) ++ E) H7 H10).

    rewrite_env (empty_menv ++ empty_menv) in H0...
    rewrite bindings_find in H0... 
    rewrite bindings_add in H0... 
    rewrite bindings_find in H0... 
    rewrite bindings_add with (A:=A2) in H0... 
    unfold zero in H0. simpl in H0. rewrite H2' in H0.
    rewrite_env (X ~ 1 ++ mk_benv E) in H0.
    rewrite <- find_var_one with (X:=X) in H0...
    2:{ apply mk_benv_dom... }
    rewrite <- find_var_one with (Q:=A2) (X:=X) in H0...
    2:{ apply mk_benv_dom... }
    rewrite <- find_var_one with (X:=X) in H0...
    2:{ apply mk_benv_dom... }

    rewrite_env (empty_menv ++ empty_menv) in H0...
    rewrite bindings_find in H0...
    replace (bindings_rec (mk_benv E) (empty_menv ++ empty_menv) 0 X) with 2 in H0.
    2:{ simpl. rewrite findX_notin... apply mk_benv_dom... }
    simpl in H0. rewrite bindings_add with (A:=A2) in H0...
    simpl in H0. unfold zero in H0. rewrite Nat.sub_0_r in H0...

constructor. apply WF_type with (E:=X ~ bind_sub typ_top ++ E)...
constructor. apply WF_type with (E:=X ~ bind_sub typ_top ++ E)...


- 
  intros.
  dependent destruction H2.
  { dependent destruction H4. inv_rt. }
  2:{ inv_rt. }
  dependent destruction H3.
  2:{ inv_rt. }
  rename T2 into S1. rename S2 into T2.
  rename T3 into S2.
  inversion H1;subst.
  pick_fresh X.
  specialize_x_and_L X L.
  specialize_x_and_L X L0.
  specialize_x_and_L X L1.
  specialize_x_and_L X L2.
  specialize (IHHA _ H6 E H2_ H2_0).
  simpl. rewrite IHHA. f_equal. f_equal.

  rewrite_env (nil ++ X ~ bind_sub T1 ++ E) in H3.
  apply sub_narrowing with (P:=T2) in H3...

  specialize (H0 _ H7 (X ~ bind_sub T2 ++ E) H2 H3).

  apply type4rec_to_type in H6.
  get_well_form...
  assert (WFC S1 0). { apply type_open_tt_WFC with (X:=X)... apply WF_type with (E:=X~bind_sub T2 ++ E)... }
  assert (WFC S2 0). { apply type_open_tt_WFC with (X:=X)... apply WF_type with (E:=X~bind_sub T2 ++ E)... }
  rewrite bindings_fvar_spec in H0...
  rewrite bindings_fvar_spec with (A:=S2) in H0...

-
  intros.
  dependent destruction H0.
  { dependent destruction H2. inv_rt. }
  2:{ inv_rt. }
  dependent destruction H1.
  2:{ inv_rt. }
  dependent destruction H.
  simpl. f_equal. apply IHHA...

-
  intros. dependent destruction H0.
  { dependent destruction H2. inv_rt. }
  dependent destruction H7;try inv_rt...
  dependent destruction H8...
  simpl in H3. collect_nil H3.
-
  intros. inversion H1;subst.
  { dependent destruction H2;try inv_rt. }
  inversion H2;subst;try inv_rt...
  dependent destruction H5...
  { simpl in H13. collect_nil H13. }
  simpl.
  assert (equiv E (typ_rcd_cons i0 T0 T3)  (typ_rcd_cons i T1 T2)) by (split;auto)...
  apply record_permutation in H5. unfold equiv in H5. destruct_hypos.
  rewrite IHHA1 with (B:=x)...
  2:{ apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
  rewrite IHHA2 with (B:=(dropLabel i (typ_rcd_cons i0 T0 T3)))...
  2:{ apply type_to_rec. apply WF_type with (E:=E). apply WF_drop. get_well_form... }
  pose proof bindings_drop_label (T:=typ_rcd_cons i0 T0 T3) (E:=E) empty_menv (t:=x) i.
  rewrite H22...
Qed.


Lemma label_equiv: forall E C D,
    equiv E C D ->
    collectLabel C [=] collectLabel D.
Proof with auto.
  intros.
  unfold equiv in *.
  destruct H.
  induction H;simpl in *;try solve [apply AtomSetProperties.equal_refl]...
  -
    dependent destruction H0...
    simpl.
    apply AtomSetProperties.equal_refl.
    inversion H2.
  -
    apply sub_tvar_inv in H0. destruct H0... subst...
    apply AtomSetProperties.equal_refl.
  -
    dependent induction H0;simpl in *;try solve [apply AtomSetProperties.equal_refl]...
    +
      inversion H1.
    +
      inversion H2.
    +
      apply AtomSetProperties.subset_antisym...
Qed.


Lemma subtyping_dec : forall k A B E,
bindings_rec (mk_benv E) nil 0 A + 
bindings_rec (mk_benv E) nil 0 B <= k ->
{sub E A B} + {~ sub E A B}.
Proof with auto.
induction k.
-
induction A;intros;try solve [unfold bindings in *;exfalso;simpl in *;lia]...
-
induction A.
+
  induction B;intros;try solve [ solve_right_dec | solve_top_dec E]...

+
  induction B;intros;try solve [ solve_right_dec | solve_top_dec E]...

+
  induction B;intros;try solve [ solve_right_dec | solve_top_dec E]...
  right. intros C. inversion C;subst. inversion H1. inv_rt.
      
+
  intros. simpl in H.
  destruct (wf_env_dec E).
  2:{ right. intros C. apply sub_regular in C. destruct C... }
  destruct (binds_key_dec E a).
  *
    pose proof uniq_from_wf_env w as u.
    destruct s.
    destruct x.
    { assert (WF E t).
      { apply WF_from_binds_typ with (x:=a)... }
      apply WF_type in H0.
      rewrite (findX_sem _ _ w b) in H. 
      (* 2:{ apply binds_split in b.
        destruct b as [E1 [E2 b]]. rewrite b in w.
        apply wf_env_binds_not_fv_tt in w... } *)
      apply le_S_n in H.
      destruct (IHk _ _ _ H)...
      { left. apply sa_trans_tvar with (U:=t)... }
      { destruct (EqDec_eq a B).
        { left. subst. apply sa_fvar... apply WF_var with (U:=t)... }
        destruct (EqDec_eq typ_top B).
        { left. subst. apply sa_top... apply WF_var with (U:=t)... }
        right. intros C. inversion C;inv_rt;subst...
        { assert (bind_sub t =  bind_sub U). 
          { eapply binds_unique with (x:=a) (E:=E)... }
          inversion H1;subst... }
      }
    }
    { right. intros C. apply uniq_from_wf_env in w.
      inversion C;subst;inv_rt.
      { inversion H3;subst. pose proof binds_unique _ _ _ _ _ b H4 w.
        inversion H0.  }
      { inversion H1;subst. pose proof binds_unique _ _ _ _ _ b H4 w.
        inversion H2.  }
      { pose proof binds_unique _ _ _ _ _ b H1 w.
        inversion H0.  }
    }

  *
    right. intros C.
    inversion C;inv_rt;subst...
    { inversion H3;subst. apply n in H4... }
    { inversion H1;subst. apply n in H4... }
    { apply n in H1... }


+ intros. simpl in H.
  induction B;intros;try solve [ solve_right_dec | solve_top_dec E]...
  * solve_top_dec E. solve_top_wfs_dec E (typ_arrow A1 A2).
  
  *
    simpl in H.
    destruct IHk with (A:=B1) (B:=A1) (E:=E); try solve [lia];
    destruct IHk with (A:=A2) (B:=B2) (E:=E);try solve [lia];
    try solve [solve_right_dec].
    left. apply sa_arrow...

+
  intros. simpl in H.
  induction B;intros;try solve [ solve_right_dec]...
  * solve_top_dec E. solve_top_wfs_dec E (typ_all A1 A2).

  *
    destruct (IHk A1 B1 E); try solve [solve_right_dec].
    { simpl in H. lia. }
    destruct (IHk B1 A1 E); try solve [solve_right_dec].
    { simpl in H. lia. }


    (* destruct (EqDec_eq A1 B1);try solve [solve_right_dec]. *)
    (* rename A1 into A. *)
    (* rename A2 into B1. *)

    destruct (wf_env_dec E).
    2:{ right. intros C. apply sub_regular in C. destruct C as [? [? ?]]... }
    pose proof uniq_from_wf_env w as u.
    (* destruct (wf_dec A1 u);try solve [solve_right_dec]. *)

    pick_fresh X1.
    assert (uniq ((X1 ~ bind_sub A1) ++ E)) as u2...
    assert (uniq ((X1 ~ bind_sub B1) ++ E)) as u3...
    destruct (wf_dec (open_tt A2 X1) u2).
    2:{ right. intros C.
        apply sub_regular in C. destruct C as [? [? ?]].
        inversion H1;subst.
        pick_fresh X2. specialize_x_and_L X2 L.
        apply n. apply WF_replacing_var with (X:=X2)... }
    destruct (wf_dec (open_tt B2 X1) u3).
    2:{ right. intros C.
        apply sub_regular in C. destruct C as [? [? ?]].
        inversion H2;subst.
        pick_fresh X2. specialize_x_and_L X2 L.
        apply n. apply WF_replacing_var with (X:=X2)... }
    

    clear IHA1 IHA2 IHB1 IHB2. simpl in H.

    specialize (IHk (open_tt A2 X1) (open_tt B2 X1)
    (X1 ~ bind_sub B1 ++ E)).

    rewrite <- bindings_fvar_spec with (X:=X1)in H...
    2:{ apply type_open_tt_WFC with (X:=X1)... apply WF_type in w0... }
    2:{ get_well_form... }
    2:{ get_well_form... apply WF_type in H4... }
    
    rewrite <- bindings_fvar_spec with (X:=X1)in H...
    2:{ apply type_open_tt_WFC with (X:=X1)... apply WF_type in w1... }
    2:{ get_well_form... }
    2:{ get_well_form... apply WF_type in H5... } 

    assert (Eq: bindings_rec (mk_benv E) empty_menv 0 A1 = bindings_rec (mk_benv E) empty_menv 0 B1).
    { apply equiv_measure...
      { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
      { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
    }
    rewrite Eq in *.

    destruct IHk.
    { simpl in H. simpl. rewrite Eq in H. lia. }
    { left.
      apply sa_all with (L:={{X1}} \u fv_tt A1 \u fv_tt A2 \u fv_tt B1 \u fv_tt B2 \u dom E);intros...
      (* { apply Reflexivity... } { apply Reflexivity... } *)
      apply sub_replacing_var with (X:=X1)...
      get_well_form...
    }
    { right. intros. intros C.
      inversion C;inv_rt. subst. pick_fresh X2.
      specialize_x_and_L X2 L.
      apply n. apply sub_replacing_var with (X:=X2)...
      get_well_form... }


+ 
  intros. simpl in H.
  induction B;intros;try solve [ solve_right_dec]...
  * solve_top_dec E. solve_top_wfs_dec E (typ_mu A).

  *
    destruct (wf_env_dec E).
    2:{ right. intros C. apply sub_regular in C. destruct C as [? [? ?]]... }
    pose proof uniq_from_wf_env w as u.

    pick_fresh X1. assert (uniq ((X1 ~ bind_sub typ_top) ++ E)) as u2...
    
    destruct (wf_dec (open_tt A X1) u2).
    2:{ right. intros C. apply n.
        inversion C;inv_rt. subst.
        pick_fresh X2. specialize_x_and_L X2 L.
        apply WF_replacing_var with (X:=X2)... }
    destruct (wf_dec (open_tt B X1) u2).
    2:{ right. intros C. apply n.
        inversion C;inv_rt. subst.
        pick_fresh X2. specialize_x_and_L X2 L.
        apply WF_replacing_var with (X:=X2)... }

    clear IHA IHB. simpl in H.

    specialize (IHk (open_tt A (typ_label X1 (open_tt A X1)))
    (open_tt B (typ_label X1 (open_tt B X1)))
    (X1 ~ bind_sub typ_top ++ E)).

    assert (WFC A 0). { apply WF_type in w0. apply type_open_tt_WFC in w0... }
    assert (WFC B 0). { apply WF_type in w1. apply type_open_tt_WFC in w1... }


    rewrite bindings_find_spec' 
      with (A:=A) (B:= typ_label X1 (open_tt A X1)) in IHk... 
    2:{ constructor. apply WF_type in w0... }
    rewrite bindings_find_spec' 
      with (A:=B) (B:= typ_label X1 (open_tt B X1)) in IHk... 
    2:{ constructor. apply WF_type in w1... }

    assert (Haux: forall G E n A X, 
      bindings_rec G E n (typ_label X A) = S (bindings_rec G E n A))...
    rewrite !Haux in IHk. clear Haux.

    rewrite bindings_fvar_spec in IHk...
    rewrite bindings_fvar_spec in IHk...

    rewrite <- findX_extend in IHk...
    2:{ apply WFC_WFD_S... }
    rewrite <- findX_extend in IHk...
    2:{ apply WFC_WFD_S... }

    destruct IHk.
    { apply le_S_n in H. eapply le_trans;[|apply H].
      apply plus_le_compat.
      { apply sub_menv_sem. constructor...
        simpl. lia. }
      { apply le_S. apply sub_menv_sem.
        constructor... simpl. lia. }
    }

    { left.
      apply sa_rec with (L:={{X1}} \u fv_tt A \u fv_tt B \u dom E \u fl_tt A \u fl_tt B);intros...
      { apply WF_replacing_var with (X:=X1)... }
      { apply WF_replacing_var with (X:=X1)... }
      {
        apply sub_renaming_unfolding with (X:=X1)...
      }
    }
    { right. intros. intros C.
      inversion C;inv_rt. subst. pick_fresh X2.
      specialize_x_and_L X2 L.
      apply n. simpl.
      apply sub_renaming_unfolding with (X:=X2)...
    }

+ 
  intros. simpl in H.
  induction B;intros;try solve [ solve_right_dec]...
  * solve_top_dec E. solve_top_wfs_dec E (typ_label a A).

  *
    simpl in H. destruct IHk with (A:=A) (B:=B) (E:=E).
    { lia. }

    { destruct (a == a0).
      + subst. constructor...
      + right. intros C. inversion C;inv_rt;subst... }
    { right. intros C. inversion C;inv_rt;subst... }

+
  intros. simpl in H.
  induction B;intros;try solve [ solve_right_dec]...
  * solve_top_dec E.

  * solve_top_dec E. left. apply Reflexivity...

  * right. intros C. inversion C. collect_nil H3.

+
intros. 
induction B;intros;try solve [ solve_right_dec]...
* solve_top_dec E. solve_top_wfs_dec E (typ_rcd_cons a A1 A2).

* solve_top_dec E. 
  solve_top_wfs_dec E (typ_rcd_cons a A1 A2).
  left.
  apply sa_rcd...
  { intro r. intros. simpl in H0. exfalso. apply notin_empty_1 in H0... }
  { intros. inversion H1. }
  
*



destruct (subset_dec (collectLabel (typ_rcd_cons a0 B1 B2)) (collectLabel (typ_rcd_cons a A1 A2)) );
  try solve [ solve_right_dec].

solve_top_dec E. 
solve_top_wfs_dec E (typ_rcd_cons a A1 A2).
solve_top_wfs_dec E (typ_rcd_cons a0 B1 B2).


destruct (@record_permutation_exists a0 E (typ_rcd_cons a A1 A2)) as [[x e]| e]...
{ apply s... simpl. apply union_iff. left... }

pose proof (e':=e).
destruct e'.
assert (type4rec (typ_rcd_cons a0 x (dropLabel a0 (typ_rcd_cons a A1 A2)))).
{ apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
assert (type4rec (typ_rcd_cons a A1 A2)).
{ apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
pose proof equiv_measure H2 H3 H0 H1.
rewrite <- H4 in H.

destruct IHk with (E:=E)
(A:= x) (B:=B1)...
{ simpl in H. lia... }
2:{ right. intros C.
    pose proof sub_transitivity H0 C.
    inversion H5;subst.
    specialize (H12 a0 x B1).
    apply n. apply H12;simpl;rewrite eq_dec_refl...
    }

destruct IHk with (E:=E)
(B:= B2) (A:=(dropLabel a0 (typ_rcd_cons a A1 A2)))...
{  simpl in H. simpl. lia... }

-- left.
    apply sub_transitivity with (typ_rcd_cons a0 x (dropLabel a0 (typ_rcd_cons a A1 A2)))...
    apply sa_rcd...
    { apply label_equiv in e. rewrite e... }
    { destruct e. get_well_form... }
    { intros.  simpl in H5. simpl in H6.
      destruct (a0 == i).
      { inversion H5. inversion H6. subst... }
      { apply (rcd_inversion s1) with (i:=i)...
        + get_well_form. apply rt_type_drop with (E:=E)...
        + inversion w0... }
    }

-- right.
    intros C.
    pose proof sub_transitivity H0 C.
    inversion H5;subst.
    apply n. apply sa_rcd...
    { apply rt_type_drop with (E:=E)... }
    { inversion w0... }
    { simpl in H9.
      rewrite <- !KeySetProperties.add_union_singleton in H9.
      apply dom_add_subset in H9...
      inversion H10;inversion H11... }
    { inversion H10... }
    { inversion H11... }
    { intros. apply H12 with (i:=i).
      + simpl. destruct (a0 == i)... subst i.
        apply label_belong in H14.
        inversion H11. exfalso...
      + simpl. destruct (a0 == i)... subst i.
        apply label_belong in H14.
        inversion H11. exfalso...
    }

Qed.


Lemma decidability : forall A B E,
{sub E A B} + {~ sub E A B}.
Proof with auto.
  intros.
  apply subtyping_dec with (k:=bindings_rec (mk_benv E) nil 0 A + 
                               bindings_rec (mk_benv E) nil 0 B )...
Qed.
