Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export DecidabilityWF.
Require Export Coq.micromega.Lia.

Inductive measure_val : Type :=
| mval : nat -> measure_val
| mtop : measure_val
| mbot : measure_val
.

(* The first one is for local nameless, the second one is for initial free variables *)
Definition menv := list (nat * measure_val).
Notation empty_menv := (@nil (nat * measure_val)).

Definition genv  := list (atom * measure_val).

Fixpoint find  (n:nat) (E: menv) :=
  match E with
  | (k, mval v) :: E' =>
      if (n == k) then Some (S v) else find n E'
  | (k, mtop) :: E' => 
      if (n == k) then Some 1 else find n E'
  | (k, mbot) :: E' =>
      if (n == k) then Some 1 else find n E'
  | nil => None
  end.


Fixpoint findX  (x:var) (G: genv) :=
  match G with
  | (k, mval v) :: E' =>
      if (x == k) then Some (S v) else findX x E'
  | (k, mtop) :: E' =>
      if (x == k) then Some 1 else findX x E'
  | (k, mbot) :: E' =>
      if (x == k) then Some 1 else findX x E'
  | nil => None
  end.


Fixpoint find_top (n:nat) (E: menv) :=
  match E with
  | (k, mval v) :: E' =>
      if (n == k) then false else find_top n E'
  | (k, mtop) :: E' => 
      if (n == k) then true else find_top n E'
  | (k, mbot) :: E' =>
      if (n == k) then false else find_top n E'
  | nil => false
  end.

Fixpoint find_bot (n:nat) (E: menv) :=
  match E with
  | (k, mval v) :: E' =>
      if (n == k) then false else find_bot n E'
  | (k, mtop) :: E' => 
      if (n == k) then false else find_bot n E'
  | (k, mbot) :: E' =>
      if (n == k) then true else find_bot n E'
  | nil => false
  end.


Fixpoint findX_top  (x:var) (G: genv) :=
  match G with
  | (k, mval v) :: E' =>
      if (x == k) then false else findX_top x E'
  | (k, mtop) :: E' =>
      if (x == k) then true else findX_top x E'
  | (k, mbot) :: E' =>
      if (x == k) then false else findX_top x E'
  | nil => false
  end.

Fixpoint findX_bot  (x:var) (G: genv) :=
  match G with
  | (k, mval v) :: E' =>
      if (x == k) then false else findX_bot x E'
  | (k, mtop) :: E' =>
      if (x == k) then false else findX_bot x E'
  | (k, mbot) :: E' =>
      if (x == k) then true else findX_bot x E'
  | nil => false
  end.

Definition is_top (G:genv) (E: menv) (m: typ) n  :=
  match m with
  | typ_top => true
  | typ_fvar x => findX_top x G
  | typ_bvar k => find_top (n - k) E
  | _ => false
  end.

Definition is_bot (G:genv) (E: menv) (m: typ) n  :=
  match m with
  | typ_bot => true
  | typ_fvar x => findX_bot x G
  | typ_bvar k => find_bot (n - k) E
  | _ => false
  end.

Fixpoint bindings_rec (G:genv) (E: menv) (n: nat) (T:typ) : nat :=
  match T with
  | typ_nat => 1
  | typ_top => 1
  | typ_bot => 1
  | typ_fvar x => match findX x G with
                      | Some k => k
                      | None => 2
                      end
  | typ_bvar m => match find (n - m) E with
                      | Some k => k
                      | None => 2
                      end 
  | typ_arrow A B => S (bindings_rec G E n A) + (bindings_rec G E n B)
  | typ_label _ A => S (bindings_rec G E n A)
  | typ_all_lb A B =>
      if is_top G E A n then
        S (1 + (bindings_rec G ((S n, mtop) :: E) (S n) B))
      else
        let i := bindings_rec G E n A in
        S (i + (bindings_rec G ((S n, mval i) :: E) (S n) B))
  | typ_all A B =>
      if is_bot G E A n then
        S (1 + (bindings_rec G ((S n, mbot) :: E) (S n) B))
      else
        let i := bindings_rec G E n A in
        S (i + (bindings_rec G ((S n, mval i) :: E) (S n) B))
  | typ_mu A => 
       let i := bindings_rec G ((S n , mval 1) :: E) (S n) A in
       S (bindings_rec G ((S n, mval i) :: E) (S n) A)
  (* | typ_rcd_nil => 1
  | typ_rcd_cons i T1 T2 =>
      S (bindings_rec G E n T1) + (bindings_rec G E n T2) *)
  end.



Definition equiv_top (G:genv) (m: typ) :=
  match m with
  | typ_top => true
  | typ_fvar x => findX_top x G
  | _ => false
  end.

Definition equiv_bot (G:genv) (m: typ) :=
  match m with
  | typ_bot => true
  | typ_fvar x => findX_bot x G
  | _ => false
  end.


Fixpoint mk_benv (E:env) : genv :=
  match E with
  | nil => nil
  | (_, bind_typ _)::E' => mk_benv E'
  | (X, bind_sub U)::E' => 
        let G := mk_benv E' in
        if equiv_bot G U 
        then (X, mbot) :: G
        else 
        (X, mval (bindings_rec G nil 0 U)) :: G
  | (X, bind_sub_lb U)::E' => 
        let G := mk_benv E' in
        if equiv_top G U 
        then (X, mtop) :: G
        else 
        (X, mval (bindings_rec G nil 0 U)) :: G
  end.

Definition bindings E T := bindings_rec (mk_benv E) nil 0 T.

Definition zero := 0.

Lemma bindings_find_in: forall (E1 E2:menv) k,
    find 0 (E1 ++ E2) = None ->
    find 0 (E1 ++ (0, mval k) :: E2) = Some (S k).
Proof with auto.
  induction E1...
  intros.
  destruct a. destruct m.
  + simpl in *.
    destruct n;simpl in *...
    inversion H.
  + simpl in *.
    destruct n;simpl in *...
    inversion H.
  + simpl in *.
    destruct n;simpl in *...
    inversion H.
Qed.

Lemma bindings_find_notin: forall (E1 E2:menv) k (n:nat),
    find (S n) (E1 ++ (0, k) :: E2) = find (S n) (E1++E2).
Proof with auto.
  induction E1;intros...
  -
    destruct k...
  -
    destruct a... destruct m;simpl...
    +
      destruct (S n == n0)...
    +
      destruct (S n == n0)...
    +
      destruct (S n == n0)...
Qed.

(* WFC typ n : type with <= k binded variables *)
Inductive WFC :  typ -> nat -> Prop :=
| WC_nat: forall k,
    WFC typ_nat k
| WC_top: forall k,
    WFC typ_top k
| WC_bot: forall k,
    WFC typ_bot k
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
| WC_all_lb : forall A B n,
    WFC A n ->
    WFC B (S n) ->
    WFC (typ_all_lb A B) n
| WC_rec: forall A n,
    WFC A (S n) ->
    WFC (typ_mu A) n
| WC_label: forall l A k,
    WFC A k ->
    WFC (typ_label l A) k
(* | WC_nil: forall k,
    WFC typ_rcd_nil k
| WC_cons: forall i A B k,
    WFC A k ->
    WFC B k ->
    WFC (typ_rcd_cons i A B) k *)
.

(* WFC typ n : type with < k binded variables *)
Inductive WFD :  typ -> nat -> Prop :=
| WD_nat: forall k,
    WFD typ_nat k
| WD_top: forall k,
    WFD typ_top k
| WD_bot: forall k,
    WFD typ_bot k
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
| WD_all_lb: forall A B n,
    WFD A n ->
    WFD B (S n) ->
    WFD (typ_all_lb A B) n
| WD_rcd: forall l A k,
    WFD A k ->
    WFD (typ_label l A) k
(* | WD_nil: forall k,
    WFD typ_rcd_nil k
| WD_cons: forall i A B k,
    WFD A k ->
    WFD B k ->
    WFD (typ_rcd_cons i A B) k *)
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
  destruct m.
  + destruct (S k == n)...
    lia.
    apply IHE...
    lia.
  + destruct (S k == n)...
    lia.
    apply IHE...
    lia.
  + destruct (S k == n)...
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
  destruct m.
  +
    destruct (k == n) ...
    destruct (S k == S n)...
    destruct n1...
    destruct (S k == S n)...
    destruct n1...
  +
    destruct (k == n) ...
    destruct (S k == S n)...
    destruct n0...
    destruct (S k == S n)...
    destruct n0...
  +
    destruct (k == n) ...
    destruct (S k == S n)...
    destruct n0...
    destruct (S k == S n)...
    destruct n0...
Qed.


Lemma find_top_add_eq: forall E k,
    find_top k E = find_top (S k) (addone E).
Proof with auto.
  induction E;intros...
  destruct a...
  simpl...
  destruct m.
  +
    destruct (k == n) ...
    destruct (S k == S n)...
    destruct n1...
    destruct (S k == S n)...
    destruct n1...
  +
    destruct (k == n) ...
    destruct (S k == S n)...
    destruct n0...
    destruct (S k == S n)...
  +
    destruct (k == n) ...
    destruct (S k == S n)... lia.
    destruct (S k == S n)... lia.
Qed.

Lemma find_add: forall E k b,
    k >= b ->
    find (k - b) E = find (S k - b) (addone E).
Proof with auto using find_add_eq.
  induction E;intros...
  -
    destruct a...
    assert (addone ((n, m) :: E) = (S n, m) :: addone E) by auto.
    rewrite H0.
    assert (S k - b = S (k-b)) by lia.
    rewrite H1.
    destruct m.
    +
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
    +
      destruct (k-b);simpl...
      destruct (0==n)...
      destruct (1== S n)...
      destruct n0...
      destruct (1== S n)...
      destruct n0...
      destruct (S n0 == n)...
      destruct (S (S n0) == S n)...
      destruct n1...
      destruct (S (S n0) == S n)...
      destruct n1...
    +
      destruct (k-b);simpl...
      destruct (0==n)...
      destruct (1== S n)...
      destruct n0...
      destruct (1== S n)...
      destruct n0...
      destruct (S n0 == n)...
      destruct (S (S n0) == S n)...
      destruct n1...
      destruct (S (S n0) == S n)...
      destruct n1...
Qed.

Lemma is_top_add_one : forall G E A n,
  WFC A n ->
  is_top G E A n = is_top G (addone E) A (S n).
Proof with auto.
  intros.
  induction A... unfold is_top.
  rewrite find_top_add_eq. f_equal.
  inversion H;subst. lia.
Qed.


Lemma find_bot_add_eq: forall E k,
    find_bot k E = find_bot (S k) (addone E).
Proof with auto.
  induction E;intros...
  destruct a...
  simpl...
  destruct m.
  +
    destruct (k == n) ...
    destruct (S k == S n)...
    destruct n1...
    destruct (S k == S n)...
    destruct n1...
  +
    destruct (k == n) ...
    destruct (S k == S n)...
    destruct n0...
    destruct (S k == S n)... lia.
  +
    destruct (k == n) ...
    destruct (S k == S n)...
    destruct n0...
    destruct (S k == S n)...
Qed.

Lemma is_bot_add_one : forall G E A n,
  WFC A n ->
  is_bot G E A n = is_bot G (addone E) A (S n).
Proof with auto.
  intros.
  induction A... unfold is_bot.
  rewrite find_bot_add_eq. f_equal.
  inversion H;subst. lia.
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
    (* all_lb *)
    simpl.
    rewrite is_bot_add_one...
    destruct (is_bot G (addone E) A (S n)).
    + replace ((S (S n), mbot) :: addone E) with (addone ((S n, mbot) :: E))...
    +
      rewrite <- IHWFC1.
      replace ((S (S n), mval (bindings_rec G E n A)) :: addone E)
      with (addone ((S n, mval (bindings_rec G E n A)) :: E))...
  -
    (* all *)
    simpl.
    rewrite is_top_add_one...
    destruct (is_top G (addone E) A (S n)).
    + replace ((S (S n), mtop) :: addone E) with (addone ((S n, mtop) :: E))...
    +
      rewrite <- IHWFC1.
      replace ((S (S n), mval (bindings_rec G E n A)) :: addone E)
      with (addone ((S n, mval (bindings_rec G E n A)) :: E))...
  -
    simpl...
    f_equal...
    assert (bindings_rec G ((S (S n), mval 1) :: addone E) (S (S n)) A =
            bindings_rec G (addone ((S n, mval 1)::E)) (S (S n)) A) by auto.
    rewrite H0...
    rewrite <- IHWFC ...
    remember ((bindings_rec G ((S n, mval 1) :: E) (S n) A)).
    assert ((S (S n), mval n0) :: addone E = addone ((S n, mval n0)::E)) by auto.
    rewrite H1.
    rewrite <- IHWFC...
Qed.

Fixpoint close_tt_rec (K : nat) (Z : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat      
  | typ_bot         => typ_bot      
  | typ_top         => typ_top              
  | typ_bvar J      => typ_bvar J
  | typ_fvar X      => if X == Z then typ_bvar K else typ_fvar X 
  | typ_arrow T1 T2 => typ_arrow (close_tt_rec K Z T1) (close_tt_rec K Z T2)
  | typ_mu T        => typ_mu (close_tt_rec (S K) Z T)
  | typ_all A B     => typ_all (close_tt_rec K Z A) 
                                (close_tt_rec (S K) Z B)
  | typ_all_lb A B  => typ_all_lb (close_tt_rec K Z A) 
                                   (close_tt_rec (S K) Z B)
  | typ_label l T => typ_label l (close_tt_rec K Z T)
  (* | typ_rcd_nil => typ_rcd_nil
  | typ_rcd_cons i A B => typ_rcd_cons i (close_tt_rec K Z A) (close_tt_rec K Z B) *)
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
  - (* WFC_all_lb *)
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
  - (* WFD_all_lb *)
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
  destruct b.
  + destruct (n==S k);destruct (n0==n1)...
    lia.
    lia.
    subst.
    apply IHWFE...
  + destruct (n==S k);destruct (n0==n1)...
    lia.
    lia.
    subst.
    apply IHWFE...
  + destruct (n==S k);destruct (n0==n1)...
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


Lemma find_top_minusk: forall E k,
    WFE E k ->
    forall q n, 0 < n -> 
    q < n ->
    find_top n E = find_top (n - q) (minusk E q).
Proof with auto.
  intros E k H.
  induction H;intros...
  remember (n-q).
  assert (minusk ((S k, b) :: E) q = (S k - q, b) :: (minusk E q)) as W by (simpl;auto).
  rewrite W.
  remember (S k - q).
  simpl...
  destruct b.
  + destruct (n==S k);destruct (n0==n1)...
    lia.
    lia.
    subst.
    apply IHWFE...
  + destruct (n==S k);destruct (n0==n1)...
    lia.
    lia.
    subst.
    apply IHWFE...
  + destruct (n==S k);destruct (n0==n1)...
    lia.
    lia.
    subst.
    apply IHWFE...
Qed.
  

Lemma is_top_minusk: forall G E A n q k,
    WFE E n -> WFD A k -> k <= n - q -> q <= n ->
    is_top G (minusk E q) A (n - q) = is_top G E A n.
Proof with auto.
  intros.
  induction A... unfold is_top.
  replace (n - q - n0) with ((n - n0) - q) by lia.
  inversion H0;subst.
  rewrite <- find_top_minusk with (k:=n)...
  lia. lia.
Qed.


Lemma find_bot_minusk: forall E k,
    WFE E k ->
    forall q n, 0 < n -> 
    q < n ->
    find_bot n E = find_bot (n - q) (minusk E q).
Proof with auto.
  intros E k H.
  induction H;intros...
  remember (n-q).
  assert (minusk ((S k, b) :: E) q = (S k - q, b) :: (minusk E q)) as W by (simpl;auto).
  rewrite W.
  remember (S k - q).
  simpl...
  destruct b.
  + destruct (n==S k);destruct (n0==n1)...
    lia.
    lia.
    subst.
    apply IHWFE...
  + destruct (n==S k);destruct (n0==n1)...
    lia.
    lia.
    subst.
    apply IHWFE...
  + destruct (n==S k);destruct (n0==n1)...
    lia.
    lia.
    subst.
    apply IHWFE...
Qed.


Lemma is_bot_minusk: forall G E A n q k,
    WFE E n -> WFD A k -> k <= n - q -> q <= n ->
    is_bot G (minusk E q) A (n - q) = is_bot G E A n.
Proof with auto.
  intros.
  induction A... unfold is_bot.
  replace (n - q - n0) with ((n - n0) - q) by lia.
  inversion H0;subst.
  rewrite <- find_bot_minusk with (k:=n)...
  lia. lia.
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
    remember (bindings_rec G ((S (n0 - q), mval 1) :: minusk E q) (S (n0 - q)) A).
    assert (S (n0 - q) = (S n0) - q) as W by  lia.
    rewrite W.
    assert  ( ((S n0 - q, mval n1) :: minusk E q) = minusk ((S n0, mval n1)::E) q) as W2 by (simpl;auto).
    rewrite W2.
    rewrite <- IHWFD...
    f_equal...
    f_equal...
    f_equal...
    f_equal...
    subst.
    rewrite W.
    assert ((S n0 - q, mval 1) :: minusk E q = minusk ((S n0, mval 1)::E) q) as W3 by (simpl;auto).
    rewrite W3.
    rewrite <- IHWFD...
    lia.
    lia.
  - (* typ_all *)
    simpl...
    rewrite is_bot_minusk with (k:=n)...
    destruct (is_bot G E A n0)...
    + replace (S (n0 - q)) with (S n0 - q) by lia.
      replace ((S n0 - q, mbot) :: minusk E q) with
      (minusk ((S n0, mbot)::E) q)...
      rewrite <- IHWFD2... lia.
    + f_equal.
      rewrite <- IHWFD1... f_equal.
      replace (S (n0 - q)) with (S n0 - q) by lia.
      assert  ( ((S n0 - q, mval (bindings_rec G E n0 A)) :: minusk E q) = minusk ((S n0, mval (bindings_rec G E n0 A))::E) q) as W2 by (simpl;auto).
      rewrite W2.
      rewrite <- IHWFD2... lia.
  - (* typ_all_lb *)
    simpl...
    rewrite is_top_minusk with (k:=n)...
    destruct (is_top G E A n0)...
    + replace (S (n0 - q)) with (S n0 - q) by lia.
      replace ((S n0 - q, mtop) :: minusk E q) with
      (minusk ((S n0, mtop)::E) q)...
      rewrite <- IHWFD2... lia.
    + f_equal.
      rewrite <- IHWFD1... f_equal.
      replace (S (n0 - q)) with (S n0 - q) by lia.
      assert  ( ((S n0 - q, mval (bindings_rec G E n0 A)) :: minusk E q) = minusk ((S n0, mval (bindings_rec G E n0 A))::E) q) as W2 by (simpl;auto).
      rewrite W2.
      rewrite <- IHWFD2... lia.
Qed.

Lemma find_former: forall E2 E1 (k:nat),
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
      destruct n0...
    +
      simpl.
      destruct (k == n)...
      apply in_inv in H.
      destruct H...
      dependent destruction H...
      destruct n1...
      destruct m.
      *
        apply IHE1...
        exists x...
      *
        apply IHE1...
        exists x...
      *
        apply IHE1...
        exists x...
Qed.


Lemma minus_in_for_bindings: forall E ( n :nat) (k:measure_val),
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
    exists (mval 0)...
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


Lemma find_top_former: forall E2 E1 (k:nat),
    (exists p, In (k,p) E1) ->
    find_top k E1 = find_top k (E1++E2).
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
      destruct n0...
    +
      simpl.
      destruct (k == n)...
      apply in_inv in H.
      destruct H...
      dependent destruction H...
      destruct n1...
      destruct m.
      *
        apply IHE1...
        exists x...
      *
        apply IHE1...
        exists x...
      *
        apply IHE1...
        exists x...
Qed.

Lemma is_top_close_env: forall G E1 E2 A  k,
  WFD A k->   
  (forall q, exists p, q < k -> In (k-q,p) E1) -> 
    is_top G (E1 ++ E2) A k = is_top G E1 A k.
Proof with auto.
  intros.
  induction A;try solve [simpl;auto]...
  unfold is_top.
  rewrite <- find_top_former with (E2:=E2)...
  inversion H;subst.
  destruct H0 with (q:=n)...
  apply H1 in H2. exists x...
Qed.



Lemma find_bot_former: forall E2 E1 (k:nat),
    (exists p, In (k,p) E1) ->
    find_bot k E1 = find_bot k (E1++E2).
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
      destruct n0...
    +
      simpl.
      destruct (k == n)...
      apply in_inv in H.
      destruct H...
      dependent destruction H...
      destruct n1...
      destruct m.
      *
        apply IHE1...
        exists x...
      *
        apply IHE1...
        exists x...
      *
        apply IHE1...
        exists x...
Qed.

Lemma is_bot_close_env: forall G E1 E2 A  k,
  WFD A k->   
  (forall q, exists p, q < k -> In (k-q,p) E1) -> 
    is_bot G (E1 ++ E2) A k = is_bot G E1 A k.
Proof with auto.
  intros.
  induction A;try solve [simpl;auto]...
  unfold is_bot.
  rewrite <- find_bot_former with (E2:=E2)...
  inversion H;subst.
  destruct H0 with (q:=n)...
  apply H1 in H2. exists x...
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
    remember (bindings_rec G ((S n, mval 1) :: E1 ++ E2) (S n) A).
    rewrite_env (((S n, mval n0) :: E1) ++ E2).
    rewrite IHWFD...
    subst.
    rewrite_env (((S n, mval 1) :: E1) ++ E2).
    rewrite IHWFD...
    intros.
    apply minus_in_for_bindings...
    intros.
    apply minus_in_for_bindings...
  -
    simpl.
    rewrite is_bot_close_env...
    destruct (is_bot G E1 A n).
    +
      rewrite_env (((S n, mbot) :: E1) ++ E2).
      rewrite IHWFD2...
      intros.
      apply minus_in_for_bindings...
    +
      f_equal.
      rewrite IHWFD1... f_equal.
      remember (bindings_rec G E1 n A).
      rewrite_env (((S n, mval n0) :: E1) ++ E2).
      rewrite IHWFD2...
      intros.
      apply minus_in_for_bindings...

  -
    simpl.
    rewrite is_top_close_env...
    destruct (is_top G E1 A n).
    +
      rewrite_env (((S n, mtop) :: E1) ++ E2).
      rewrite IHWFD2...
      intros.
      apply minus_in_for_bindings...
    +
      f_equal.
      rewrite IHWFD1... f_equal.
      remember (bindings_rec G E1 n A).
      rewrite_env (((S n, mval n0) :: E1) ++ E2).
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
  exists (mval 0).
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
Proof with auto.
  intros. revert E n.
  induction A;intros;simpl;try solve[lia]...
  { induction E;simpl;try lia.
    destruct a, m.
    + destruct (n0 - n == n1)... lia.
    + destruct (n0 - n == n1)...
    + destruct (n0 - n == n1)...
  }
  { induction G;simpl;try lia.
    destruct a0, m.
    + destruct (a  == a0 )... lia.
    + destruct (a  == a0 )...
    + destruct (a  == a0 )...
  }
  {
      destruct (is_bot G E A1 n);try solve[lia].
  }
  {
      destruct (is_top G E A1 n);try solve[lia].
  }
Qed.

Lemma is_top_mk_benv: forall G E A n X T,
  X \notin fv_tt A ->
  is_top (mk_benv G) E A n = is_top (mk_benv (X ~ T ++ G)) E A n.
Proof with auto.
  intros. simpl. destruct T...
  + destruct A... simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
    destruct (equiv_bot (mk_benv G) t).
    * simpl. destruct (a == X)... exfalso...
    * simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
  + destruct A... simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
    destruct (equiv_top (mk_benv G) t).
    * simpl. destruct (a == X)...
    * simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
Qed.


Lemma is_bot_mk_benv: forall G E A n X T,
  X \notin fv_tt A ->
  is_bot (mk_benv G) E A n = is_bot (mk_benv (X ~ T ++ G)) E A n.
Proof with auto.
  intros. simpl. destruct T...
  + destruct A... simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
    destruct (equiv_bot (mk_benv G) t).
    * simpl. destruct (a == X)...
    * simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
  + destruct A... simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
    destruct (equiv_top (mk_benv G) t).
    * simpl. destruct (a == X)... exfalso...
    * simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
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
    * simpl.
      destruct (equiv_bot (mk_benv G) t) eqn:E0.
      + simpl.
        destruct (X0==X)...
        subst. exfalso.
        apply H0. simpl...
      + simpl.
        destruct (X0==X)...
        subst. exfalso.
        apply H0. simpl...
    * simpl.
      destruct (equiv_top (mk_benv G) t) eqn:E0.
      + simpl.
        destruct (X0==X)...
        subst. exfalso.
        apply H0. simpl...
      + simpl.
        destruct (X0==X)...
        subst. exfalso.
        apply H0. simpl...
  - simpl. f_equal. destruct T...
    +
      rewrite IHWFD... 2:{ constructor... apply WFE_find_none... }
      simpl. f_equal. f_equal. f_equal.
      rewrite IHWFD... { constructor... apply WFE_find_none... }
    +
      rewrite IHWFD... 2:{ constructor... apply WFE_find_none... }
      simpl. f_equal. f_equal. f_equal.
      rewrite IHWFD... { constructor... apply WFE_find_none... }

  - destruct T... 
    + simpl in H0.
      simpl. rewrite is_bot_mk_benv with (X:=X) (T:=bind_sub t)...
      simpl.
      remember (is_bot
      (if equiv_bot (mk_benv G) t
       then (X, mbot) :: mk_benv G
       else (X, mval (bindings_rec (mk_benv G) empty_menv 0 t)) :: mk_benv G) E
      A n) as b.
      destruct b.
      * 
        rewrite IHWFD2... { constructor... apply WFE_find_none... }
      *
        rewrite IHWFD1... f_equal.
        rewrite IHWFD2... { constructor... apply WFE_find_none... }
    + simpl in H0.
      simpl. rewrite is_bot_mk_benv with (X:=X) (T:=bind_sub_lb t)...
      simpl.
      remember (is_bot
      (if equiv_top (mk_benv G) t
       then (X, mtop) :: mk_benv G
       else (X, mval (bindings_rec (mk_benv G) empty_menv 0 t)) :: mk_benv G) E
      A n) as b.
      destruct b.
      * 
        rewrite IHWFD2... { constructor... apply WFE_find_none... }
      *
        rewrite IHWFD1... f_equal.
        rewrite IHWFD2... { constructor... apply WFE_find_none... }

  - destruct T... 
    + simpl in H0.
      simpl. rewrite is_top_mk_benv with (X:=X) (T:=bind_sub t)...
      simpl.
      remember (is_top
        (if equiv_bot (mk_benv G) t
        then (X, mbot) :: mk_benv G
        else (X, mval (bindings_rec (mk_benv G) empty_menv 0 t)) :: mk_benv G) E
        A n) as b.
      destruct b.
      * 
        rewrite IHWFD2... { constructor... apply WFE_find_none... }
      *
        rewrite IHWFD1... f_equal.
        rewrite IHWFD2... { constructor... apply WFE_find_none... }
    + simpl in H0.
      simpl. rewrite is_top_mk_benv with (X:=X) (T:=bind_sub_lb t)...
      simpl.
      remember (is_top
      (if equiv_top (mk_benv G) t
       then (X, mtop) :: mk_benv G
       else (X, mval (bindings_rec (mk_benv G) empty_menv 0 t)) :: mk_benv G) E
      A n) as b.
      destruct b.
      * 
        rewrite IHWFD2... { constructor... apply WFE_find_none... }
      *
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


Lemma bindings_find_in_top: forall (E1 E2:menv),
    find 0 (E1 ++ E2) = None ->
    find 0 (E1 ++ (0, mtop) :: E2) = Some 1.
Proof with auto.
  induction E1...
  intros.
  destruct a. destruct m.
  + simpl in *.
    destruct n;simpl in *...
    inversion H.
  + simpl in *.
    destruct n;simpl in *...
  + simpl in *.
    destruct n;simpl in *...
Qed.


Lemma bindings_is_top: forall G E A n,
  is_top G E A n = true -> type A ->
  bindings_rec G E n A = 1.
Proof with auto.
  intros. induction A;simpl in *;try solve [inversion H]...
  - inversion H0.
   (* induction E...
    destruct a. destruct m;simpl in *...
    + destruct (n-n0==n1);simpl in *... inversion H.
    + destruct (n-n0==n1);simpl in *... *)
  - induction G...
    { inversion H. }
    destruct a0. destruct m;simpl in *...
    + destruct (a==a0);simpl in *... inversion H.
    + destruct (a==a0);simpl in *...
    + destruct (a==a0);simpl in *...
Qed.



Lemma bindings_is_bot: forall G E A n,
  is_bot G E A n = true -> type A ->
  bindings_rec G E n A = 1.
Proof with auto.
  intros. induction A;simpl in *;try solve [inversion H]...
  - inversion H0.
   (* induction E...
    destruct a. destruct m;simpl in *...
    + destruct (n-n0==n1);simpl in *... inversion H.
    + destruct (n-n0==n1);simpl in *... *)
  - induction G...
    { inversion H. }
    destruct a0. destruct m;simpl in *...
    + destruct (a==a0);simpl in *... inversion H.
    + destruct (a==a0);simpl in *...
    + destruct (a==a0);simpl in *...
Qed.

Lemma is_top_open_tt_top: forall G E1 E2 B n A1,
WFE (E1 ++ E2) n -> WFC A1 n ->
is_top G (E1 ++ E2) B n = true ->
is_top G (E1 ++ E2) (open_tt_rec n B A1) n = is_top G (E1 ++ (0, mtop) :: E2) A1 n.
Proof with auto.
  intros.
  induction A1...
  simpl in *. destruct (n == n0).
  - subst. replace (n0 - n0) with 0 by lia.
    rewrite H1. clear H1.
    dependent induction H.
    + destruct E1;inversion x. destruct E2;inversion x. simpl...
    + destruct E1... inversion x;subst.
      simpl. rewrite <- IHWFE... destruct b...
  - simpl. clear H. clear H1. induction E1...
    + simpl. destruct (n-n0==0)... exfalso. inversion H0. lia.
    + destruct a. simpl. destruct (n-n0==n2)... destruct m;apply IHE1...
Qed.


Lemma is_bot_open_tt_bot: forall G E1 E2 B n A1,
WFE (E1 ++ E2) n -> WFC A1 n ->
is_bot G (E1 ++ E2) B n = true ->
is_bot G (E1 ++ E2) (open_tt_rec n B A1) n = is_bot G (E1 ++ (0, mbot) :: E2) A1 n.
Proof with auto.
  intros.
  induction A1...
  simpl in *. destruct (n == n0).
  - subst. replace (n0 - n0) with 0 by lia.
    rewrite H1. clear H1.
    dependent induction H.
    + destruct E1;inversion x. destruct E2;inversion x. simpl...
    + destruct E1... inversion x;subst.
      simpl. rewrite <- IHWFE... destruct b...
  - simpl. clear H. clear H1. induction E1...
    + simpl. destruct (n-n0==0)... exfalso. inversion H0. lia.
    + destruct a. simpl. destruct (n-n0==n2)... destruct m;apply IHE1...
Qed.


Lemma bindings_find_top_in: forall (E1 E2:menv) k,
    find 0 (E1 ++ E2) = None ->
    find_top 0 (E1 ++ (0, mval k) :: E2) = false.
Proof with auto.
  induction E1...
  intros.
  destruct a. destruct m.
  + simpl in *.
    destruct n;simpl in *...
  + simpl in *.
    destruct n;simpl in *...
    inversion H.
  + simpl in *.
    destruct n;simpl in *...
Qed.



Lemma bindings_find_top_in2: forall (E1 E2:menv),
    find 0 (E1 ++ E2) = None ->
    find_top 0 (E1 ++ (0, mbot) :: E2) = false.
Proof with auto.
  induction E1...
  intros.
  destruct a. destruct m.
  + simpl in *.
    destruct n;simpl in *...
  + simpl in *.
    destruct n;simpl in *...
    inversion H.
  + simpl in *.
    destruct n;simpl in *...
Qed.


Lemma bindings_find_bot_in: forall (E1 E2:menv) k,
    find 0 (E1 ++ E2) = None ->
    find_bot 0 (E1 ++ (0, mval k) :: E2) = false.
Proof with auto.
  induction E1...
  intros.
  destruct a. destruct m.
  + simpl in *.
    destruct n;simpl in *...
  + simpl in *.
    destruct n;simpl in *...
  + simpl in *.
    destruct n;simpl in *...
    inversion H.
Qed.


Lemma bindings_find_bot_in2: forall (E1 E2:menv),
    find 0 (E1 ++ E2) = None ->
    find_bot 0 (E1 ++ (0, mtop) :: E2) = false.
Proof with auto.
  induction E1...
  intros.
  destruct a. destruct m.
  + simpl in *.
    destruct n;simpl in *...
  + simpl in *.
    destruct n;simpl in *...
  + simpl in *.
    destruct n;simpl in *...
    inversion H.
Qed.


Lemma is_top_open_tt_nottop: forall G E1 E2 B n A1 k,
find zero (E1++E2) = None ->
WFE (E1 ++ E2) n -> WFC A1 n ->
is_top G (E1 ++ E2) B n = false ->
is_top G (E1 ++ E2) (open_tt_rec n B A1) n = 
is_top G (E1 ++ (0, mval k) :: E2) A1 n.
Proof with auto.
  intros.
  induction A1...
  simpl in *. destruct (n == n0).
  - subst. replace (n0 - n0) with 0 by lia.
    rewrite H2. clear H2.
    rewrite bindings_find_top_in...
  - simpl. clear H. clear H0. clear H2. induction E1...
    + simpl. destruct (n-n0==0)... exfalso. inversion H1. lia.
    + destruct a. simpl. destruct (n-n0==n2)... destruct m;
      apply IHE1...
Qed.


Lemma is_top_open_tt_nottop2: forall G E1 E2 B n A1,
find zero (E1++E2) = None ->
WFE (E1 ++ E2) n -> WFC A1 n ->
is_top G (E1 ++ E2) B n = false ->
is_top G (E1 ++ E2) (open_tt_rec n B A1) n = 
is_top G (E1 ++ (0, mbot) :: E2) A1 n.
Proof with auto.
  intros.
  induction A1...
  simpl in *. destruct (n == n0).
  - subst. replace (n0 - n0) with 0 by lia.
    rewrite H2. clear H2.
    rewrite bindings_find_top_in2...
  - simpl. clear H. clear H0. clear H2. induction E1...
    + simpl. destruct (n-n0==0)... exfalso. inversion H1. lia.
    + destruct a. simpl. destruct (n-n0==n2)... destruct m;
      apply IHE1...
Qed.


Lemma is_bot_open_tt_notbot: forall G E1 E2 B n A1 k,
find zero (E1++E2) = None ->
WFE (E1 ++ E2) n -> WFC A1 n ->
is_bot G (E1 ++ E2) B n = false ->
is_bot G (E1 ++ E2) (open_tt_rec n B A1) n = 
is_bot G (E1 ++ (0, mval k) :: E2) A1 n.
Proof with auto.
  intros.
  induction A1...
  simpl in *. destruct (n == n0).
  - subst. replace (n0 - n0) with 0 by lia.
    rewrite H2. clear H2.
    rewrite bindings_find_bot_in...
  - simpl. clear H. clear H0. clear H2. induction E1...
    + simpl. destruct (n-n0==0)... exfalso. inversion H1. lia.
    + destruct a. simpl. destruct (n-n0==n2)... destruct m;
      apply IHE1...
Qed.


Lemma is_bot_open_tt_notbot2: forall G E1 E2 B n A1,
find zero (E1++E2) = None ->
WFE (E1 ++ E2) n -> WFC A1 n ->
is_bot G (E1 ++ E2) B n = false ->
is_bot G (E1 ++ E2) (open_tt_rec n B A1) n = 
is_bot G (E1 ++ (0, mtop) :: E2) A1 n.
Proof with auto.
  intros.
  induction A1...
  simpl in *. destruct (n == n0).
  - subst. replace (n0 - n0) with 0 by lia.
    rewrite H2. clear H2.
    rewrite bindings_find_bot_in2...
  - simpl. clear H. clear H0. clear H2. induction E1...
    + simpl. destruct (n-n0==0)... exfalso. inversion H1. lia.
    + destruct a. simpl. destruct (n-n0==n2)... destruct m;
      apply IHE1...
Qed.


Lemma is_bot_extend: forall G E1 E2 A n k,
  find k (E1++E2) = None ->
  is_bot G (E1 ++ E2) A n = true ->
  is_bot G (E1 ++ (k, mbot) :: E2) A n = true.
Proof with auto.
  intros.
  induction A... simpl in *.
  induction E1...
  - simpl. destruct (n-n0==k)...
  - destruct a. simpl in *.
    destruct (k == n1).
    + subst. destruct (n - n0 == n1)...
      { destruct m; inversion H. }
    + destruct (n - n0 == n1)... destruct m...
Qed.



Lemma is_bot_extend2: forall G E A n k,
  type A ->
  is_bot G (E) A n = 
  is_bot G ((S n, k) :: E) A (S n).
Proof with auto.
  intros.
  induction A... inversion H.
Qed.

Lemma is_top_extend: forall G E1 E2 A n k,
  find k (E1++E2) = None ->
  is_top G (E1 ++ E2) A n = true ->
  is_top G (E1 ++ (k, mtop) :: E2) A n = true.
Proof with auto.
  intros.
  induction A... simpl in *.
  induction E1...
  - simpl. destruct (n-n0==k)...
  - destruct a. simpl in *.
    destruct (k == n1).
    + subst. destruct (n - n0 == n1)...
      { destruct m; inversion H. }
    + destruct (n - n0 == n1)... destruct m...
Qed.



Lemma is_top_extend2: forall G E A n k,
  type A ->
  is_top G (E) A n = 
  is_top G ((S n, k) :: E) A (S n).
Proof with auto.
  intros.
  induction A... inversion H.
Qed.


Lemma bindings_find_in_bot: forall (E1 E2:menv),
    find 0 (E1 ++ E2) = None ->
    find 0 (E1 ++ (0, mbot) :: E2) = Some 1.
Proof with auto.
  induction E1...
  intros.
  destruct a. destruct m.
  + simpl in *.
    destruct n;simpl in *...
    inversion H.
  + simpl in *.
    destruct n;simpl in *...
  + simpl in *.
    destruct n;simpl in *...
Qed.

Lemma findX_bot_top_contra:  forall a G,
  findX_bot a G = true ->
  findX_top a G = true -> False.
Proof.
  intros. induction G.
  - inversion H.
  - destruct a0. simpl in H, H0.
    destruct (a==a0).
    + destruct m;inversion H;inversion H0.
    + destruct m;apply IHG;auto.
Qed.



(* incorrect: when B is a bottom variable *)
Lemma bindings_find: forall A G E1 E2 B,
    find zero (E1++E2) = None ->
    type B ->
    WFC A 0 ->
    WFE (E1++E2)  0 ->
    (* is_top G (E1 ++ E2) B 0 = false -> *)
    (bindings_rec G (E1++E2) 0 (open_tt A B)) =
    bindings_rec G (E1 ++ (zero, 
        if is_top G (E1 ++ E2) B 0 then mtop else
        if is_bot G (E1 ++ E2) B 0 then mbot else
        mval ((bindings_rec G (E1++E2) 0 B) - 1)) :: E2) 0 A.


(* incorrect: when B is a bottom variable *)
(* Lemma bindings_find: forall A G E1 E2 B,
    find zero (E1++E2) = None ->
    WFC B 0 ->
    WFC A 0 ->
    WFE (E1++E2)  0 ->
    (* is_top G (E1 ++ E2) B 0 = false -> *)
    (bindings_rec G (E1++E2) 0 (open_tt A B)) =
    bindings_rec G (E1 ++ (zero, mval ((bindings_rec G (E1++E2) 0 B) - 1)) :: E2) 0 A. *)
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
      destruct (is_top G (E1 ++ E2) B n) eqn:E0...
      { rewrite bindings_find_in_top... apply bindings_is_top... }
      destruct (is_bot G (E1 ++ E2) B n) eqn:E0'...
      { rewrite bindings_find_in_bot... apply bindings_is_bot... }
      { rewrite bindings_find_in...
        pose proof bindings_rec_ge_1 G (E1 ++ E2) n B.
        lia. }
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
    simpl.
    destruct (is_bot G (E1 ++ E2) B n) eqn:Bbot, (is_top G (E1 ++ E2) B n) eqn:Btop...
    + (* B is bot and top, contradiction *)
      destruct B;try solve [inversion Bbot;inversion Btop;inversion H0]...
      simpl in Bbot. simpl in Btop.
      exfalso. eapply findX_bot_top_contra;eauto.
    + (* B is bot type *)
      rewrite is_bot_open_tt_bot...
      destruct ((is_bot G (E1 ++ (0, mbot) :: E2) A1 n)) eqn:Abot...
      * (* A1 (the bound) is bot type *)
        f_equal. f_equal.
        specialize (IHA2 (S n) G ((S n, mbot)::E1) E2 B). simpl in IHA2.
        rewrite IHA2... 2:{ constructor... apply WFE_find_none... }
        repeat try f_equal.
        rewrite <- is_top_extend2...
        rewrite <- is_bot_extend2... rewrite Bbot, Btop...
      * (* A1 (the bound) is not bottom type *)
        f_equal. 
        rewrite IHA1... rewrite Btop, Bbot. f_equal.
        remember ((S n, mval (bindings_rec G (E1 ++ (0, mbot) :: E2) n A1))) as R1.
        specialize (IHA2 (S n) G (R1::E1) E2 B). simpl in IHA2.
        rewrite IHA2...
        { subst. simpl. 
          rewrite <- is_top_extend2, <- is_bot_extend2... rewrite Btop, Bbot... }
        { subst... }
        { rewrite_env (R1 :: E1 ++ E2).
          subst.
          apply WFE_S_n... }
    + (* B is top type *)
      rewrite <- is_bot_open_tt_notbot2 with (B:=B)...
      destruct (is_bot G (E1 ++ E2) (open_tt_rec n B A1) n) eqn:Abot...
      * (* A1 (the bound) is bot type *)
        f_equal. f_equal.
        specialize (IHA2 (S n) G ((S n, mbot)::E1) E2 B). simpl in IHA2.
        rewrite IHA2... 2:{ constructor... apply WFE_find_none... }
        repeat try f_equal.
        rewrite <- is_top_extend2... rewrite Btop...
      * (* A1 (the bound) is not top type *)
        f_equal.
        rewrite IHA1... rewrite Btop. f_equal.
        remember ((S n, mval
          (bindings_rec G (E1 ++ (0, mtop) :: E2) n A1))) as R1.
        specialize (IHA2 (S n) G (R1::E1) E2 B). simpl in IHA2.
        rewrite IHA2...
        { subst. simpl. 
          rewrite <- is_top_extend2, <- is_bot_extend2... rewrite Btop... }
        { subst... }
        { rewrite_env (R1 :: E1 ++ E2).
          subst.
          apply WFE_S_n... }
    + (* B is normal type *)
      rewrite <- !is_bot_open_tt_notbot with (B:=B)...
      destruct (is_bot G (E1 ++ E2) (open_tt_rec n B A1)) eqn:Abot...
      * (* A1 (the bound) is top type *)
        f_equal. f_equal.
        specialize (IHA2 (S n) G ((S n, mbot)::E1) E2 B). simpl in IHA2.
        rewrite IHA2... 2:{ constructor... apply WFE_find_none... }
        repeat try f_equal.
        rewrite <- is_top_extend2... rewrite Btop.
        f_equal. f_equal.
        rewrite_alist ((S n, mbot) :: (E1 ++ E2)).
        rewrite <- is_bot_extend2... rewrite Bbot...
        rewrite <- bindings_close...
      * (* A1 (the bound) is not top type *)
        f_equal.
        rewrite IHA1... rewrite Btop, Bbot. f_equal.
        remember ((S n, mval
          (bindings_rec G (E1 ++ (0, mval (bindings_rec G (E1 ++ E2) n B - 1)) :: E2) n A1))) as R1.
        assert (bindings_rec G (E1++E2) n B = bindings_rec G (R1 :: E1++E2) (S n) B) as Q1.
        subst.
        apply bindings_close...
        rewrite Q1.    
        rewrite_alist ((R1 :: E1) ++ (0, mval (bindings_rec G ((R1 :: E1) ++ E2) (S n) B - 1)) :: E2).
        specialize (IHA2 (S n) G (R1::E1) E2 B). simpl in IHA2.
        rewrite IHA2...
        { subst. simpl. rewrite <- is_top_extend2... rewrite <- is_bot_extend2... 
          rewrite Btop... rewrite Bbot... }
        { subst... }
        { rewrite_env (R1 :: E1 ++ E2).
          subst.
          apply WFE_S_n... }

  - (* all_lb *)
    dependent destruction H1.
    simpl.
    destruct (is_bot G (E1 ++ E2) B n) eqn:Bbot, (is_top G (E1 ++ E2) B n) eqn:Btop...
    + (* B is bot and top, contradiction *)
      destruct B;try solve [inversion Bbot;inversion Btop;inversion H0]...
      simpl in Bbot. simpl in Btop.
      exfalso. eapply findX_bot_top_contra;eauto.
    + (* B is bot type *)
      rewrite <- is_top_open_tt_nottop2 with (B:=B)...
      destruct (is_top G (E1 ++ E2) (open_tt_rec n B A1) n) eqn:Abot...
      * (* A1 (the bound) is bot type *)
        f_equal. f_equal.
        specialize (IHA2 (S n) G ((S n, mtop)::E1) E2 B). simpl in IHA2.
        rewrite IHA2... 2:{ constructor... apply WFE_find_none... }
        repeat try f_equal.
        rewrite <- is_top_extend2... rewrite <- is_bot_extend2...
        rewrite Btop, Bbot...
      * (* A1 (the bound) is not top type *)
        f_equal.
        rewrite IHA1... rewrite Btop, Bbot. f_equal.
        remember ((S n, mval
          (bindings_rec G (E1 ++ (0, mbot) :: E2) n A1))) as R1.
        specialize (IHA2 (S n) G (R1::E1) E2 B). simpl in IHA2.
        rewrite IHA2...
        { subst. simpl. 
          rewrite <- is_top_extend2, <- is_bot_extend2... rewrite Btop...
            rewrite Bbot... }
        { subst... }
        { rewrite_env (R1 :: E1 ++ E2).
          subst.
          apply WFE_S_n... }
    + (* B is bot type *)
      rewrite is_top_open_tt_top...
      destruct ((is_top G (E1 ++ (0, mtop) :: E2) A1 n)) eqn:Atop...
      * (* A1 (the bound) is top type *)
        f_equal. f_equal.
        specialize (IHA2 (S n) G ((S n, mtop)::E1) E2 B). simpl in IHA2.
        rewrite IHA2... 2:{ constructor... apply WFE_find_none... }
        repeat try f_equal.
        rewrite <- is_top_extend2...
        rewrite <- is_bot_extend2... rewrite Bbot, Btop...
      * (* A1 (the bound) is not top type *)
        f_equal. 
        rewrite IHA1... rewrite Btop...
        remember ((S n, mval (bindings_rec G (E1 ++ (0, mtop) :: E2) n A1))) as R1.
        specialize (IHA2 (S n) G (R1::E1) E2 B). simpl in IHA2.
        rewrite IHA2...
        { subst. simpl. 
          rewrite <- is_top_extend2, <- is_bot_extend2... rewrite Btop... }
        { subst... }
        { rewrite_env (R1 :: E1 ++ E2).
          subst.
          apply WFE_S_n... }
    + (* B is normal type *)
      rewrite <- !is_top_open_tt_nottop with (B:=B)...
      destruct (is_top G (E1 ++ E2) (open_tt_rec n B A1)) eqn:Abot...
      * (* A1 (the bound) is top type *)
        f_equal. f_equal.
        specialize (IHA2 (S n) G ((S n, mtop)::E1) E2 B). simpl in IHA2.
        rewrite IHA2... 2:{ constructor... apply WFE_find_none... }
        repeat try f_equal.
        rewrite <- is_top_extend2... rewrite Btop.
        f_equal. f_equal.
        rewrite_alist ((S n, mtop) :: (E1 ++ E2)).
        rewrite <- is_bot_extend2... rewrite Bbot...
        rewrite <- bindings_close...
      * (* A1 (the bound) is not top type *)
        f_equal.
        rewrite IHA1... rewrite Btop, Bbot. f_equal.
        remember ((S n, mval
          (bindings_rec G (E1 ++ (0, mval (bindings_rec G (E1 ++ E2) n B - 1)) :: E2) n A1))) as R1.
        assert (bindings_rec G (E1++E2) n B = bindings_rec G (R1 :: E1++E2) (S n) B) as Q1.
        subst.
        apply bindings_close...
        rewrite Q1.    
        rewrite_alist ((R1 :: E1) ++ (0, mval (bindings_rec G ((R1 :: E1) ++ E2) (S n) B - 1)) :: E2).
        specialize (IHA2 (S n) G (R1::E1) E2 B). simpl in IHA2.
        rewrite IHA2...
        { subst. simpl. rewrite <- is_top_extend2... rewrite <- is_bot_extend2... 
          rewrite Btop... rewrite Bbot... }
        { subst... }
        { rewrite_env (R1 :: E1 ++ E2).
          subst.
          apply WFE_S_n... }


  -
    dependent destruction H1...
    simpl.
    f_equal.
    remember ( 
      mval (bindings_rec G
         ((S n, mval 1) :: E1 ++ (0, if is_top G (E1 ++ E2) B n
         then mtop
         else 
         if is_bot G (E1 ++ E2) B n
         then mbot
         else mval (bindings_rec G (E1 ++ E2) n B - 1)) :: E2) 
         (S n) A)) as R1.
    assert (bindings_rec G (E1++E2) n B = bindings_rec G ((S n, R1) :: E1++E2) (S n) B) as Q1.
    subst.
    apply bindings_close...
    rewrite Q1.
    rewrite_alist (((S n, R1) :: E1) ++ (0, if is_top G (E1 ++ E2) B n
        then mtop
        else
       if is_bot G (E1 ++ E2) B n
       then mbot
       else mval (bindings_rec G ((S n, R1) :: E1 ++ E2) (S n) B - 1)) :: E2).
    rewrite is_top_extend2 with (k:=R1)...
    rewrite is_bot_extend2 with (k:=R1)...
    rewrite_alist (((S n, R1) :: E1) ++ E2).
    rewrite <- IHA...
    { f_equal.
      remember (bindings_rec G ((S n, mval 1) :: E1 ++ E2) (S n) (open_tt_rec (S n) B A)) as R2.
      rewrite_alist ((S n, R1) :: E1 ++ E2).
      f_equal.
      subst.
      f_equal...
      f_equal.
      assert (bindings_rec G (E1++E2) n B = bindings_rec G (((S n, mval 1) :: E1)++E2) (S n) B) as Q2.
      apply bindings_close...
      rewrite Q2.
      rewrite_alist (((S n, mval 1) :: E1) ++ (0, 
        if is_top G (E1 ++ E2) B n
        then mtop
        else if is_bot G (E1 ++ E2) B n
        then mbot
        else mval (bindings_rec G (((S n, mval 1) :: E1) ++ E2) (S n) B - 1)) :: E2).
      rewrite is_top_extend2 with (k:=mval 1)...
      rewrite is_bot_extend2 with (k:=mval 1)...
      rewrite_alist (((S n, mval 1) :: E1) ++ E2).
      rewrite <- IHA...
      rewrite_env ((S n, mval 1) :: E1 ++ E2).
      apply WFE_S_n...
    }
    { subst... }
    { subst.
      apply WFE_S_n... }
Qed.



Lemma bindings_find_spec: forall A G E B,
  find zero E = None ->
  type B ->
  WFC A 0 ->
  WFE E 0 ->
  bindings_rec 
    (mk_benv G) E 0 (open_tt A B) =
  bindings_rec 
    (mk_benv G) ((zero, 
      if is_top (mk_benv G) E B 0 then mtop else
      if is_bot (mk_benv G) E B 0 then mbot else
          mval ((bindings_rec (mk_benv G) E 0 B) - 1)
    ) :: E) 0 A.
Proof with auto.
  intros. 
  rewrite_env (nil ++ (zero, if is_top (mk_benv G) E B 0
  then mtop
  else if is_bot (mk_benv G) E B 0
       then mbot
       else mval (bindings_rec (mk_benv G) E 0 B - 1)) :: E).
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
    (mk_benv G) ((1, if is_top (mk_benv G) empty_menv B 0 then mtop else
      if is_bot (mk_benv G) empty_menv B 0 then mbot else
          mval ((bindings_rec (mk_benv G) empty_menv 0 B) - 1)
    ) :: empty_menv) 1 A.
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
    (E1 ++ [(zero, 
    if is_bot (mk_benv G) (E1 ++ E2) B 0 then mbot else
     mval (bindings_rec (mk_benv G) (E1 ++ E2) 0 B) )] ++ E2) 0 A.
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
      simpl. replace (n - n) with 0 by lia.
      destruct (is_bot (mk_benv G) (E1 ++ E2) B n) eqn:Bbot.
      * rewrite bindings_find_in_bot...
        destruct (equiv_bot (mk_benv G) B) eqn:Bbot2...
        { simpl. rewrite eq_dec_refl... }
        { exfalso. induction H3;try solve [inversion Bbot|inversion Bbot2]...
          simpl in Bbot. simpl in Bbot2. rewrite Bbot in Bbot2. inversion Bbot2. }
      * rewrite bindings_find_in...
        destruct (equiv_bot (mk_benv G) B) eqn:Bbot2...
        { exfalso. induction H3;try solve [inversion Bbot|inversion Bbot2]...
          simpl in Bbot. simpl in Bbot2. rewrite Bbot in Bbot2. inversion Bbot2. }
        { simpl. rewrite eq_dec_refl...
          rewrite <- bindings_local_close with (E:=E1 ++ E2) (n:=n)...
        }

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
    simpl. 
    destruct (equiv_bot (mk_benv G) B) eqn:Bbot;simpl...
    { destruct (a == X)...
      subst X. exfalso. apply H0... simpl... }
    { destruct (a == X)...
      subst X. exfalso. apply H0... simpl... }
  -
    simpl.
    dependent destruction H. simpl in H1.
    simpl in IHA1. rewrite IHA1...
    simpl in IHA2. rewrite IHA2...

  -
    simpl.
    dependent destruction H. simpl in H1.
    destruct (equiv_bot (mk_benv G) B) eqn:Bbot.
    { destruct (is_bot (mk_benv G) (E1 ++ E2) B n) eqn:Bbot2.
      2:{ exfalso. induction H4;try solve [inversion Bbot|inversion Bbot2]...
          simpl in Bbot, Bbot2. congruence. }

          rewrite is_bot_open_tt_bot...
          2:{ simpl. rewrite eq_dec_refl... }
          rewrite_alist (mk_benv (X ~ bind_sub typ_bot ++ G)).
          rewrite <- is_bot_mk_benv...
          destruct (is_bot (mk_benv G) (E1 ++ (0, mbot) :: E2) A1 n).

      + (* A1 is bot *)
        f_equal. f_equal.
        rewrite_env (((S n, mbot)::E1) ++ E2).
        rewrite IHA2...
        { inversion H2;subst. constructor... }
        { constructor... apply WFE_find_none... }

      + (* A1 is not bot *)
        rewrite IHA1...
        2:{ inversion H2;subst. constructor... }
        f_equal. f_equal.
        rewrite <- cons_app_assoc.
        rewrite IHA2...
        * inversion H2;subst. constructor...
        * constructor... apply WFE_find_none...
    }
    { destruct (is_bot (mk_benv G) (E1 ++ E2) B n) eqn:Bbot2.
      { exfalso. induction H4;try solve [inversion Bbot|inversion Bbot2]...
        simpl in Bbot, Bbot2. congruence. }

      rewrite is_bot_open_tt_notbot with (k:=(bindings_rec (mk_benv G) (E1 ++ E2) n B))...
      2:{ simpl. rewrite eq_dec_refl... }
      replace ((X, mval (bindings_rec (mk_benv G) empty_menv 0 B)) :: mk_benv G)
        with (mk_benv (X ~ bind_sub B ++ G)).
      2:{ simpl. rewrite Bbot... }
      rewrite <- is_bot_mk_benv...
      destruct (is_bot (mk_benv G) (E1 ++ (0, mval (bindings_rec (mk_benv G) (E1 ++ E2) n B)) :: E2) A1 n).

      + (* A1 is bot *)
        f_equal. f_equal.
        rewrite_env (((S n, mbot)::E1) ++ E2).
        rewrite IHA2...
        { simpl. erewrite <- is_bot_extend2... rewrite Bbot2.
          rewrite <- bindings_close with (B:=B)... }
        { constructor... apply WFE_find_none... }

      + (* A1 is not bot *)
        rewrite IHA1...
        rewrite Bbot2. f_equal. f_equal.
        rewrite <- !cons_app_assoc.
        rewrite IHA2...
        2:{ constructor... apply WFE_find_none... }
        f_equal. f_equal. simpl. f_equal. f_equal.
        erewrite <- is_bot_extend2...
        rewrite Bbot2. f_equal.
        rewrite <- bindings_close with (B:=B)...
    }


  -
    simpl.
    dependent destruction H. simpl in H1.


    destruct (equiv_bot (mk_benv G) B) eqn:Bbot.
    { destruct (is_bot (mk_benv G) (E1 ++ E2) B n) eqn:Bbot2.
      2:{ exfalso. induction H4;try solve [inversion Bbot|inversion Bbot2]...
          simpl in Bbot, Bbot2. congruence. }

          rewrite is_top_open_tt_nottop2...
          2:{ simpl. rewrite eq_dec_refl... }
          rewrite_alist (mk_benv (X ~ bind_sub typ_bot ++ G)).
          rewrite <- is_top_mk_benv...
          destruct (is_top (mk_benv G) (E1 ++ (0, mbot) :: E2) A1 n).

      + (* A1 is bot *)
        f_equal. f_equal.
        rewrite_env (((S n, mtop)::E1) ++ E2).
        rewrite IHA2...
        { inversion H2;subst. constructor... }
        { constructor... apply WFE_find_none... }

      + (* A1 is not bot *)
        rewrite IHA1...
        2:{ inversion H2;subst. constructor... }
        f_equal. f_equal.
        rewrite <- cons_app_assoc.
        rewrite IHA2...
        * inversion H2;subst. constructor...
        * constructor... apply WFE_find_none...
    }
    { destruct (is_bot (mk_benv G) (E1 ++ E2) B n) eqn:Bbot2.
      { exfalso. induction H4;try solve [inversion Bbot|inversion Bbot2]...
        simpl in Bbot, Bbot2. congruence. }

      rewrite is_top_open_tt_nottop with (k:=(bindings_rec (mk_benv G) (E1 ++ E2) n B))...
      2:{ simpl. rewrite eq_dec_refl... }
      replace ((X, mval (bindings_rec (mk_benv G) empty_menv 0 B)) :: mk_benv G)
        with (mk_benv (X ~ bind_sub B ++ G)).
      2:{ simpl. rewrite Bbot... }
      rewrite <- is_top_mk_benv...
      destruct (is_top (mk_benv G) (E1 ++ (0, mval (bindings_rec (mk_benv G) (E1 ++ E2) n B)) :: E2) A1 n).

      + (* A1 is bot *)
        f_equal. f_equal.
        rewrite_env (((S n, mtop)::E1) ++ E2).
        rewrite IHA2...
        { simpl. erewrite <- is_bot_extend2... rewrite Bbot2.
          rewrite <- bindings_close with (B:=B)... }
        { constructor... apply WFE_find_none... }

      + (* A1 is not bot *)
        rewrite IHA1...
        rewrite Bbot2. f_equal. f_equal.
        rewrite <- !cons_app_assoc.
        rewrite IHA2...
        2:{ constructor... apply WFE_find_none... }
        f_equal. f_equal. simpl. f_equal. f_equal.
        erewrite <- is_bot_extend2...
        rewrite Bbot2. f_equal.
        rewrite <- bindings_close with (B:=B)...
    }


  -
    simpl.
    dependent destruction H. simpl in H0.
    f_equal.


    destruct (equiv_bot (mk_benv G) B) eqn:Bbot.
    { destruct (is_bot (mk_benv G) (E1 ++ E2) B n) eqn:Bbot2.
      2:{ exfalso. induction H3;try solve [inversion Bbot|inversion Bbot2]...
          simpl in Bbot, Bbot2. congruence. }
      
      rewrite_alist (mk_benv (X ~ bind_sub typ_bot ++ G)).
      rewrite <- cons_app_assoc. rewrite IHA...
      2:{ inversion H1;subst. constructor... }
      2:{ constructor... apply WFE_find_none... }
      simpl. f_equal. f_equal. f_equal. f_equal.
      rewrite <- cons_app_assoc.
      rewrite_alist (mk_benv (X ~ bind_sub typ_bot ++ G)). rewrite IHA...
      { inversion H1;subst. constructor... }
      { constructor... apply WFE_find_none... }
    }
    { destruct (is_bot (mk_benv G) (E1 ++ E2) B n) eqn:Bbot2.
      { exfalso. induction H3;try solve [inversion Bbot|inversion Bbot2]...
        simpl in Bbot, Bbot2. congruence. }

      replace ((X, mval (bindings_rec (mk_benv G) empty_menv 0 B)) :: mk_benv G)
        with (mk_benv (X ~ bind_sub B ++ G)).
      2:{ simpl. rewrite Bbot... }
      rewrite <- cons_app_assoc. rewrite IHA...
      2:{ constructor... apply WFE_find_none... }
      f_equal. rewrite !cons_app_assoc.
      erewrite <- is_bot_extend2...
      rewrite Bbot2.
      rewrite <- !cons_app_assoc.
      f_equal.
      + f_equal. f_equal. f_equal. rewrite IHA...
        simpl.
        rewrite <- cons_app_assoc.
        erewrite <- is_bot_extend2... rewrite Bbot2.
        2:{ constructor... apply WFE_find_none... }
        f_equal. simpl. rewrite <- bindings_close with (B:=B)...
      + simpl. rewrite Bbot. rewrite <- bindings_close with (B:=B)...
    }

  - simpl. f_equal. simpl in IHA. simpl in H0.
    rewrite IHA... inversion H...
  (* -
    inversion H;subst. simpl in H0.
    simpl. f_equal. simpl in IHA1. simpl in IHA2.
    rewrite IHA1...  *)
Qed.



Lemma bindings_fvar_spec: forall G A X B,
    WFC A 0 ->
    X \notin fv_tt A ->
    wf_env (X ~ bind_sub B ++ G) ->
    (* find zero (E1++E2) = None -> *)
    type B ->
    bindings_rec (mk_benv (X ~ bind_sub B ++ G)) empty_menv 0 (open_tt A X) =
    bindings_rec (mk_benv G)
    (((1, 
    if is_bot (mk_benv G) empty_menv B 0 then mbot else
            mval (bindings_rec (mk_benv G) empty_menv 0 B
            ) ) ) :: empty_menv) 1 A.
Proof with auto.
  intros.
  rewrite_env (X ~ bind_sub B ++ G).
  rewrite_env (empty_menv ++ empty_menv).
  rewrite bindings_fvar...
  { simpl. rewrite bindings_add... }
Qed.




Lemma bindings_fvar_lb: forall A G E1 E2 X B,
    WFC A 0 ->
    X \notin fv_tt A ->
    wf_env (X ~ bind_sub_lb B ++ G) ->
    find zero (E1++E2) = None ->
    type B ->
    WFE (E1 ++ E2) 0 ->
    bindings_rec (mk_benv (X ~ bind_sub_lb B ++ G)) (E1 ++ E2) 0 (open_tt A X) =
    bindings_rec (mk_benv G)
    (E1 ++ [(zero, 
    if is_top (mk_benv G) (E1 ++ E2)  B 0 then mtop else
            mval (bindings_rec (mk_benv G) (E1 ++ E2) 0 B
            ) ) ] ++ E2) 0 A.
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
      simpl. replace (n - n) with 0 by lia.
      destruct (is_top (mk_benv G) (E1 ++ E2) B n) eqn:Btop.
      * rewrite bindings_find_in_top...
        destruct (equiv_top (mk_benv G) B) eqn:Btop2...
        { simpl. rewrite eq_dec_refl... }
        { exfalso. induction H3;try solve [inversion Btop|inversion Btop2]...
          simpl in Btop. simpl in Btop2. rewrite Btop in Btop2. inversion Btop2. }
      * rewrite bindings_find_in...
        destruct (equiv_top (mk_benv G) B) eqn:Btop2...
        { exfalso. induction H3;try solve [inversion Btop|inversion Btop2]...
          simpl in Btop. simpl in Btop2. rewrite Btop in Btop2. inversion Btop2. }
        { simpl. rewrite eq_dec_refl...
          rewrite <- bindings_local_close with (E:=E1 ++ E2) (n:=n)...
        }

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
    simpl. 
    destruct (equiv_top (mk_benv G) B) eqn:Btop;simpl...
    { destruct (a == X)...
      subst X. exfalso. apply H0... simpl... }
    { destruct (a == X)...
      subst X. exfalso. apply H0... simpl... }
  -
    simpl.
    dependent destruction H. simpl in H1.
    simpl in IHA1. rewrite IHA1...
    simpl in IHA2. rewrite IHA2...

  -
    simpl.
    dependent destruction H. simpl in H1.

    destruct (equiv_top (mk_benv G) B) eqn:Btop.
    { destruct (is_top (mk_benv G) (E1 ++ E2) B n) eqn:Btop2.
      2:{ exfalso. induction H4;try solve [inversion Btop|inversion Btop2]...
          simpl in Btop, Btop2. congruence. }

      rewrite is_bot_open_tt_notbot2...
      2:{ simpl. rewrite eq_dec_refl... }
      rewrite_alist (mk_benv (X ~ bind_sub_lb typ_top ++ G)).
      rewrite <- is_bot_mk_benv...
      destruct (is_bot (mk_benv G) (E1 ++ (0, mtop) :: E2) A1 n).

      + (* A1 is top *)
        f_equal. f_equal.
        rewrite_env (((S n, mbot)::E1) ++ E2).
        rewrite IHA2...
        { inversion H2;subst. constructor... }
        { constructor... apply WFE_find_none... }

      + (* A1 is not top *)
        rewrite IHA1...
        2:{ inversion H2;subst. constructor... }
        f_equal. f_equal.
        rewrite <- cons_app_assoc.
        rewrite IHA2...
        * inversion H2;subst. constructor...
        * constructor... apply WFE_find_none...
    }
    { destruct (is_top (mk_benv G) (E1 ++ E2) B n) eqn:Btop2.
      { exfalso. induction H4;try solve [inversion Btop|inversion Btop2]...
        simpl in Btop, Btop2. congruence. }

      rewrite is_bot_open_tt_notbot with (k:=(bindings_rec (mk_benv G) (E1 ++ E2) n B))...
      2:{ simpl. rewrite eq_dec_refl... }
      replace ((X, mval (bindings_rec (mk_benv G) empty_menv 0 B)) :: mk_benv G)
        with (mk_benv (X ~ bind_sub_lb B ++ G))...
      2:{ simpl. rewrite Btop... }
      rewrite <- is_bot_mk_benv...
      destruct (is_bot (mk_benv G) (E1 ++ (0, mval (bindings_rec (mk_benv G) (E1 ++ E2) n B)) :: E2) A1 n).

      + (* A1 is top *)
        f_equal. f_equal.
        rewrite_env (((S n, mbot)::E1) ++ E2).
        rewrite IHA2...
        { simpl.
          rewrite <- is_top_extend2... rewrite Btop2.
          rewrite <- bindings_close with (B:=B)... }
        { constructor... apply WFE_find_none... }

      + (* A1 is not top *)
        rewrite IHA1... rewrite Btop2.
        f_equal. f_equal.
        rewrite <- !cons_app_assoc.
        rewrite IHA2...
        2:{ constructor... apply WFE_find_none... }
        f_equal. f_equal. simpl. f_equal. f_equal.
        f_equal.
        rewrite <- bindings_close with (B:=B)...
        rewrite <- is_top_extend2... rewrite Btop2...
    }


  -
    simpl.
    dependent destruction H. simpl in H1.
    destruct (equiv_top (mk_benv G) B) eqn:Btop.
    { destruct (is_top (mk_benv G) (E1 ++ E2) B n) eqn:Btop2.
      2:{ exfalso. induction H4;try solve [inversion Btop|inversion Btop2]...
          simpl in Btop, Btop2. congruence. }

      rewrite is_top_open_tt_top...
      2:{ simpl. rewrite eq_dec_refl... }
      rewrite_alist (mk_benv (X ~ bind_sub_lb typ_top ++ G)).
      rewrite <- is_top_mk_benv...
      destruct (is_top (mk_benv G) (E1 ++ (0, mtop) :: E2) A1 n).

      + (* A1 is top *)
        f_equal. f_equal.
        rewrite_env (((S n, mtop)::E1) ++ E2).
        rewrite IHA2...
        { inversion H2;subst. constructor... }
        { constructor... apply WFE_find_none... }

      + (* A1 is not top *)
        rewrite IHA1...
        2:{ inversion H2;subst. constructor... }
        f_equal. f_equal.
        rewrite <- cons_app_assoc.
        rewrite IHA2...
        * inversion H2;subst. constructor...
        * constructor... apply WFE_find_none...
    }
    { destruct (is_top (mk_benv G) (E1 ++ E2) B n) eqn:Btop2.
      { exfalso. induction H4;try solve [inversion Btop|inversion Btop2]...
        simpl in Btop, Btop2. congruence. }

      rewrite is_top_open_tt_nottop with (k:=(bindings_rec (mk_benv G) (E1 ++ E2) n B))...
      2:{ simpl. rewrite eq_dec_refl... }
      replace ((X, mval (bindings_rec (mk_benv G) empty_menv 0 B)) :: mk_benv G)
        with (mk_benv (X ~ bind_sub_lb B ++ G))...
      2:{ simpl. rewrite Btop... }
      rewrite <- is_top_mk_benv...
      destruct (is_top (mk_benv G) (E1 ++ (0, mval (bindings_rec (mk_benv G) (E1 ++ E2) n B)) :: E2) A1 n).

      + (* A1 is top *)
        f_equal. f_equal.
        rewrite_env (((S n, mtop)::E1) ++ E2).
        rewrite IHA2...
        { simpl.
          rewrite <- is_top_extend2... rewrite Btop2.
          rewrite <- bindings_close with (B:=B)... }
        { constructor... apply WFE_find_none... }

      + (* A1 is not top *)
        rewrite IHA1... rewrite Btop2.
        f_equal. f_equal.
        rewrite <- !cons_app_assoc.
        rewrite IHA2...
        2:{ constructor... apply WFE_find_none... }
        f_equal. f_equal. simpl. f_equal. f_equal.
        f_equal.
        rewrite <- bindings_close with (B:=B)...
        rewrite <- is_top_extend2... rewrite Btop2...
    }


  -
    simpl.
    dependent destruction H. simpl in H0.
    f_equal.

    destruct (equiv_top (mk_benv G) B) eqn:Btop.
    { destruct (is_top (mk_benv G) (E1 ++ E2) B n) eqn:Btop2.
      2:{ exfalso. induction H3;try solve [inversion Btop|inversion Btop2]...
          simpl in Btop, Btop2. congruence. }
      
      rewrite_alist (mk_benv (X ~ bind_sub_lb typ_top ++ G)).
      rewrite <- cons_app_assoc. rewrite IHA...
      2:{ inversion H1;subst. constructor... }
      2:{ constructor... apply WFE_find_none... }
      simpl. f_equal. f_equal. f_equal. f_equal.
      rewrite <- cons_app_assoc.
      rewrite_alist (mk_benv (X ~ bind_sub_lb typ_top ++ G)). rewrite IHA...
      { inversion H1;subst. constructor... }
      { constructor... apply WFE_find_none... }
    }
    { destruct (is_top (mk_benv G) (E1 ++ E2) B n) eqn:Btop2.
      { exfalso. induction H3;try solve [inversion Btop|inversion Btop2]...
        simpl in Btop, Btop2. congruence. }

      replace ((X, mval (bindings_rec (mk_benv G) empty_menv 0 B)) :: mk_benv G)
        with (mk_benv (X ~ bind_sub_lb B ++ G))...
      2:{ simpl. rewrite Btop... }
      rewrite <- cons_app_assoc. rewrite IHA...
      2:{ constructor... apply WFE_find_none... }
      f_equal. rewrite !cons_app_assoc.
      rewrite <- is_top_extend2...
      rewrite Btop2.
      rewrite <- !cons_app_assoc.
      f_equal.
      + f_equal. f_equal. f_equal. rewrite IHA...
        simpl.
        rewrite <- cons_app_assoc.
        erewrite <- is_top_extend2... rewrite Btop2.
        2:{ constructor... apply WFE_find_none... }
        f_equal. simpl. rewrite <- bindings_close with (B:=B)...
      + simpl.
        (* rewrite Btop.  *)
        rewrite <- bindings_close with (B:=B)...
    }
    
    
  - simpl. f_equal. simpl in IHA. simpl in H0.
    rewrite IHA... inversion H...
  (* -
    inversion H;subst. simpl in H0.
    simpl. f_equal. simpl in IHA1. simpl in IHA2.
    rewrite IHA1...  *)
Qed.



Lemma bindings_fvar_spec_lb: forall G A X B,
    WFC A 0 ->
    X \notin fv_tt A ->
    wf_env (X ~ bind_sub_lb B ++ G) ->
    (* find zero (E1++E2) = None -> *)
    type B ->
    bindings_rec (mk_benv (X ~ bind_sub_lb B ++ G)) empty_menv 0 (open_tt A X) =
    bindings_rec (mk_benv G)
    (((1, 
    if is_top (mk_benv G) empty_menv B 0 then mtop else
            mval (bindings_rec (mk_benv G) empty_menv 0 B
            ) ) ) :: empty_menv) 1 A.
Proof with auto.
  intros.
  rewrite_env (X ~ bind_sub_lb B ++ G).
  rewrite_env (empty_menv ++ empty_menv).
  rewrite bindings_fvar_lb...
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



Definition is_var (T: typ) : bool :=
  match T with
  | typ_fvar _ => true
  | _ => false
  end.


Ltac inv_var := match goal with
  | [H: is_var ?T = false |- _] =>
    try solve [subst;inversion H]
end.


Ltac solve_right_dec := right;intro v;inversion v;
(* try inv_rt; *)
try inv_var;
auto.


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
  - destruct (IHA1 m); try solve [solve_right_dec].
    destruct (IHA2 (S m)); try solve [solve_right_dec]...
  - destruct (IHA (S m)); try solve [solve_right_dec]...
  - destruct (IHA m); try solve [solve_right_dec]...
  (* - destruct (IHA1 m); try solve [solve_right_dec].
    destruct (IHA2 (m)); try solve [solve_right_dec]... *)
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
    * left. apply WF_var_lb with (U:=t)...
    * right. intros C. inversion C;subst.
      + pose proof binds_unique _ _ _ _ _ b H2 H.
        inversion H0.
      + pose proof binds_unique _ _ _ _ _ b H2 H.
        inversion H0.
  }
  { right. intros C.
    inversion C;subst.
    apply n with (Q:=bind_sub U)...
    apply n with (Q:=bind_sub_lb U)...
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
  destruct H... destruct m...
Qed.  

(* Lemma rt_type_dec: forall A,
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
Qed. *)


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

Lemma is_top_extend_benv: forall G E A n X k, 
  X `notin` fv_tt A ->
  is_top G E A n = is_top ((X, k)::G) E A n.
Proof with auto.
  intros. simpl. destruct k...
  + destruct A... simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
  + destruct A... simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
  + destruct A... simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
Qed.




Lemma findX_top_notin: forall G X,
    X \notin dom G ->
    findX_top X G = false.
Proof with auto.
  induction G;intros...
  simpl in *.
  destruct a.
  destruct (X==a)...
  apply notin_add_1 in H.
  destruct H... destruct m...
Qed.  


Lemma findX_bot_notin: forall G X,
    X \notin dom G ->
    findX_bot X G = false.
Proof with auto.
  induction G;intros...
  simpl in *.
  destruct a.
  destruct (X==a)...
  apply notin_add_1 in H.
  destruct H... destruct m...
Qed.  

Lemma find_var_one: forall Q G X E n,
  X \notin dom G ->
   (* \u fv_tt Q ->  *)
  bindings_rec ( G) E n Q = 
  bindings_rec (X ~ mval 1 ++  G) E n Q.
Proof with auto.
  intros Q G X.
  induction Q;intros...
  + simpl. destruct (a == X)...
    subst. 
    rewrite (findX_notin)...
  + simpl in *. rewrite IHQ1...
  + simpl in *. 
    assert (is_bot G E Q1 n = is_bot ((X, mval 1) :: G) E Q1 n).
    { destruct Q1... simpl. destruct (a == X)...
      rewrite findX_bot_notin... subst... }
    rewrite <- H0.
    rewrite IHQ1...
    destruct (is_bot G E Q1 n)...
  + simpl in *. 
    assert (is_top G E Q1 n = is_top ((X, mval 1) :: G) E Q1 n).
    { destruct Q1... simpl. destruct (a == X)...
      rewrite findX_top_notin... subst... }
    rewrite IHQ1...
    rewrite <- H0.
    destruct (is_top G E Q1 n)...
  + simpl. rewrite IHQ...
    f_equal. f_equal. f_equal.
    f_equal. rewrite IHQ...
  + simpl...
  (* + simpl in *. rewrite IHQ1... *)
Qed.


Lemma mk_benv_dom: forall X G,
  X `notin` dom G -> X `notin` dom (mk_benv G).
Proof with auto.
  induction G;intros...
  + intros. destruct a. simpl. destruct b...
    destruct (equiv_top (mk_benv G) t) eqn:Btop,
     (equiv_bot (mk_benv G) t) eqn:Bbot...
    destruct (equiv_top (mk_benv G) t) eqn:Btop,
      (equiv_bot (mk_benv G) t) eqn:Bbot...
Qed.

(* Lemma bindings_drop_label: forall T E G t i,
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
Qed. *)

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

(* Lemma sub_rcd_proper: forall E a T1 T2 T1' T2',
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
Qed. *)

(* 
Lemma sub_bot_chain: forall E (X:atom),
  sub E X typ_bot ->
  findX_top X (mk_benv E) = true.
Proof with auto.
  intros.
  dependent induction H;subst;inv_rt.
  inversion H0;subst;inv_rt.
  - assert (uniq E). { apply uniq_from_wf_env in H1... }
    clear - H H3. induction E. 
    { inversion H. }
    inversion H;try inversion H0;subst.
    + simpl. rewrite eq_dec_refl...
    + destruct a. simpl in *. destruct b...
      { destruct (equiv_top (mk_benv E) t);simpl...
        { destruct (X == a)... apply IHE... inversion H3... }
        { destruct (X == a)...
          + subst. inversion H3;subst. exfalso... apply H6.
            apply binds_In in H0...
          + apply IHE... inversion H3... }
      }
      { apply IHE... inversion H3... }
  - specialize (IHsub X0 eq_refl eq_refl).
    assert (wf_env E).
    { apply sub_regular in H0. destruct_hypos... }
      (* apply uniq_from_wf_env in H0... } *)
    clear - H H3 IHsub. induction E.
    { inversion H. } destruct a. inversion H3;subst.
    inversion H;subst.
    + inversion H0;subst.
      simpl. destruct (findX_top X0 (mk_benv E)) eqn:X0bot.
      { simpl. rewrite eq_dec_refl... }
      { simpl in IHsub. rewrite X0bot in *.
        simpl in IHsub. destruct (X0 == X).
        * inversion IHsub.
        * rewrite IHsub in X0bot. inversion X0bot.
      }
    + simpl.
      simpl in IHsub.
      destruct (equiv_top (mk_benv E) T);simpl.
      * simpl in IHsub. destruct (X == a)...
        destruct (X0 == a)...
        subst a. assert (WF E X0). { apply WF_from_binds_typ with (x:=X)... }
        inversion H1;subst. apply binds_In in H8. exfalso...
      * simpl in IHsub. destruct (X == a)...
        { subst X. apply binds_In in H0. exfalso... }
        { destruct (X0 == a)...
          { subst X0. inversion IHsub. }
        }
    + simpl. simpl in IHsub. apply IHE...
      inversion H;subst... inversion H0...
Qed. *)


Lemma sub_top_chain: forall E (X:atom),
  sub E typ_top X ->
  findX_top X (mk_benv E) = true.
Proof with auto.
  intros.
  dependent induction H;subst.
  inversion H0;subst.
  - assert (uniq E). { apply uniq_from_wf_env in H1... }
    clear - H H3. induction E. 
    { inversion H. }
    inversion H;try inversion H0;subst.
    + simpl. rewrite eq_dec_refl...
    + destruct a. simpl in *. destruct b...
      { destruct (equiv_bot (mk_benv E) t);simpl...
        { destruct (X == a)...
          + subst. inversion H3;subst. exfalso... apply H6.
            apply binds_In in H0...
          + apply IHE... inversion H3... }
        { destruct (X == a)...
          + subst. inversion H3;subst. exfalso... apply H6.
            apply binds_In in H0...
          + apply IHE... inversion H3... }
      }
      { destruct (equiv_top (mk_benv E) t);simpl...
        { destruct (X == a)...
          apply IHE... inversion H3... }
        { destruct (X == a)...
          + subst. inversion H3;subst. exfalso... apply H6.
            apply binds_In in H0...
          + apply IHE... inversion H3... }
      }
      { apply IHE... inversion H3... }
  - specialize (IHsub X0 eq_refl eq_refl).
    assert (wf_env E).
    { apply sub_regular in H0. destruct_hypos... }
      (* apply uniq_from_wf_env in H0... } *)
    clear - H H3 IHsub. induction E.
    { inversion H. } destruct a. inversion H3;subst.
    + 
      inversion H;subst.
      { inversion H0;subst. }
      { simpl. simpl in IHsub.
        destruct (equiv_bot (mk_benv E) T);simpl.
        * simpl in IHsub. destruct (X == a)...
          { subst X. apply binds_In in H0. exfalso... }
          { destruct (X0 == a)...
            { subst X0. inversion IHsub. }
          }
        * simpl in IHsub. destruct (X == a)...
          { subst X. apply binds_In in H0. exfalso... }
          { destruct (X0 == a)...
            { subst X0. inversion IHsub. }
          }
      }
    + 
      inversion H;subst.
      { inversion H0;subst. simpl. 
        simpl in IHsub.
        simpl. destruct (findX_top X0 (mk_benv E)) eqn:X0bot.
        { simpl. rewrite eq_dec_refl... }
        { simpl in IHsub. rewrite X0bot in *.
          destruct (X0 == X).
          * inversion IHsub.
          * inversion IHsub.
        }
      }
      { simpl. simpl in IHsub.
        destruct (equiv_top (mk_benv E) T);simpl.
        * simpl in IHsub. destruct (X == a)...
          apply IHE...
          destruct (X0 == a)...
          { subst. assert (WF E a). { apply WF_from_binds_typ_lb with (x:=X)... }
            inversion H1;subst; apply binds_In in H8; exfalso...
          }
        * simpl in IHsub. destruct (X == a)...
          { subst X. apply binds_In in H0. exfalso... }
          { destruct (X0 == a)...
            { subst X0. inversion IHsub. }
          }
      }
    + simpl. simpl in IHsub. apply IHE...
      inversion H;subst... inversion H0...
Qed.


Lemma sub_bot_chain: forall E (X:atom),
  sub E X typ_bot ->
  findX_bot X (mk_benv E) = true.
Proof with auto.
  intros.
  dependent induction H;subst.
  inversion H0;subst.
  - assert (uniq E). { apply uniq_from_wf_env in H1... }
    clear - H H3. induction E. 
    { inversion H. }
    inversion H;try inversion H0;subst.
    + simpl. rewrite eq_dec_refl...
    + destruct a. simpl in *. destruct b...
      { destruct (equiv_bot (mk_benv E) t);simpl...
        { destruct (X == a)... apply IHE... inversion H3... }
        { destruct (X == a)...
          + subst. inversion H3;subst. exfalso... apply H6.
            apply binds_In in H0...
          + apply IHE... inversion H3... }
      }
      { destruct (equiv_top (mk_benv E) t);simpl...
        { destruct (X == a)...
          + subst. inversion H3;subst. exfalso... apply H6.
            apply binds_In in H0...
          + apply IHE... inversion H3... }
        { destruct (X == a)...
          + subst. inversion H3;subst. exfalso... apply H6.
            apply binds_In in H0...
          + apply IHE... inversion H3... }
      }
      { apply IHE... inversion H3... }
  - specialize (IHsub X0 eq_refl eq_refl).
    assert (wf_env E).
    { apply sub_regular in H0. destruct_hypos... }
      (* apply uniq_from_wf_env in H0... } *)
    clear - H H3 IHsub. induction E.
    { inversion H. } destruct a. inversion H3;subst.
    inversion H;subst.
    + inversion H0;subst.
      simpl. destruct (findX_bot X0 (mk_benv E)) eqn:X0bot.
      { simpl. rewrite eq_dec_refl... }
      { simpl in IHsub. rewrite X0bot in *.
        simpl in IHsub. destruct (X0 == X).
        * inversion IHsub.
        * rewrite IHsub in X0bot. inversion X0bot.
      }
    + simpl.
      simpl in IHsub.
      destruct (equiv_bot (mk_benv E) T);simpl.
      * simpl in IHsub. destruct (X == a)...
        destruct (X0 == a)...
        subst a. assert (WF E X0). { apply WF_from_binds_typ with (x:=X)... }
        inversion H1;subst. apply binds_In in H8. exfalso...
        apply binds_In in H8. exfalso...
      * simpl in IHsub. destruct (X == a)...
        { subst X. apply binds_In in H0. exfalso... }
        { destruct (X0 == a)...
          { subst X0. inversion IHsub. }
        }
    + simpl. simpl in IHsub.
      destruct (equiv_top (mk_benv E) T);simpl.
      * simpl in IHsub. destruct (X == a)...
        { subst X. analyze_binds H. apply binds_In in BindsTac... }
        destruct (X0 == a)... inversion IHsub.
        apply IHE... inversion H... inversion H0;subst.
      * simpl in IHsub. destruct (X == a)...
        { subst X. analyze_binds H. apply binds_In in BindsTac... }
        destruct (X0 == a)... inversion IHsub.
        apply IHE... inversion H... inversion H0;subst.
    +
      simpl. simpl in IHsub. apply IHE...
      inversion H;subst... inversion H0...
Qed.


Lemma is_top_then_not_bot: forall X G,
  findX_top X G = true ->
  findX_bot X G = false.
Proof with auto.
  intros.
  induction G...
  destruct a. destruct m;simpl in H;simpl;destruct (X == a);try solve [inversion H;subst;auto]...
Qed.

Lemma is_bot_then_not_top: forall X G,
  findX_bot X G = true ->
  findX_top X G = false.
Proof with auto.
  intros.
  induction G...
  destruct a. destruct m;simpl in H;simpl;destruct (X == a);try solve [inversion H;subst;auto]...
Qed.

(* Lemma equiv_is_top_same_var: forall E (X X0:atom),
  sub E X X0 -> sub E X0 X -> findX_top X0 (mk_benv E) = findX_top X (mk_benv E).
Proof with auto.
  intros.
  pose proof suba_sub_tvar_chain H.
  pose proof suba_sub_tvar_chain H0.
  destruct H1 as [[W H5]|[[W H5]|[[U1 [U2 [H5a H5b]]]|[H5|H5]]]].
  *
    destruct H2 as [[W' H6]|[[W' H6]|[[U1 [U2 [H6a H6b]]]|[H6|H6]]]].
    { pose proof sub_tvar_chain_antisym H5 H6. subst... }
    { inversion H5;subst.
      * inversion H6;subst.
        { pose proof binds_uniq _ _ _ H1 H2 H4 as C;inversion C. }
        { apply binds_mid_eq in H2. inversion H2. apply uniq_from_wf_env... }
      * inversion H6;subst.
        { apply binds_mid_eq in H4. inversion H4. apply uniq_from_wf_env... }
        { assert (binds X (bind_sub X2) ( E0 ++ (X, bind_sub_lb X3) :: E3)).
          { rewrite H3... }
          apply binds_mid_eq in H8. inversion H8. apply uniq_from_wf_env... }
    }
    { inversion H5;subst.
      * pose proof binds_uniq _ _ _ H1 H6a H6b as C;inversion C.
      * apply binds_mid_eq in H6b. inversion H6b. apply uniq_from_wf_env...
    }
    { assert (sub E typ_top X0).
      { eapply sub_transitivity with (Q:=X)... }
      apply sub_top_chain in H6. apply sub_top_chain in H1.
      congruence.
    }
    { 
      
    inversion H6;subst.
      inversion H5;subst.
      * pose proof binds_uniq _ _ _ H1 H2 H3 as C;inversion C. subst. 

    }
  *
    destruct H2 as [[W' H6]|[[W' H6]|[[U1 [U2 [H6a H6b]]]|H6]]].
    { inversion H5;subst.
      * inversion H6;subst.
        { pose proof binds_uniq _ _ _ H1 H2 H4 as C;inversion C. }
        { apply binds_mid_eq in H2. inversion H2. apply uniq_from_wf_env... }
      *  inversion H6;subst.
        { apply binds_mid_eq in H4. inversion H4. apply uniq_from_wf_env... }
        { assert (binds X0 (bind_sub_lb X2) ( E0 ++ (X0, bind_sub X3) :: E3)).
          { rewrite H3... }
          apply binds_mid_eq in H8. inversion H8. apply uniq_from_wf_env... }
    }
    { pose proof sub_tvar_chain_antisym_lb H5 H6. subst... }
    { inversion H5;subst.
      * pose proof binds_uniq _ _ _ H1 H6a H6b as C;inversion C.
      * apply binds_mid_eq in H6a. inversion H6a. apply uniq_from_wf_env...
    }
    { assert (sub E typ_top X0).
      { eapply sub_transitivity with (Q:=X)... }
      apply sub_top_chain in H6. apply sub_top_chain in H1.
      congruence.
    }
  *
    destruct H2 as [[W' H6]|[[W' H6]|[[U1' [U2' [H6a H6b]]]|H6]]].
    { inversion H6;subst.
      * pose proof binds_uniq _ _ _ H1 H5a H5b as C;inversion C.
      * apply binds_mid_eq in H5b. inversion H5b. apply uniq_from_wf_env...
    }
    { inversion H6;subst.
      * pose proof binds_uniq _ _ _ H1 H5a H5b as C;inversion C.
      * apply binds_mid_eq in H5a. inversion H5a. apply uniq_from_wf_env...
    }
    { assert (wf_env E) by (get_well_form;auto).
      pose proof binds_uniq _ _ _ H1 H5a H6b as C;inversion C.
    }
    { assert (sub E typ_top X0).
      { eapply sub_transitivity with (Q:=X)... }
      apply sub_top_chain in H6. apply sub_top_chain in H1.
      congruence.
    }
  *
    assert (sub E typ_top X).
    { eapply sub_transitivity with (Q:=X0)... }
    apply sub_top_chain in H5. apply sub_top_chain in H1.
    congruence.
Qed. *)


Lemma equiv_is_top_same_var': forall E (X X0:atom),
  sub E X X0 -> sub E X0 X -> 
  findX_top X0 (mk_benv E) = true /\ true = findX_top X (mk_benv E) \/
  findX_bot X0 (mk_benv E) = true /\ true = findX_bot X (mk_benv E) \/ X = X0.
Proof with auto.
  intros.
  pose proof suba_sub_tvar_chain H.
  pose proof suba_sub_tvar_chain H0.
  destruct H1 as [[W H5]|[[W H5]|[[U1 [U2 [H5a H5b]]]|[H5|H5]]]].
  *
    destruct H2 as [[W' H6]|[[W' H6]|[[U1 [U2 [H6a H6b]]]|[H6|H6]]]].
    { pose proof sub_tvar_chain_antisym H5 H6. subst... }
    { inversion H5;subst.
      * inversion H6;subst.
        { pose proof binds_uniq _ _ _ H1 H2 H4 as C;inversion C. }
        { apply binds_mid_eq in H2. inversion H2. apply uniq_from_wf_env... }
      * inversion H6;subst.
        { apply binds_mid_eq in H4. inversion H4. apply uniq_from_wf_env... }
        { assert (binds X (bind_sub X2) ( E0 ++ (X, bind_sub_lb X3) :: E3)).
          { rewrite H3... }
          apply binds_mid_eq in H8. inversion H8. apply uniq_from_wf_env... }
    }
    { inversion H5;subst.
      * pose proof binds_uniq _ _ _ H1 H6a H6b as C;inversion C.
      * apply binds_mid_eq in H6b. inversion H6b. apply uniq_from_wf_env...
    }
    { assert (sub E typ_top X0).
      { eapply sub_transitivity with (Q:=X)... }
      apply sub_top_chain in H6. apply sub_top_chain in H1.
      left. split; congruence.
    }
    { assert (sub E X typ_bot).
      { eapply sub_transitivity with (Q:=X0)... }
      apply sub_bot_chain in H6. apply sub_bot_chain in H1.
      right. left. split; congruence.
    }
  *
    destruct H2 as [[W' H6]|[[W' H6]|[[U1 [U2 [H6a H6b]]]|[H6|H6]]]].
    { inversion H5;subst.
      * inversion H6;subst.
        { pose proof binds_uniq _ _ _ H1 H2 H4 as C;inversion C. }
        { apply binds_mid_eq in H2. inversion H2. apply uniq_from_wf_env... }
      *  inversion H6;subst.
        { apply binds_mid_eq in H4. inversion H4. apply uniq_from_wf_env... }
        { assert (binds X0 (bind_sub_lb X2) ( E0 ++ (X0, bind_sub X3) :: E3)).
          { rewrite H3... }
          apply binds_mid_eq in H8. inversion H8. apply uniq_from_wf_env... }
    }
    { pose proof sub_tvar_chain_antisym_lb H5 H6. subst... }
    { inversion H5;subst.
      * pose proof binds_uniq _ _ _ H1 H6a H6b as C;inversion C.
      * apply binds_mid_eq in H6a. inversion H6a. apply uniq_from_wf_env...
    }
    { assert (sub E typ_top X0).
      { eapply sub_transitivity with (Q:=X)... }
      apply sub_top_chain in H6. apply sub_top_chain in H1.
      left;split; congruence.
    }
    { assert (sub E X typ_bot).
      { eapply sub_transitivity with (Q:=X0)... }
      apply sub_bot_chain in H6. apply sub_bot_chain in H1.
      right. left. split; congruence.
    }
  *
    destruct H2 as [[W' H6]|[[W' H6]|[[U1' [U2' [H6a H6b]]]|[H6|H6]]]].
    { inversion H6;subst.
      * pose proof binds_uniq _ _ _ H1 H5a H5b as C;inversion C.
      * apply binds_mid_eq in H5b. inversion H5b. apply uniq_from_wf_env...
    }
    { inversion H6;subst.
      * pose proof binds_uniq _ _ _ H1 H5a H5b as C;inversion C.
      * apply binds_mid_eq in H5a. inversion H5a. apply uniq_from_wf_env...
    }
    { assert (wf_env E) by (get_well_form;auto).
      pose proof binds_uniq _ _ _ H1 H5a H6b as C;inversion C.
    }
    { assert (sub E typ_top X0).
      { eapply sub_transitivity with (Q:=X)... }
      apply sub_top_chain in H6. apply sub_top_chain in H1.
      left;split;congruence.
    }
    { assert (sub E X typ_bot).
      { eapply sub_transitivity with (Q:=X0)... }
      apply sub_bot_chain in H6. apply sub_bot_chain in H1.
      right. left. split; congruence.
    }
  *
    assert (sub E typ_top X).
    { eapply sub_transitivity with (Q:=X0)... }
    apply sub_top_chain in H5. apply sub_top_chain in H1.
    left;split;congruence.
  *
    assert (sub E X0 typ_bot).
    { eapply sub_transitivity with (Q:=X)... }
    apply sub_bot_chain in H5. apply sub_bot_chain in H1.
    right. left. split; congruence.
Qed.


Lemma equiv_is_top_same: forall G A B n, 
  (* type4rec A -> type4rec B ->  *)
  equiv G A B -> is_top (mk_benv G) empty_menv A n = is_top (mk_benv G) empty_menv B n.
Proof with auto.
  intros.
  destruct H.
  induction H...
  (* -
    induction A...
    + inversion H0;inv_rt.
    + inversion H0;inv_rt. *)
  -
    inversion H0...
    subst. apply sub_top_chain in H0.
    simpl...
  -
    inversion H0...
    subst. apply sub_bot_chain in H0.
    apply is_bot_then_not_top in H0.
    simpl...
  - 
    inversion H0;simpl;subst...
    + assert (sub E X typ_bot). { apply sa_trans_tvar with (U:=U)... }
      apply sub_bot_chain in H4. apply is_bot_then_not_top in H4...

    + (* X0 <: X <: U <: X0 <: U0 <: X  *)
      assert (sub E X X0)... { apply sa_trans_tvar with (U:=U)... }
      destruct (equiv_is_top_same_var' H0 H4) as [[? ?]| [[? ?] | ?]];try congruence.
      apply is_bot_then_not_top in H5. symmetry in H6. apply is_bot_then_not_top in H6.
      congruence.

    + assert (wf_env E) by (get_well_form;auto).
      pose proof binds_uniq _ _ _ H2 H H3 as C;inversion C.
  
  -
    inversion H0;simpl;subst...
    + assert (sub E typ_top X)... { apply sa_trans_tvar_lb with (U:=U)... }
      apply sub_top_chain in H4...
    + 
      assert (wf_env E) by (get_well_form;auto).
      pose proof binds_uniq _ _ _ H2 H3 H. inversion H4.
    +
      (* X :> U >= X0 :> U0 >= X *)
      assert (sub E X0 X)... { apply sa_trans_tvar_lb with (U:=U)... }
      destruct (equiv_is_top_same_var' H0 H4) as [[? ?]| [[? ?] | ?]];try congruence.
      apply is_bot_then_not_top in H5. symmetry in H6. apply is_bot_then_not_top in H6.
      congruence.
Qed.

Lemma findX_findX_top: forall X G,
   findX_top X G = true -> findX X G = Some 1.
Proof with auto.
  intros.
  induction G...
  - inversion H.
  - destruct a. simpl in H. simpl. destruct m.
    + destruct (X == a)... inversion H.
    + destruct (X == a)...
    + destruct (X == a)...
Qed. 

Ltac inv_rt := idtac.

Ltac inv_lbub := try solve [get_well_form;match goal with
  | [H1: wf_env ?E,
      H2: binds ?X (bind_sub _) ?E,
      H3: binds ?X (bind_sub_lb _) ?E |- _] =>
      pose proof binds_uniq _ _ _ H1 H2 H3 as C;inversion C
end].


Lemma findX_findX_bot: forall X G,
   findX_bot X G = true -> findX X G = Some 1.
Proof with auto.
  intros.
  induction G...
  - inversion H.
  - destruct a. simpl in H. simpl. destruct m.
    + destruct (X == a)... inversion H.
    + destruct (X == a)...
    + destruct (X == a)...
Qed. 


Lemma equiv_is_bot_same: forall G A B n, 
  (* type4rec A -> type4rec B ->  *)
  equiv G A B -> is_bot (mk_benv G) empty_menv A n = is_bot (mk_benv G) empty_menv B n.
Proof with auto.
  intros.
  destruct H.
  induction H...
  -
    inversion H0...
    subst. apply sub_top_chain in H0.
    apply is_top_then_not_bot in H0.
    simpl...
  -
    inversion H0...
    subst. apply sub_bot_chain in H0.
    simpl...
  - 
    inversion H0;simpl;subst...
    + assert (sub E X typ_bot). { apply sa_trans_tvar with (U:=U)... }
      apply sub_bot_chain in H4...

    + (* X0 <: X <: U <: X0 <: U0 <: X  *)
      assert (sub E X X0)... { apply sa_trans_tvar with (U:=U)... }
      destruct (equiv_is_top_same_var' H0 H4) as [[? ?]| [[? ?] | ?]];try congruence.
      apply is_top_then_not_bot in H5. symmetry in H6. apply is_top_then_not_bot in H6.
      congruence.

    + assert (wf_env E) by (get_well_form;auto).
      pose proof binds_uniq _ _ _ H2 H H3 as C;inversion C.
  
  -
    inversion H0;simpl;subst...
    + assert (sub E typ_top X)... { apply sa_trans_tvar_lb with (U:=U)... }
      apply sub_top_chain in H4...
      apply is_top_then_not_bot in H4...
    + 
      assert (wf_env E) by (get_well_form;auto).
      pose proof binds_uniq _ _ _ H2 H3 H. inversion H4.
    +
      (* X :> U >= X0 :> U0 >= X *)
      assert (sub E X0 X)... { apply sa_trans_tvar_lb with (U:=U)... }
      destruct (equiv_is_top_same_var' H0 H4) as [[? ?]| [[? ?] | ?]];try congruence.
      apply is_top_then_not_bot in H5. symmetry in H6. apply is_top_then_not_bot in H6.
      congruence.
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
    { apply sub_top_chain in H. simpl. rewrite (findX_findX_top _ _ H)... }

  - intros B HB;induction HB;intros;
    try solve [simpl; lia| inversion H;inv_rt|inversion H0;inv_rt|
    inversion H1;inv_rt|
      inversion H2;inv_rt|inversion H3;inv_rt|inversion H4;inv_rt].
    { apply sub_bot_chain in H0. simpl. rewrite (findX_findX_bot _ _ H0)... }

  - intros B HB;induction HB;intros;
  try solve [simpl; lia| inversion H;inv_rt|inversion H0;inv_rt|
  inversion H1;inv_rt|
    inversion H2;inv_rt|inversion H3;inv_rt|inversion H4;inv_rt].
    + inversion H;subst. inversion H0;subst.
      inv_lbub.


  - intros B HB;induction HB;intros;
  try solve [simpl; lia| inversion H;inv_rt|inversion H0;inv_rt|
  inversion H1;inv_rt|
    inversion H2;inv_rt|inversion H3;inv_rt| inversion H4;inv_rt].
    + apply sub_top_chain in H0. simpl. rewrite (findX_findX_top _ _ H0)...
    + apply sub_bot_chain in H. simpl. rewrite (findX_findX_bot _ _ H)...
    + inversion H;subst. inversion H0;subst. inv_lbub.
    + pose proof equiv_is_top_same_var' H H0 as C.
      destruct C as [? |[? | ?]].
      { destruct H1. symmetry in H2. simpl.
        rewrite (findX_findX_top _ _ H1)...
        rewrite (findX_findX_top _ _ H2)...
      }
      { destruct H1. symmetry in H2. simpl.
        rewrite (findX_findX_bot _ _ H1)...
        rewrite (findX_findX_bot _ _ H2)...
      }
      { subst... }
    + inversion H;subst. inversion H0;subst. inv_lbub.
    + inversion H3;subst. inversion H4;subst. inv_lbub.
    + inversion H1;subst. inversion H2;subst. inv_lbub.
    + inversion H1;subst. inversion H2;subst. inv_lbub.
    + inversion H;subst. inversion H0;subst. inv_lbub.
  
  - intros B HB;induction HB;intros;
    try solve [simpl; lia| inversion H;inv_rt|inversion H0;inv_rt|
    inversion H1;inv_rt|
      inversion H2;inv_rt|inversion H3;inv_rt| inversion H4;inv_rt].
    + inversion H;inversion H0;subst. inv_lbub.
    + dependent destruction H0.
      (* { dependent destruction H2. inv_rt. } *)
      (* 2:{ inv_rt. } *)
      dependent destruction H.
      (* 2:{ inv_rt. } *)
      simpl. 
      rewrite IHHA1 with (B:=T0)...
      (* 2:{ apply type_to_rec. apply WF_type with (E:=E). get_well_form... } *)
      (* rewrite IHHA2 with (B:=)...
      { apply type_to_rec. apply WF_type with (E:=E). get_well_form... } *)
  - intros. rename T into A1.
    dependent destruction H4.
    { dependent destruction H6; inv_rt. }
    { inversion H6. inv_lbub. }
    (* 2:{ inv_rt. } *)
    dependent destruction H7.
    (* 2:{ inv_rt. } *)
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
    replace (1-0) with 1 in H2... simpl in H2.
    rewrite_env (X ~ mval 1 ++ mk_benv E) in H2.
    rewrite <- find_var_one with (X:=X) in H2...
    2:{ solve_notin. apply mk_benv_dom... }
    rewrite <- find_var_one with (X:=X) in H2...
    2:{ solve_notin. apply mk_benv_dom... }
    rewrite H2. f_equal...


    specialize (H0 _ H3 ((X ~ bind_sub typ_top) ++ E) H7 H10).

    rewrite_env (empty_menv ++ empty_menv) in H0...
    rewrite bindings_find in H0...
    rewrite bindings_add in H0... 
    2:{ constructor. apply WF_type with (E:=X ~ bind_sub typ_top ++ E)... }
    rewrite bindings_find in H0... 
    rewrite bindings_add with (A:=A2) in H0... 
    2:{ constructor. apply WF_type with (E:=X ~ bind_sub typ_top ++ E)... }
    unfold zero in H0. simpl in H0. rewrite H2' in H0.
    rewrite_env (X ~ mval 1 ++ mk_benv E) in H0.
    rewrite <- find_var_one with (X:=X) in H0...
    2:{ solve_notin. apply mk_benv_dom... }
    rewrite <- find_var_one with (Q:=A2) (X:=X) in H0...
    2:{ solve_notin. apply mk_benv_dom... }
    rewrite <- find_var_one with (Q:=open_tt A2 X) (X:=X) in H0...
    2:{ solve_notin. apply mk_benv_dom... }

    rewrite_env (empty_menv ++ empty_menv) in H0...
    rewrite bindings_find in H0...
    replace (bindings_rec (mk_benv E) (empty_menv ++ empty_menv) 0 X) with 2 in H0.
    2:{ simpl. rewrite findX_notin... apply mk_benv_dom... }
    simpl in H0. rewrite bindings_add with (A:=A2) in H0...
    simpl in H0. unfold zero in H0. rewrite Nat.sub_0_r in H0...
    destruct (findX_top X (mk_benv E)) eqn:Xtop...
    { exfalso. rewrite findX_top_notin in Xtop...
      inversion Xtop. apply mk_benv_dom... }
    destruct (findX_bot X (mk_benv E)) eqn:Xbot...
    { exfalso. rewrite findX_bot_notin in Xbot...
      inversion Xbot. apply mk_benv_dom... }

- 
  intros.
  dependent destruction H2.
  { dependent destruction H4;inv_rt. }
  { inversion H4. inv_lbub. }
  (* 2:{ inv_rt. } *)
  dependent destruction H3.
  (* 2:{ inv_rt. } *)
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


  rewrite equiv_is_bot_same with (B:=T2). 2:{ constructor... }
  destruct (is_bot (mk_benv E) empty_menv T2 0) eqn:Ttop.
  + (* bound is bot *)
    rewrite_env (nil ++ X ~ bind_sub T1 ++ E) in H3.
    apply sub_narrowing with (P:=typ_bot) in H3...
    2:{ apply sub_regular in H2_. destruct_hypos... }

    rewrite_env (nil ++ X ~ bind_sub T2 ++ E) in H2.
    apply sub_narrowing with (P:=typ_bot) in H2...
    2:{ apply sub_regular in H2_. destruct_hypos... }

    specialize (H0 _ H7 (X ~ bind_sub typ_bot ++ E) H2 H3).

    apply type4rec_to_type in H6.
    get_well_form...
    assert (WFC S1 0). { apply type_open_tt_WFC with (X:=X)... apply WF_type with (E:=X~bind_sub typ_bot ++ E)... }
    assert (WFC S2 0). { apply type_open_tt_WFC with (X:=X)... apply WF_type with (E:=X~bind_sub typ_bot ++ E)... }
    rewrite bindings_fvar_spec in H0...
    rewrite bindings_fvar_spec with (A:=S2) in H0...

  + (* bound is not bot *)
    rewrite_env (nil ++ X ~ bind_sub T1 ++ E) in H3.
    apply sub_narrowing with (P:=T2) in H3...

    specialize (H0 _ H7 (X ~ bind_sub T2 ++ E) H2 H3).

    apply type4rec_to_type in H6.
    get_well_form...
    assert (WFC S1 0). { apply type_open_tt_WFC with (X:=X)... apply WF_type with (E:=X~bind_sub T2 ++ E)... }
    assert (WFC S2 0). { apply type_open_tt_WFC with (X:=X)... apply WF_type with (E:=X~bind_sub T2 ++ E)... }
    rewrite bindings_fvar_spec in H0...
    rewrite bindings_fvar_spec with (A:=S2) in H0...
    rewrite Ttop in H0...

- 
  intros.
  dependent destruction H2.
  { dependent destruction H4;inv_rt. }
  { inversion H4. inv_lbub. }
  (* 2:{ inv_rt. } *)
  dependent destruction H3.
  (* 2:{ inv_rt. } *)
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


  rewrite equiv_is_top_same with (B:=T2). 2:{ constructor... }
  destruct (is_top (mk_benv E) empty_menv T2 0) eqn:Ttop.
  + (* bound is bot *)
    rewrite_env (nil ++ X ~ bind_sub_lb T1 ++ E) in H3.
    apply sub_narrowing_lb with (P:=typ_top) in H3...
    2:{ apply sub_regular in H2_. destruct_hypos... }

    rewrite_env (nil ++ X ~ bind_sub_lb T2 ++ E) in H2.
    apply sub_narrowing_lb with (P:=typ_top) in H2...
    2:{ apply sub_regular in H2_. destruct_hypos... }

    specialize (H0 _ H7 (X ~ bind_sub_lb typ_top ++ E) H2 H3).

    apply type4rec_to_type in H6.
    get_well_form...
    assert (WFC S1 0). { apply type_open_tt_WFC with (X:=X)... apply WF_type with (E:=X~bind_sub_lb typ_top ++ E)... }
    assert (WFC S2 0). { apply type_open_tt_WFC with (X:=X)... apply WF_type with (E:=X~bind_sub_lb typ_top ++ E)... }
    rewrite bindings_fvar_spec_lb in H0...
    rewrite bindings_fvar_spec_lb with (A:=S2) in H0...

  + (* bound is not bot *)
    rewrite_env (nil ++ X ~ bind_sub_lb T1 ++ E) in H3.
    apply sub_narrowing_lb with (P:=T2) in H3...

    specialize (H0 _ H7 (X ~ bind_sub_lb T2 ++ E) H2 H3).

    apply type4rec_to_type in H6.
    get_well_form...
    assert (WFC S1 0). { apply type_open_tt_WFC with (X:=X)... apply WF_type with (E:=X~bind_sub_lb T2 ++ E)... }
    assert (WFC S2 0). { apply type_open_tt_WFC with (X:=X)... apply WF_type with (E:=X~bind_sub_lb T2 ++ E)... }
    rewrite bindings_fvar_spec_lb in H0...
    rewrite bindings_fvar_spec_lb with (A:=S2) in H0...
    rewrite Ttop in H0...

-
  intros.
  dependent destruction H0.
  { dependent destruction H2; inv_rt. }
  { inversion H2. inv_lbub. }
  (* 2:{ inv_rt. } *)
  dependent destruction H1.
  (* 2:{ inv_rt. } *)
  dependent destruction H.
  simpl. f_equal. apply IHHA...

(* -
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
  rewrite H22... *)
Qed.

Lemma equiv_top_extend:
  forall E X k Q, X `notin` fv_tt Q ->
    equiv_top E Q = equiv_top ((X, k) :: E) Q.
Proof with auto.
  intros.
  destruct Q;simpl...
  destruct k.
  + destruct (a == X)...
    subst. simpl in H... exfalso...
  + destruct (a == X)...
    subst. simpl in H...
  + destruct (a == X)...
    subst. simpl in H... exfalso...
Qed.

Lemma equiv_bot_extend:
  forall E X k Q, X `notin` fv_tt Q ->
    equiv_bot E Q = equiv_bot ((X, k) :: E) Q.
Proof with auto.
  intros.
  destruct Q;simpl...
  destruct k.
  + destruct (a == X)...
    subst. simpl in H... exfalso...
  + destruct (a == X)...
    subst. simpl in H... exfalso...
  + destruct (a == X)...
    subst. simpl in H...
Qed.


Lemma findX_sem: forall E X Q,
  wf_env E ->
  binds X (bind_sub Q) E ->
  findX X (mk_benv E) = 
  if equiv_bot (mk_benv E) Q
  then Some 1
  else Some (S (bindings_rec (mk_benv E) nil 0 Q)).
Proof with auto.
  induction E.
  - intros. inversion H0.
  - intros. destruct H0.
    + destruct a. inversion H0;subst.
      simpl.
      destruct (equiv_bot (mk_benv E) Q) eqn:E0.
      * simpl. rewrite eq_dec_refl.
        destruct Q;try solve [inversion E0];simpl...
        destruct (a == X)... simpl in E0. rewrite E0...
      * replace ((X, mval (bindings_rec (mk_benv E) empty_menv 0 Q)) :: mk_benv E)
          with (mk_benv (X ~ bind_sub Q ++ E))...
        2:{ simpl. rewrite E0... }
        rewrite <- findX_extend_spec with (X:=X) (T:=bind_sub Q)...
        2:{ inversion H;subst. apply WF_type in H5... }
        2:{ rewrite_env (nil ++ X ~ bind_sub Q ++ E) in H.
          apply notin_from_wf_env in H... }
        simpl. rewrite E0. simpl. rewrite eq_dec_refl.
        destruct (equiv_bot
        ((X, mval (bindings_rec (mk_benv E) empty_menv 0 Q)) :: mk_benv E) Q) eqn:Qbot...
        destruct Q;try solve [inversion Qbot|inversion E0]...
        simpl in E0. simpl in Qbot. destruct (a ==X);try congruence.
    + destruct a.
      rewrite_alist (a ~ b ++ E).
      rewrite <- findX_extend_spec.
      2:{ apply WF_type with (E:=E). apply WF_from_binds_typ with (x:=X)...
          inversion H... }
      2:{ rewrite_alist (nil ++ (a, b):: E) in H.
          apply notin_from_wf_env_spec in H.
          assert (binds X (bind_sub Q) E)...
          apply notin_fv_tt_fv_env with (E:=E) (Y:=X)...
        }
      simpl. destruct b...
      * simpl. destruct (equiv_bot (mk_benv E) t) eqn:Tbot...
        { simpl. destruct (X == a)...
          { subst. inversion H;subst. apply binds_In in H0. exfalso... }
          { pose proof H0 as H0'. apply IHE in H0... 2:{ inversion H... }
            rewrite <- equiv_bot_extend with (X:=a)...
            inversion H;subst.
            pose proof WF_from_binds_typ _ _ H4 H0'.
            apply WF_imply_dom in H1...
          }
        }
        { simpl. destruct (X == a)...
          { subst. inversion H;subst. apply binds_In in H0. exfalso... }
          { pose proof H0 as H0'. apply IHE in H0... 2:{ inversion H... }
            rewrite <- equiv_bot_extend with (X:=a)...
            inversion H;subst.
            pose proof WF_from_binds_typ _ _ H4 H0'.
            apply WF_imply_dom in H1...
          }
        }
      * simpl. destruct (equiv_top (mk_benv E) t) eqn:Ttop.
        { simpl.  destruct (X == a).
          { subst. apply uniq_from_wf_env in H. inversion H;subst.
            apply binds_In in H0. congruence. }
          { rewrite IHE with (Q:=Q)... 2:{ inversion H;subst... }
            rewrite <- equiv_bot_extend with (X:=a) (k:=mtop)...
            inversion H;subst.
            pose proof WF_from_binds_typ _ _ H4 H0.
            apply WF_imply_dom in H1... }
        }
        { simpl.  destruct (X == a).
          { subst. apply uniq_from_wf_env in H. inversion H;subst.
            apply binds_In in H0. congruence. }
          { rewrite IHE with (Q:=Q)... 2:{ inversion H;subst... }
            rewrite <- equiv_bot_extend with (X:=a) ...
            inversion H;subst.
            pose proof WF_from_binds_typ _ _ H4 H0.
            apply WF_imply_dom in H1... }
        }
      * inversion H...
Qed.

Lemma findX_sem_lb: forall E X Q,
  wf_env E ->
  binds X (bind_sub_lb Q) E ->
  findX X (mk_benv E) = 
    if equiv_top (mk_benv E) Q
    then Some 1
    else Some (S (bindings_rec (mk_benv E) empty_menv 0 Q)).
Proof with auto.
  induction E.
  - intros. inversion H0.
  - intros. destruct H0.
    + destruct a. inversion H0;subst.
      simpl.
      destruct (equiv_top (mk_benv E) Q) eqn:E0.
      * simpl. rewrite eq_dec_refl.
        destruct Q;try solve [inversion E0];simpl...
        destruct (a == X)... simpl in E0. rewrite E0...
      * replace ((X, mval (bindings_rec (mk_benv E) empty_menv 0 Q)) :: mk_benv E)
          with (mk_benv (X ~ bind_sub_lb Q ++ E))...
        2:{ simpl. rewrite E0... }
        rewrite <- findX_extend_spec with (X:=X) (T:=bind_sub_lb Q)...
        2:{ inversion H;subst. apply WF_type in H5... }
        2:{ rewrite_env (nil ++ X ~ bind_sub_lb Q ++ E) in H.
          apply notin_from_wf_env_lb in H... }
        simpl. rewrite E0. simpl. rewrite eq_dec_refl.
        destruct (equiv_top
        ((X, mval (bindings_rec (mk_benv E) empty_menv 0 Q)) :: mk_benv E) Q) eqn:Qtop...
        destruct Q;try solve [inversion Qtop|inversion E0]...
        simpl in E0. simpl in Qtop. destruct (a ==X);try congruence.
    + destruct a.
      rewrite_alist (a ~ b ++ E).
      rewrite <- findX_extend_spec.
      2:{ apply WF_type with (E:=E). apply WF_from_binds_typ_lb with (x:=X)...
          inversion H... }
      2:{ rewrite_alist (nil ++ (a, b):: E) in H.
          apply notin_from_wf_env_spec in H.
          assert (binds X (bind_sub_lb Q) E)...
          apply notin_fv_tt_fv_env_lb with (E:=E) (Y:=X)...
        }
      destruct b...
      * simpl. destruct (equiv_bot (mk_benv E) t) eqn:Tbot.
        { simpl. destruct (X == a)...
          { subst. inversion H;subst. apply binds_In in H0. exfalso... }
          { pose proof H0 as H0'. apply IHE in H0... 2:{ inversion H... }
            rewrite <- equiv_top_extend with (X:=a)...
            inversion H;subst.
            pose proof WF_from_binds_typ_lb _ _ H4 H0'.
            apply WF_imply_dom in H1...
          }
        }
        { simpl. destruct (X == a)...
          { subst. inversion H;subst. apply binds_In in H0. exfalso... }
          { pose proof H0 as H0'. apply IHE in H0... 2:{ inversion H... }
            rewrite <- equiv_top_extend with (X:=a)...
            inversion H;subst.
            pose proof WF_from_binds_typ_lb _ _ H4 H0'.
            apply WF_imply_dom in H1...
          }
        }
      * simpl. destruct (equiv_top (mk_benv E) t) eqn:Ttop.
        { simpl.  destruct (X == a).
          { subst. apply uniq_from_wf_env in H. inversion H;subst.
            apply binds_In in H0. congruence. }
          { rewrite IHE with (Q:=Q)... 2:{ inversion H;subst... }
            rewrite <- equiv_top_extend with (X:=a) (k:=mtop)...
            inversion H;subst.
            pose proof WF_from_binds_typ_lb _ _ H4 H0.
            apply WF_imply_dom in H1... }
        }
        { simpl.  destruct (X == a).
          { subst. apply uniq_from_wf_env in H. inversion H;subst.
            apply binds_In in H0. congruence. }
          { rewrite IHE with (Q:=Q)... 2:{ inversion H;subst... }
            rewrite <- equiv_top_extend with (X:=a) ...
            inversion H;subst.
            pose proof WF_from_binds_typ_lb _ _ H4 H0.
            apply WF_imply_dom in H1... }
        }
      * inversion H...
Qed.

Lemma findX_equiv_top_sem: forall G,
  wf_env G ->
  (forall X, findX_top X (mk_benv G) = true -> sub G typ_top X)
  /\ forall T, equiv_top (mk_benv G) T  = true -> sub G typ_top T.
Proof with auto.
  intros.
  induction H.
  - split;intros; inversion H.
    simpl in H. induction T;try solve [inversion H]...
  -
    destruct IHwf_env. split;intros.
    + simpl in H4. destruct (equiv_bot (mk_benv E) T) eqn:Tbot.
      * simpl in H4.
        destruct (X0 == X);inversion H4.
        apply H2 in H4. 
        add_nil. apply Sub_weakening... constructor...
      * simpl in H4.
        destruct (X0 == X);inversion H4.
        apply H2 in H4. 
        add_nil. apply Sub_weakening... constructor...
    + simpl in H4. destruct (equiv_bot (mk_benv E) T) eqn:Tbot.
      * simpl in H4. destruct T0 ;try solve [inversion H4;inv_rt]...
        simpl in H4. destruct (a == X);inversion H4.
        apply H2 in H4.
        add_nil. apply Sub_weakening... constructor...
      * simpl in H4. destruct T0 ;try solve [inversion H4;inv_rt]...
        simpl in H4. destruct (a == X);inversion H4.
        apply H2 in H4.
        add_nil. apply Sub_weakening... constructor...
  - 
    destruct IHwf_env. split;intros.
    + simpl in H4. destruct (equiv_top (mk_benv E) T) eqn:Ttop.
      * simpl in H4. destruct (X0 == X).
        { subst. apply H3 in Ttop. apply sa_trans_tvar_lb with (U:=T)...
          add_nil. apply Sub_weakening... constructor...
        }
        { apply H2 in H4. 
          add_nil. apply Sub_weakening... constructor...
        }
      * simpl in H4. destruct (X0 == X);try congruence.
        { apply H2 in H4. 
          add_nil. apply Sub_weakening... constructor...
        }
    + simpl in H4. destruct (equiv_top (mk_benv E) T) eqn:Ttop.
      * apply H3 in Ttop. destruct T0 ;try solve [inversion H4;inv_rt]...
        simpl in H4. destruct (a == X).
        { subst. apply sa_trans_tvar_lb with (U:=T)...
          add_nil. apply Sub_weakening... constructor...  }
        { apply H2 in H4.
          add_nil. apply Sub_weakening... constructor...  }
      * destruct T0 ;try solve [inversion H4;inv_rt]...
        simpl in H4. destruct (a == X);try congruence...
        { apply H2 in H4.
          add_nil. apply Sub_weakening... constructor...  }
  - destruct IHwf_env. split;intros.
    + apply H2 in H4. add_nil. apply Sub_weakening... constructor...
    + apply H3 in H4. add_nil. apply Sub_weakening... constructor...
Qed.

Lemma equiv_top_sem: forall G T,
  wf_env G ->
  equiv_top (mk_benv G)  T = true ->
  sub G typ_top T.
Proof with auto.
  intros. pose proof findX_equiv_top_sem H.
  destruct H1...
Qed.

Lemma findX_top_sem: forall G X,
  wf_env G ->
  findX_top X (mk_benv G) = true ->
  sub G typ_top X.
Proof with auto.
  intros. pose proof findX_equiv_top_sem H.
  destruct H1...
Qed.


Lemma is_top_sem: forall G T,
  wf_env G ->
  is_top (mk_benv G) empty_menv  T 0 = true ->
  sub G typ_top T.
Proof with auto.
  intros. 
  induction T;try solve [inversion H0]...
  - simpl in H0.
    apply findX_top_sem...
Qed.

Lemma findX_top_next:
forall E X U, wf_env E ->
  binds X (bind_sub_lb U) E ->
  findX_top X (mk_benv E) = is_top (mk_benv E) empty_menv U 0.
Proof with auto.
  intros.
  induction H.
  - inversion H0.
  - inversion H0.
    + inversion H3;subst.
    + apply IHwf_env in H3.
      simpl. destruct H0.
      { inversion H0;subst. }
      destruct (equiv_bot (mk_benv E) T) eqn:Tbot.
      * simpl. rewrite H3.
        destruct (X == X0). { subst. apply binds_In in H0. exfalso. simpl in H0. congruence. }
        simpl in H0.
        rewrite is_top_mk_benv with (X:=X0) (T:=bind_sub typ_bot)...
        apply WF_from_binds_typ_lb in H0...
        apply WF_imply_dom in H0...
      * simpl. rewrite H3.
        destruct (X == X0). { subst. apply binds_In in H0. exfalso. simpl in H0. congruence. }
        simpl in H0.
        rewrite is_top_mk_benv with (X:=X0) (T:=bind_sub T)...
        simpl. rewrite Tbot...
        apply WF_from_binds_typ_lb in H0...
        apply WF_imply_dom in H0...
  - inversion H0.
    + inversion H3;subst.
      simpl. destruct U eqn:Ueqn;simpl;try rewrite eq_dec_refl...
      assert (a <> X). { apply WF_imply_dom in H1. intros C. subst. simpl in H1... }
      destruct (findX_top a (mk_benv E)) eqn:Atop.
      { simpl. rewrite eq_dec_refl. destruct (a == X);try congruence... }
      { simpl. rewrite eq_dec_refl. destruct (a == X);try congruence... }
    + simpl.
      assert (X <> X0). { intros C. subst. apply binds_In in H3... }
      destruct (equiv_top (mk_benv E) T) eqn:Ebot.
      { simpl. destruct (X == X0);try congruence.
        rewrite <- is_top_extend_benv...
        pose proof WF_from_binds_typ_lb _ _ H H3.
        apply WF_imply_dom in H5... }
      { simpl. destruct (X == X0);try congruence.
        rewrite <- is_top_extend_benv...
        pose proof WF_from_binds_typ_lb _ _ H H3.
        apply WF_imply_dom in H5... }
  - simpl. apply IHwf_env. inversion H0... inversion H3.
Qed.




Lemma is_not_top_sem: forall G T,
  wf_env G ->
  is_top (mk_benv G) empty_menv  T 0 = false ->
  ~ sub G typ_top T.
Proof with auto.
  intros. intros C. dependent induction C; 
  try solve [inversion H0]...
  - simpl in H0. rewrite findX_top_next with (U:=U)  in H0 ...
  (* - inv_rt. *)
Qed.



Lemma findX_equiv_bot_sem: forall G,
  wf_env G ->
  (forall X, findX_bot X (mk_benv G) = true -> sub G X typ_bot)
  /\ forall T, equiv_bot (mk_benv G) T  = true -> sub G T typ_bot.
Proof with auto.
  intros.
  induction H.
  - split;intros; inversion H.
    simpl in H. induction T;try solve [inversion H]...
  -
    destruct IHwf_env. split;intros.
    + simpl in H4. destruct (equiv_bot (mk_benv E) T) eqn:Tbot.
      * simpl in H4.
        destruct (X0 == X).
        { subst. apply H3 in Tbot. apply sa_trans_tvar with (U:=T)...
          add_nil. apply Sub_weakening... constructor...
        }
        { apply H2 in H4. 
          add_nil. apply Sub_weakening... constructor...
        }
      * simpl in H4.
        destruct (X0 == X);try congruence.
        { apply H2 in H4. 
          add_nil. apply Sub_weakening... constructor...
        }
    + simpl in H4. destruct (equiv_bot (mk_benv E) T) eqn:Tbot.
      * simpl in H4. destruct T0 ;try solve [inversion H4;inv_rt]...
        simpl in H4. destruct (a == X);inversion H4.
        { subst. apply sa_trans_tvar with (U:=T)...
          add_nil. apply Sub_weakening... constructor...  }
        { apply H2 in H4.
          add_nil. apply Sub_weakening... constructor...  }
      * simpl in H4. destruct T0 ;try solve [inversion H4;inv_rt]...
        simpl in H4. destruct (a == X);try congruence...
        { apply H2 in H4.
          add_nil. apply Sub_weakening... constructor...  }
  - 
    destruct IHwf_env. split;intros.
    + simpl in H4. destruct (equiv_top (mk_benv E) T) eqn:Ttop.
      * simpl in H4. destruct (X0 == X);try congruence...
        apply H2 in H4. 
        add_nil. apply Sub_weakening... constructor...
      * simpl in H4. destruct (X0 == X);try congruence.
        apply H2 in H4. 
        add_nil. apply Sub_weakening... constructor...
    + simpl in H4. destruct (equiv_top (mk_benv E) T) eqn:Ttop.
      * destruct T0 ;try solve [inversion H4;inv_rt]...
        simpl in H4. destruct (a == X);try congruence.
        { apply H2 in H4.
          add_nil. apply Sub_weakening... constructor...  }
      * destruct T0 ;try solve [inversion H4;inv_rt]...
        simpl in H4. destruct (a == X);try congruence...
        { apply H2 in H4.
          add_nil. apply Sub_weakening... constructor...  }
  - destruct IHwf_env. split;intros.
    + apply H2 in H4. add_nil. apply Sub_weakening... constructor...
    + apply H3 in H4. add_nil. apply Sub_weakening... constructor...
Qed.

Lemma equiv_bot_sem: forall G T,
  wf_env G ->
  equiv_bot (mk_benv G)  T = true ->
  sub G T typ_bot.
Proof with auto.
  intros. pose proof findX_equiv_bot_sem H.
  destruct H1...
Qed.

Lemma findX_bot_sem: forall G X,
  wf_env G ->
  findX_bot X (mk_benv G) = true ->
  sub G X typ_bot.
Proof with auto.
  intros. pose proof findX_equiv_bot_sem H.
  destruct H1...
Qed.


Lemma is_bot_sem: forall G T,
  wf_env G ->
  is_bot (mk_benv G) empty_menv  T 0 = true ->
  sub G T typ_bot.
Proof with auto.
  intros. 
  induction T;try solve [inversion H0]...
  - simpl in H0.
    apply findX_bot_sem...
Qed.


Lemma is_bot_extend_benv: forall G E A n X k, 
  X `notin` fv_tt A ->
  is_bot G E A n = is_bot ((X, k)::G) E A n.
Proof with auto.
  intros. simpl. destruct k...
  + destruct A... simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
  + destruct A... simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
  + destruct A... simpl. destruct (a == X)... subst. exfalso. apply H. simpl...
Qed.



Lemma findX_bot_next:
forall E X U, wf_env E ->
  binds X (bind_sub U) E ->
  findX_bot X (mk_benv E) = is_bot (mk_benv E) empty_menv U 0.
Proof with auto.
  intros.
  induction H.
  - inversion H0.
  - inversion H0.
    + inversion H3;subst.
      simpl. destruct U eqn:Ueqn;simpl;try rewrite eq_dec_refl...
      assert (a <> X). { apply WF_imply_dom in H1. intros C. subst. simpl in H1... }
      destruct (findX_bot a (mk_benv E)) eqn:Atop.
      { simpl. rewrite eq_dec_refl. destruct (a == X);try congruence... }
      { simpl. rewrite eq_dec_refl. destruct (a == X);try congruence... }
    + simpl.
      assert (X <> X0). { intros C. subst. apply binds_In in H3... }
      destruct (equiv_bot (mk_benv E) T) eqn:Ebot.
      { simpl. destruct (X == X0);try congruence.
        rewrite <- is_bot_extend_benv...
        pose proof WF_from_binds_typ _ _ H H3.
        apply WF_imply_dom in H5... }
      { simpl. destruct (X == X0);try congruence.
        rewrite <- is_bot_extend_benv...
        pose proof WF_from_binds_typ _ _ H H3.
        apply WF_imply_dom in H5... }
    
  
  - inversion H0.
    + inversion H3;subst.
    + simpl.
      apply IHwf_env in H3.
      simpl. destruct H0.
      { inversion H0;subst. }
      destruct (equiv_top (mk_benv E) T) eqn:Tbot.
      * simpl. rewrite H3.
        destruct (X == X0). { subst. apply binds_In in H0. exfalso. simpl in H0. congruence. }
        simpl in H0.
        rewrite is_bot_mk_benv with (X:=X0) (T:=bind_sub_lb typ_top)...
        apply WF_from_binds_typ in H0...
        apply WF_imply_dom in H0...
      * simpl. rewrite H3.
        destruct (X == X0). { subst. apply binds_In in H0. exfalso. simpl in H0. congruence. }
        simpl in H0.
        rewrite is_bot_mk_benv with (X:=X0) (T:=bind_sub_lb T)...
        simpl. rewrite Tbot...
        apply WF_from_binds_typ in H0...
        apply WF_imply_dom in H0...

  - simpl. apply IHwf_env. inversion H0... inversion H3.
Qed.



Lemma is_not_bot_sem: forall G T,
  wf_env G ->
  is_bot (mk_benv G) empty_menv  T 0 = false ->
  ~ sub G T typ_bot.
Proof with auto.
  intros. intros C. dependent induction C; 
  try solve [inversion H0]...
  - simpl in H0. rewrite findX_bot_next with (U:=U)  in H0 ...
  (* - inv_rt. *)
Qed.



Ltac get_same_bind := match goal with
  | [H1: wf_env ?E,
      H2: binds ?X (bind_sub _) ?E,
      H3: binds ?X (bind_sub _) ?E |- _] =>
      let C := fresh "C" in
      pose proof binds_uniq _ _ _ H1 H2 H3 as C;inversion C;subst
  | [H1: wf_env ?E,
      H2: binds ?X (bind_sub_lb _) ?E,
      H3: binds ?X (bind_sub_lb _) ?E |- _] =>
      let C := fresh "C" in
      pose proof binds_uniq _ _ _ H1 H2 H3 as C;inversion C;subst
  | [H1: wf_env ?E,
    H2: binds ?X _ ?E,
    H3: binds ?X _ ?E |- _] =>
    let C := fresh "C" in
    pose proof binds_uniq _ _ _ H1 H2 H3 as C;inversion C;subst
end.



Ltac get_same_bind_for X := match goal with
  | [H1: wf_env ?E,
      H2: binds X (bind_sub _) ?E,
      H3: binds X (bind_sub _) ?E |- _] =>
      let C := fresh "C" in
      pose proof binds_uniq _ _ _ H1 H2 H3 as C;inversion C;subst
  | [H1: wf_env ?E,
      H2: binds X (bind_sub_lb _) ?E,
      H3: binds X (bind_sub_lb _) ?E |- _] =>
      let C := fresh "C" in
      pose proof binds_uniq _ _ _ H1 H2 H3 as C;inversion C;subst
  | [H1: wf_env ?E,
    H2: binds X _ ?E,
    H3: binds X _ ?E |- _] =>
    let C := fresh "C" in
    pose proof binds_uniq _ _ _ H1 H2 H3 as C;inversion C;subst
end.





Lemma subtyping_dec : forall k A B E,
bindings_rec (mk_benv E) nil 0 A + 
bindings_rec (mk_benv E) nil 0 B <= k ->
{sub E A B} + {~ sub E A B}.
Proof with auto.
induction k.
-
  induction A;intros;try solve [unfold bindings in *;exfalso;simpl in *;lia]...
  + pose proof bindings_rec_ge_1 (mk_benv E) empty_menv 0 a. lia.
  + simpl in H. destruct (is_bot (mk_benv E) empty_menv A1 0); lia.
  + simpl in H. destruct (is_top (mk_benv E) empty_menv A1 0); lia.

-
  intros A B. destruct (is_var A) eqn:EvarA, (is_var B) eqn:EvarB.
  { (* A, B is variable *)
    intros. destruct A;try solve [inversion EvarA].
    destruct B;try solve [inversion EvarB].
    rename a0 into b.
    destruct (wf_env_dec E).
    2:{ right. intros C. apply sub_regular in C. destruct C... }
    destruct (binds_key_dec E a).
    2:{ right. intros C. get_well_form. inversion H1;exfalso;eapply n;eassumption... }
    destruct (binds_key_dec E b).
    2:{ right. intros C. get_well_form. inversion H2;exfalso;eapply n;eassumption... }
    destruct s as [A HbA], s0 as [B HbB].
    pose proof uniq_from_wf_env w as u.
    destruct A as [A |A | A].
    + (* A is upper bounded: a <: A *)
      simpl in H. rewrite (findX_sem _ _ w HbA) in H.
      destruct (equiv_bot (mk_benv E) A) eqn:Abot.
      {
        (* A is bot *)
        destruct (wf_dec (E:=E) b)...
        { left. apply equiv_bot_sem in Abot...
          apply sa_trans_tvar with (U:=A)...
          apply sub_transitivity with (Q:=typ_bot)...
        }
        { right. intros C. get_well_form... }
      }
      (* A is other type *)
      destruct B as [B | B | B].
      * (* B is upper bounded b <: B *)
        rewrite (findX_sem _ _ w HbB) in H.
        destruct (equiv_bot (mk_benv E) B) eqn:Bbot.
        { (* B is equivalent to bot *)
          destruct (EqDec_eq a b). (* decide a = b *)
          { left. inversion e; subst. apply sa_fvar...
            apply WF_var with (U:=B)... }
          destruct (IHk A b E)... (* decide a <: B *)
          { simpl in *. rewrite (findX_sem _ _ w HbB)... rewrite Bbot. lia. }
          - left. apply sa_trans_tvar with (U:=A)...
          - right. intros C;inversion C;subst;get_same_bind...
        }
        { (* B is not equivalent to bot *)
          destruct (EqDec_eq a b). (* decide a = b *)
          { left. inversion e; subst. apply sa_fvar...
            apply WF_var with (U:=B)... }
          destruct (IHk A b E).  (* decide A <: b *)
          { simpl in *. rewrite (findX_sem _ _ w HbB)... rewrite Bbot. simpl. lia. }
          - left. apply sa_trans_tvar with (U:=A)...
          - right. intros C. inversion C;subst...
            { pose proof binds_uniq _ _ _ w HbA H1 as Hb; inversion Hb;subst... }
            { pose proof binds_uniq _ _ _ w HbB H1 as Hb; inversion Hb;subst... }
        }
      * (* B is lower bounded B <: b *)
        rewrite (findX_sem_lb _ _ w HbB) in H.
        destruct (equiv_top (mk_benv E) B) eqn:Btop.
        { (* B is equivalent to top *)
          left. apply equiv_top_sem in Btop...
          apply sa_trans_tvar_lb with (U:=B)...
          apply sub_transitivity with (Q:=typ_top)...
          apply sa_top... apply WF_var with (U:=A)... }
        { (* B is not equivalent to top *)
          destruct (IHk A B E). (* decide A <: B *)
          { simpl in H. simpl. lia. }
          - left. apply sa_trans_tvar with (U:=A)...
            apply sa_trans_tvar_lb with (U:=B)...
          - destruct (IHk A b E). (* decide A <: b *)
            { simpl. simpl in H. rewrite (findX_sem_lb _ _ w HbB)...
              rewrite Btop. lia. }
            { left. apply sa_trans_tvar with (U:=A)... }
            destruct (IHk a B E). (* decide a <: B*)
            { simpl. simpl in H. rewrite (findX_sem _ _ w HbA)...
              rewrite Abot. lia. }
            { left. apply sa_trans_tvar_lb with (U:=B)... }
            { right. intros C. inversion C;subst...
              + inv_lbub.
              + get_same_bind...
              + get_same_bind...
            }
        }
      * (* B is type *)
        right. intros C. inversion C;subst...
        { get_same_bind. }
        { get_well_form. inversion H3;subst; get_same_bind_for b ... }
        { get_same_bind... }
    + (* A is lower bounded: A <: a *)
      simpl in H. rewrite (findX_sem_lb _ _ w HbA) in H.
      destruct (equiv_top (mk_benv E) A) eqn:Atop.
      { (* A is top bounded variable *)
        destruct B as [B | B | B].
        * (* B is upper bounded b <: B *)
          right. intro C;inversion C;subst;get_same_bind...
        * (* B is lower bounded B <: b *)
          rewrite (findX_sem_lb _ _ w HbB) in H.
          destruct (equiv_top (mk_benv E) B) eqn:Btop.
          { (* B is equivalent to top *)
            left. apply equiv_top_sem in Btop...
            apply sa_trans_tvar_lb with (U:=B)...
            apply sub_transitivity with (Q:=typ_top)...
            apply sa_top... apply WF_var_lb with (U:=A)... }
          { (* B is not equivalent to top *)
            destruct (EqDec_eq a b). (* decide a = b *)
            { left. inversion e; subst. apply sa_fvar...
              apply WF_var_lb with (U:=B)... }
            destruct (IHk a B E)... (* decide a <: B *)
            { simpl in *. rewrite (findX_sem_lb _ _ w HbA)... rewrite Atop. lia. }
            - left. apply sa_trans_tvar_lb with (U:=B)...
            - right. intros C;inversion C;subst;get_same_bind...
          }
        * (* B is type *)
          right. intros C. inversion C;subst;get_same_bind...
      }
      { (* A is not top bounded, the same procedure as above *)
        destruct B as [B | B | B].
        * (* B is upper bounded b <: B *)
          right. intro C;inversion C;subst;get_same_bind...
        * (* B is lower bounded B <: b *)
          rewrite (findX_sem_lb _ _ w HbB) in H.
          destruct (equiv_top (mk_benv E) B) eqn:Btop.
          { (* B is equivalent to top *)
            left. apply equiv_top_sem in Btop...
            apply sa_trans_tvar_lb with (U:=B)...
            apply sub_transitivity with (Q:=typ_top)...
            apply sa_top... apply WF_var_lb with (U:=A)... }
          { (* B is not equivalent to top *)
            destruct (EqDec_eq a b). (* decide a = b *)
            { left. inversion e; subst. apply sa_fvar...
              apply WF_var_lb with (U:=B)... }
            destruct (IHk a B E)... (* decide a <: B *)
            { simpl in *. rewrite (findX_sem_lb _ _ w HbA)... rewrite Atop. lia. }
            - left. apply sa_trans_tvar_lb with (U:=B)...
            - right. intros C;inversion C;subst;get_same_bind...
          }
        * (* B is type *)
          right. intros C. inversion C;subst;get_same_bind...
      }
    + (* A is type *)
      right. intros C. get_well_form. inversion H1;subst;get_same_bind...
  }
  { (* A is variable, B is not *)
    intros.
    destruct A;try solve [inversion EvarA].
    destruct (wf_env_dec E).
    2:{ right. intros C. apply sub_regular in C. destruct C... }
    destruct (binds_key_dec E a).
    2:{ right. intros C. get_well_form. inversion H1;exfalso;eapply n;eassumption... }
    destruct s as [A HbA].
    pose proof uniq_from_wf_env w as u.
    destruct A as [A |A | A].
    + (* A is upper bounded: a <: A *)
      simpl in H. rewrite (findX_sem _ _ w HbA) in H.
      destruct (equiv_bot (mk_benv E) A) eqn:Abot.
      {
        (* A is bot *)
        destruct (wf_dec (E:=E) B)...
        { left. apply equiv_bot_sem in Abot...
          apply sa_trans_tvar with (U:=A)...
          apply sub_transitivity with (Q:=typ_bot)...
        }
        { right. intros C. get_well_form... }
      }
      destruct (IHk A B E)... (* decide A <: B *)
      { lia. }
      - left. apply sa_trans_tvar with (U:=A)...
      - right. intros C;inversion C;subst;inversion EvarB...
        { apply n. apply sa_top... apply WF_from_binds_typ with (x:=a)... }
        { get_same_bind... }
    + (* A is lower bounded: A <: a *)
      destruct (EqDec_eq typ_top B). (* decide top = B *)
      { left. subst. apply sa_top... apply WF_var_lb with (U:=A)... }
      { right. intros C;inversion C;subst;inversion EvarB...
        { get_same_bind... }
      }
    + (* A is type *)
      right. intros C. get_well_form. inversion H1;subst;get_same_bind...
  }
  { (* B is variable, A is not *)
    intros.
    destruct B;try solve [inversion EvarB]. rename a into b.
    destruct (wf_env_dec E).
    2:{ right. intros C. apply sub_regular in C. destruct C... }
    destruct (binds_key_dec E b).
    2:{ right. intros C. get_well_form. inversion H2;exfalso;eapply n;eassumption... }
    destruct s as [B HbB].
    pose proof uniq_from_wf_env w as u.
    destruct B as [B |B | B].
    + (* B is upper bounded: b <: B *)
      simpl in H. rewrite (findX_sem _ _ w HbB) in H.
      destruct (equiv_bot (mk_benv E) B) eqn:Bbot.
      { (* B is bot bounded *)
        destruct (EqDec_eq A typ_bot).
        { left. subst. apply sa_bot... apply WF_var with (U:=B)... }
        right. intros C.
        assert (sub E A typ_bot). { apply equiv_bot_sem in Bbot...
          apply sub_transitivity with (Q:=B)...
          apply sub_transitivity with (Q:=b)...
          apply sa_trans_tvar with (U:=B)...
          apply Reflexivity... get_well_form... }
        inversion H0;subst... inversion EvarA.
      }
      { (* B is not bot bounded *)
        destruct (EqDec_eq A typ_bot).
        { left. subst. apply sa_bot... apply WF_var with (U:=B)... }
        destruct (EqDec_eq A b).
        { left. subst. apply sa_fvar... apply WF_var with (U:=B)... }
        right. intros C. inversion C;subst...
        { inversion EvarA. }
        { inv_lbub. }
      }
    + (* B is lower bounded: B <: b *)
      simpl in H. rewrite (findX_sem_lb _ _ w HbB) in H.
      destruct (equiv_top (mk_benv E) B) eqn:Btop.
      { (* B is top bounded *)
        destruct (wf_dec (E:=E) A)... (* decide A is well-formed *)
        - left. apply equiv_top_sem in Btop...
          apply sub_transitivity with (Q:=typ_top)...
          apply sa_trans_tvar_lb with (U:=B)...
        - right. intros C. get_well_form...
      }
      { (* B is not top bounded *)
        destruct (IHk A B E). (* decide A <: B *)
        { lia. }
        - left. subst. apply sa_trans_tvar_lb with (U:=B)...
        - destruct (EqDec_eq A typ_bot).
          { left. subst. apply sa_bot... apply WF_var_lb with (U:=B)... }
          right. intros C;inversion C;subst;inversion EvarA...
          { get_same_bind... }
      }
    + (* B is type *)
      right. intros C. get_well_form. inversion H2;subst;get_same_bind...
  }
  (* Now, A and B are neither variables *)
  induction A.
  
+
  induction B;intros;try solve [ solve_right_dec | solve_top_dec E]...

+
  induction B;intros;try solve [ solve_right_dec | solve_top_dec E]...

+
  intros.
  solve_top_dec E.
  destruct (wf_dec (E:=E) B)... { apply uniq_from_wf_env... }
  right. intros C. get_well_form...


+
  induction B;intros;try solve [ solve_right_dec | solve_top_dec E]...
  right. intros C. inversion C;subst. inversion H1.

+
  inversion EvarA.

+ 
  intros. simpl in H.
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
    destruct (is_bot (mk_benv E) empty_menv A1 0) eqn:Abot.
    ++ (* bound is bot *)
      destruct (is_bot (mk_benv E) empty_menv B1 0) eqn:Bbot...
      2:{ (* then B1 must also be bot *)
        solve_right_dec. subst. apply is_not_bot_sem in Bbot... 2:{ get_well_form... }
        apply Bbot. apply is_bot_sem in Abot... 2:{ get_well_form... }
        apply sub_transitivity with (Q:=A1)...
      }

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
      rewrite Bbot in *.

      specialize (IHk (open_tt A2 X1) (open_tt B2 X1)
      (X1 ~ bind_sub B1 ++ E)).
      (* simpl in IHk. *)
      (* assert (equiv_top (mk_benv E) B1 = true) as Btop2.
      { destruct B1;try solve [inversion Btop]... }
      rewrite Btop2 in IHk. *)

      destruct (wf_dec (E:=E) A1)...
      2:{ right. intros C. apply sub_regular in C. destruct C as [? [? ?]]...
          inversion H1;subst... }
      destruct (wf_dec (E:=E) B1)...
      2:{ right. intros C. apply sub_regular in C. destruct C as [? [? ?]]...
          inversion H2;subst... }

      rewrite bindings_fvar_spec in IHk...
      (* rewrite <- bindings_fvar_spec with (X:=X1)in H... *)
      2:{ apply type_open_tt_WFC with (X:=X1)... apply WF_type in w0... }
      2:{ get_well_form... get_type... }
      
      rewrite bindings_fvar_spec in IHk...
      2:{ apply type_open_tt_WFC with (X:=X1)... apply WF_type in w1... }
      2:{ get_well_form... get_type... }
      rewrite Bbot in *. 

      (* assert (Eq: bindings_rec (mk_benv E) empty_menv 0 A1 = bindings_rec (mk_benv E) empty_menv 0 B1).
      { apply equiv_measure...
        { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
        { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
      }
      rewrite Eq in *. *)

      destruct IHk.
      { simpl in H. simpl. lia. }
      { left.
        apply sa_all with (L:={{X1}} \u fv_tt A1 \u fv_tt A2 \u fv_tt B1 \u fv_tt B2 \u dom E);intros...
        (* { apply Reflexivity... } { apply Reflexivity... } *)
        { apply sub_transitivity with (Q:=typ_bot)... apply is_bot_sem... }
        { apply sub_transitivity with (Q:=typ_bot)... apply is_bot_sem... }
        apply sub_replacing_var with (X:=X1)...
      }
      { right. intros. intros C.
        inversion C;inv_rt. subst. pick_fresh X2.
        specialize_x_and_L X2 L.
        apply n. apply sub_replacing_var with (X:=X2)... }




    ++ (* bound is not bot *)
      destruct (is_bot (mk_benv E) empty_menv B1 0) eqn:Bbot...
      { (* then B1 must also not be bot *)
        solve_right_dec. subst. apply is_bot_sem in Bbot... 2:{ get_well_form... }
        pose proof sub_transitivity H5 Bbot.
        inversion H0;inv_rt;subst;try solve [inversion Abot]...
        apply is_not_bot_sem in Abot... get_well_form... 
      }
      destruct (IHk A1 B1 E); try solve [solve_right_dec].
      { simpl in H. rewrite Bbot in *. lia. }
      destruct (IHk B1 A1 E); try solve [solve_right_dec].
      { simpl in H. rewrite Bbot in *. lia. }

      destruct (wf_env_dec E).
      2:{ right. intros C. apply sub_regular in C. destruct C as [? [? ?]]... }
      pose proof uniq_from_wf_env w as u.

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

      
      rewrite bindings_fvar_spec with (X:=X1)in IHk...
      2:{ apply type_open_tt_WFC with (X:=X1)... apply WF_type in w0... }
      2:{ get_well_form... }
      2:{ get_well_form... apply WF_type in H1... }
      
      rewrite bindings_fvar_spec with (X:=X1)in IHk...
      2:{ apply type_open_tt_WFC with (X:=X1)... apply WF_type in w1... }
      2:{ get_well_form... }
      2:{ get_well_form... apply WF_type in H5... } 
      rewrite Bbot in *.

      assert (Eq: bindings_rec (mk_benv E) empty_menv 0 A1 = bindings_rec (mk_benv E) empty_menv 0 B1).
      { apply equiv_measure...
        { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
        { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
      }
      rewrite Eq in *.

      destruct IHk.
      { simpl in H. simpl. lia. }
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
  * solve_top_dec E. solve_top_wfs_dec E (typ_all_lb A1 A2).

  * destruct (is_top (mk_benv E) empty_menv A1 0) eqn:Atop...

    ++ (* bound is top *)
      destruct (is_top (mk_benv E) empty_menv B1 0) eqn:Btop...
      2:{ (* then B1 must also be bot *)
        solve_right_dec. subst. apply is_not_top_sem in Btop... 2:{ get_well_form... }
        apply Btop. apply is_top_sem in Atop... 2:{ get_well_form... }
        apply sub_transitivity with (Q:=A1)...
      }

      destruct (wf_env_dec E).
      2:{ right. intros C. apply sub_regular in C. destruct C as [? [? ?]]... }
      pose proof uniq_from_wf_env w as u.
      (* destruct (wf_dec A1 u);try solve [solve_right_dec]. *)
  
      pick_fresh X1.
      assert (uniq ((X1 ~ bind_sub_lb A1) ++ E)) as u2...
      assert (uniq ((X1 ~ bind_sub_lb B1) ++ E)) as u3...
      destruct (wf_dec (open_tt A2 X1) u2).
      2:{ right. intros C.
          apply sub_regular in C. destruct C as [? [? ?]].
          inversion H1;subst.
          pick_fresh X2. specialize_x_and_L X2 L.
          apply n. apply WF_replacing_var_lb with (X:=X2)... }
      destruct (wf_dec (open_tt B2 X1) u3).
      2:{ right. intros C.
          apply sub_regular in C. destruct C as [? [? ?]].
          inversion H2;subst.
          pick_fresh X2. specialize_x_and_L X2 L.
          apply n. apply WF_replacing_var_lb with (X:=X2)... }
      
  
      clear IHA1 IHA2 IHB1 IHB2. simpl in H.
      rewrite Btop in *.
  
      specialize (IHk (open_tt A2 X1) (open_tt B2 X1)
      (X1 ~ bind_sub_lb B1 ++ E)).
       (* simpl in IHk. *)
      (* assert (equiv_top (mk_benv E) B1 = true) as Btop2.
      { destruct B1;try solve [inversion Btop]... }
      rewrite Btop2 in IHk. *)

      destruct (wf_dec (E:=E) A1)...
      2:{ right. intros C. apply sub_regular in C. destruct C as [? [? ?]]...
          inversion H1;subst... }
      destruct (wf_dec (E:=E) B1)...
      2:{ right. intros C. apply sub_regular in C. destruct C as [? [? ?]]...
          inversion H2;subst... }
  
      rewrite bindings_fvar_spec_lb in IHk...
      (* rewrite <- bindings_fvar_spec with (X:=X1)in H... *)
      2:{ apply type_open_tt_WFC with (X:=X1)... apply WF_type in w0... }
      2:{ get_well_form... get_type... }
      
      rewrite bindings_fvar_spec_lb in IHk...
      2:{ apply type_open_tt_WFC with (X:=X1)... apply WF_type in w1... }
      2:{ get_well_form... get_type... }
      rewrite Btop in *. 
  
      (* assert (Eq: bindings_rec (mk_benv E) empty_menv 0 A1 = bindings_rec (mk_benv E) empty_menv 0 B1).
      { apply equiv_measure...
        { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
        { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
      }
      rewrite Eq in *. *)
  
      destruct IHk.
      { simpl in H. simpl. lia. }
      { left.
        apply sa_all_lb with (L:={{X1}} \u fv_tt A1 \u fv_tt A2 \u fv_tt B1 \u fv_tt B2 \u dom E);intros...
        (* { apply Reflexivity... } { apply Reflexivity... } *)
        { apply sub_transitivity with (Q:=typ_top)... apply is_top_sem... }
        { apply sub_transitivity with (Q:=typ_top)... apply is_top_sem... }
        apply sub_replacing_var_lb with (X:=X1)...
      }
      { right. intros. intros C.
        inversion C;inv_rt. subst. pick_fresh X2.
        specialize_x_and_L X2 L.
        apply n. apply sub_replacing_var_lb with (X:=X2)... }

    ++ (* bound is not top*)
    destruct (is_top (mk_benv E) empty_menv B1 0) eqn:Btop...
    { (* then B1 must also not be top *)
      solve_right_dec. subst. apply is_top_sem in Btop... 2:{ get_well_form... }
      pose proof sub_transitivity Btop H6.
      inversion H0;inv_rt;subst;try solve [inversion Atop]...
      apply is_not_top_sem in Atop... get_well_form... 
    }
    destruct (IHk A1 B1 E); try solve [solve_right_dec].
    { simpl in H. rewrite Btop in *. lia. }
    destruct (IHk B1 A1 E); try solve [solve_right_dec].
    { simpl in H. rewrite Btop in *. lia. }

    (* destruct (EqDec_eq A1 B1);try solve [solve_right_dec]. *)
    (* rename A1 into A. *)
    (* rename A2 into B1. *)

    destruct (wf_env_dec E).
    2:{ right. intros C. apply sub_regular in C. destruct C as [? [? ?]]... }
    pose proof uniq_from_wf_env w as u.
    (* destruct (wf_dec A1 u);try solve [solve_right_dec]. *)

    pick_fresh X1.
    assert (uniq ((X1 ~ bind_sub_lb A1) ++ E)) as u2...
    assert (uniq ((X1 ~ bind_sub_lb B1) ++ E)) as u3...
    destruct (wf_dec (open_tt A2 X1) u2).
    2:{ right. intros C.
        apply sub_regular in C. destruct C as [? [? ?]].
        inversion H1;subst.
        pick_fresh X2. specialize_x_and_L X2 L.
        apply n. apply WF_replacing_var_lb with (X:=X2)... }
    destruct (wf_dec (open_tt B2 X1) u3).
    2:{ right. intros C.
        apply sub_regular in C. destruct C as [? [? ?]].
        inversion H2;subst.
        pick_fresh X2. specialize_x_and_L X2 L.
        apply n. apply WF_replacing_var_lb with (X:=X2)... }
    

    clear IHA1 IHA2 IHB1 IHB2. simpl in H.

    specialize (IHk (open_tt A2 X1) (open_tt B2 X1)
    (X1 ~ bind_sub_lb B1 ++ E)).

    rewrite bindings_fvar_spec_lb in IHk...

    (* rewrite <- bindings_fvar_spec with (X:=X1)in H... *)
    2:{ apply type_open_tt_WFC with (X:=X1)... apply WF_type in w0... }
    2:{ get_well_form... }
    2:{ get_well_form... get_type... }
    rewrite Btop in *.
    
    rewrite bindings_fvar_spec_lb in IHk...
    2:{ apply type_open_tt_WFC with (X:=X1)... apply WF_type in w1... }
    2:{ get_well_form... }
    2:{ get_well_form... apply WF_type in H5... }
    rewrite Btop in *. 

    assert (Eq: bindings_rec (mk_benv E) empty_menv 0 A1 = bindings_rec (mk_benv E) empty_menv 0 B1).
    { apply equiv_measure...
      { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
      { apply type_to_rec. apply WF_type with (E:=E). get_well_form... }
    }
    rewrite Eq in *.

    destruct IHk.
    { simpl in H. simpl. lia. }
    { left.
      apply sa_all_lb with (L:={{X1}} \u fv_tt A1 \u fv_tt A2 \u fv_tt B1 \u fv_tt B2 \u dom E);intros...
      (* { apply Reflexivity... } { apply Reflexivity... } *)
      apply sub_replacing_var_lb with (X:=X1)...
      get_well_form...
    }
    { right. intros. intros C.
      inversion C;inv_rt. subst. pick_fresh X2.
      specialize_x_and_L X2 L.
      apply n. apply sub_replacing_var_lb with (X:=X2)...
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
    { apply le_S_n in H. eapply le_trans;[|apply H]. simpl.
      apply plus_le_compat.
      replace ((bindings_rec (mk_benv E) ((1, mval 1) :: empty_menv) 1 A - 0)) with
      ((bindings_rec (mk_benv E) ((1, mval 1) :: empty_menv) 1 A )) by lia. lia.
      replace ((bindings_rec (mk_benv E) ((1, mval 1) :: empty_menv) 1 B - 0)) with
      ((bindings_rec (mk_benv E) ((1, mval 1) :: empty_menv) 1 B )) by lia. lia.
      (* pose proof bindings_rec_ge_1 (mk_benv E)  ((1, mval 1) :: empty_menv) 1 A. lia.
      { apply sub_menv_sem. constructor...
        simpl. lia. }
      { apply le_S. apply sub_menv_sem.
        constructor... simpl. lia. } *)
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

(* +
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
    } *)
Qed.


Lemma decidability : forall A B E,
{sub E A B} + {~ sub E A B}.
Proof with auto.
  intros.
  apply subtyping_dec with (k:=bindings_rec (mk_benv E) nil 0 A + 
                               bindings_rec (mk_benv E) nil 0 B )...
Qed.
