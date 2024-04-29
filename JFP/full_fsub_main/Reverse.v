Set Implicit Arguments.
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Antisymmetry.


Ltac inv_rt :=
  try solve [
    repeat match goal with
    | [ H : rt_type ?T |- _ ] => inversion H;clear H
    end
      ].


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


Lemma subst_tt_collect3': forall T i X A,
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
