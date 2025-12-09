Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import ListLib.Core.
Require Import ListLib.Positional.

Import ListNotations.

Theorem prefix_ind_iff_positional {A: Type}: forall (l1 l2: list A),
  prefix_ind l1 l2 <-> prefix_pos l1 l2.
Proof.
  intros.
  split; intros.
  - destruct H as [l3 ?]; exists (length l1); subst.
    rewrite firstn_app.
    rewrite Nat.sub_diag; simpl.
    rewrite firstn_all.
    rewrite app_nil_r.
    reflexivity.
  - destruct H as [hi ?].
    exists (skipn hi l2); subst.
    rewrite firstn_skipn.
    reflexivity. 
Qed. 

Theorem suffix_ind_iff_positional {A: Type}: forall (l1 l2: list A),
  suffix_ind l1 l2 <-> suffix_pos l1 l2.
Proof.
  intros.
  split; intros.
  - destruct H as [l3 ?]; exists (length l3); subst.
    rewrite skipn_app.
    rewrite Nat.sub_diag; simpl.
    rewrite skipn_all.
    reflexivity.
  - destruct H as [lo ?].
    exists (firstn lo l2); subst.
    rewrite firstn_skipn.
    reflexivity.
Qed.

Theorem sublist_ind_iff_positional {A: Type}: forall (l1 l2: list A),
  sublist_ind l1 l2 <-> sublist_pos l1 l2.
Proof.
  intros.
  split; intros.
  - destruct H as [p [q]]. 
    exists (length p), (length p + length l1); subst. 
    rewrite! firstn_app.
    replace (length p + length l1 - length p) with (length l1) by lia.
    rewrite Nat.sub_diag; simpl. 
    rewrite app_nil_r. 
    rewrite firstn_all. 
    rewrite firstn_all2 by lia.
    rewrite skipn_app. 
    rewrite Nat.sub_diag; simpl. 
    rewrite skipn_all. 
    reflexivity. 
  - destruct H as [lo [hi Heq]].
    exists (firstn lo (firstn hi l2)), (skipn hi l2); subst.
    rewrite app_assoc.
    rewrite! firstn_skipn.
    reflexivity.
Qed.


Definition prefix {A: Type} := @prefix_ind A .
Definition suffix {A: Type} := @suffix_ind A .
Definition sublist {A: Type} := @sublist_ind A .

Notation "l1 'is_a_prefix_of' l2" := (prefix l1 l2) (at level 10, no associativity).
Notation "l1 'is_a_suffix_of' l2" := (suffix l1 l2) (at level 10, no associativity).
Notation "l1 'is_a_sublist_of' l2" := (sublist l1 l2) (at level 10, no associativity).

Lemma Forall2_nth_iff : forall (A B : Type)
  (P : A -> B -> Prop) xs ys dx dy,
  Forall2 P xs ys <->
  (length xs = length ys /\
   forall n, n < length xs ->
     P (nth n xs dx) (nth n ys dy)).
Proof.
  intros. split; intros.
  - split. apply (@Forall2_length _ _ _ _ _ H).
    intros.
    assert (n < length ys).
    { rewrite <- (@Forall2_length _ _ _ _ _ H); auto. }
    rewrite (firstn_skipSn dx _ _ H0) in H. 
    rewrite (firstn_skipSn dy _ _ H1) in H.
    apply (Forall2_split _ n) in H.
    destruct H as [_ ?].
    rewrite ! skipn_app in H.
    assert (n = length (firstn n xs)).
    { rewrite length_firstn. rewrite min_l; auto. lia. }
    assert (skipn n (firstn n xs) = nil).
    { transitivity (skipn (length (firstn n xs)) (firstn n xs)).
      - congruence.
      - apply skipn_all. }
    assert (n = length (firstn n ys)).
    { rewrite length_firstn. rewrite min_l; auto. lia. }
    assert (skipn n (firstn n ys) = nil).
    { transitivity (skipn (length (firstn n ys)) (firstn n ys)).
      - congruence.
      - apply skipn_all. }
    rewrite H3 in H. rewrite H5 in H. simpl in H.
    replace (n - length (firstn n xs)) with O in H by lia.
    replace (n - length (firstn n ys)) with O in H by lia.
    simpl in H. inversion H. auto.
  - destruct H. generalize dependent ys.
    induction xs; intros; destruct ys; simpl in *; try lia.
    + constructor.
    + constructor.
      * specialize (H0 O). apply H0. lia.
      * apply IHxs; auto.
        intros. apply (H0 (S n)). lia.
Qed.