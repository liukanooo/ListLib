Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Psatz.
Require Import ListLib.Core.

Import ListNotations.


Definition to_sublist_pos {A: Type} (lo hi: nat) (l: list A): list A := skipn lo (firstn hi l).

Lemma length_nonnil {A: Type}: forall (l: list A),
  l <> [] -> length l > 0.
Proof. 
  intros.
  destruct l.
  - congruence.
  - simpl; lia.
Qed.

Lemma sublist_nil {A: Type}:
  forall (l : list A) a b,
    b <= a -> to_sublist_pos a b l = [].
Proof.
  intros. unfold to_sublist_pos.
  apply skipn_all2.
  rewrite length_firstn; lia.
Qed.

Lemma nth_firstn: forall {A} (l: list A) n m d,
  (n < m)%nat ->
  nth n (firstn m l) d = nth n l d.
Proof.
  intros.
  rewrite nth_firstn. 
  destruct (n <? m) eqn:E; auto.
  rewrite Nat.ltb_ge in E; lia.
Qed.

Lemma length_sublist {A: Type}:
  forall (lo hi: nat) (l: list A),
    lo <= hi /\ hi <= length l ->
    length (to_sublist_pos lo hi l) = hi-lo.
Proof.
  intros.
  unfold to_sublist_pos.
  rewrite length_skipn.
  rewrite firstn_length_le by lia.
  reflexivity.
Qed.

Lemma length_sublist' {A: Type}:
  forall (i j: nat) (l: list A),
    length (to_sublist_pos i j l) = 
    (min j (length l) - i).
Proof.
  intros.
  unfold to_sublist_pos.
  rewrite length_skipn.
  rewrite length_firstn.
  reflexivity.
Qed.

Lemma nth_sublist {A: Type} (d: A):
  forall (lo i hi: nat) (l: list A),
  i < hi-lo ->
  nth i (to_sublist_pos lo hi l) d = nth (i+lo) l d.
Proof.
  intros.
  unfold to_sublist_pos.
  rewrite nth_skipn.
  rewrite nth_firstn by lia.
  f_equal.
  lia.
Qed.

Lemma firstn_skipSn {A: Type} (d: A): forall (n : nat) (l : list A),
  n < length l ->
  l = firstn n l ++ nth n l d :: skipn (S n) l.
Proof.
  induction n; intros.
  - destruct l; simpl in *; try lia. auto.
  - destruct l; simpl in *; try lia.
    f_equal. assert (n < length l) by lia.
    apply IHn. auto.
Qed.

Lemma sublist_single {A: Type} (d: A): forall (n : nat) (l : list A),
  n < length l -> to_sublist_pos n (n + 1) l = [nth n l d].
Proof.
  intros.
  rewrite (firstn_skipSn d _ _ H) at 1; try lia.
  unfold to_sublist_pos.
  rewrite firstn_app.
  assert (length (firstn n l) = n) by (rewrite length_firstn; lia).
  rewrite firstn_all2; try lia. 
  replace ((n + 1) - length (firstn (n) l))%nat with 1%nat by lia.
  rewrite skipn_app.
  replace (n - length (firstn (n) l))%nat with 0%nat by lia.
  rewrite skipn_all2; try lia.
  simpl. reflexivity.
Qed.

Lemma sublist_one_ele {A: Type} (d: A): 
  forall i (text: list A) (ch: A),
    0 <= i < length text ->
    ch = nth i text d -> 
    to_sublist_pos 0 i text ++ [ch] = to_sublist_pos 0 (i + 1) text.
Proof.
  intros. 
  eapply nth_ext.
  + rewrite length_app.
    rewrite ! length_sublist by lia.
    simpl; lia.
  + intros.
    destruct (le_gt_dec i n).
    - rewrite app_nth2 by (rewrite length_sublist by lia; lia).
      rewrite length_app, length_sublist in H1 by lia.
      simpl in H1.
      rewrite !nth_sublist by lia.
      rewrite length_sublist by lia.
      replace (n - (i - 0)) with 0 by lia.
      simpl.
      subst ch.
      f_equal; lia.
    - rewrite app_nth1 by (rewrite length_sublist by lia; lia).
      rewrite !nth_sublist by lia.
      reflexivity.
Qed.

Lemma sublist_one_ele' {A: Type} (d: A):
  forall i (text: list A),
    0 <= i < length text ->
    to_sublist_pos 0 (i + 1) text = to_sublist_pos 0 i text ++ [nth i text d].
Proof.
  intros. 
  erewrite sublist_one_ele; eauto.
Qed.

Lemma sublist_single' {A: Type} (d: A):
  forall (n : nat) (l : list A),
    0 < n <= length l ->
    to_sublist_pos (n - 1) n l = [nth (n - 1) l d].
Proof.
  intros.
  remember (n-1) as t.
  assert (n = t + 1) by lia.
  rewrite H0.
  apply sublist_single; lia.
Qed.

Lemma sublist_self {A: Type}:
  forall (l1: list A) x,
    x = length l1 ->
    to_sublist_pos 0 x l1 = l1.
Proof.
  intros. unfold to_sublist_pos; subst.
  rewrite skipn_O.
  apply firstn_all.
Qed.

Lemma sublist_split_app_l {A: Type}: forall (lo hi: nat) (l1 l2 : list A),
  lo <= hi -> hi <= length l1 -> to_sublist_pos lo hi (l1 ++ l2) = to_sublist_pos lo hi l1.
Proof.
  intros.
  unfold to_sublist_pos.
  rewrite firstn_app.
  simpl. 
  replace (hi - length l1)%nat with O by lia.
  rewrite app_nil_r. auto. 
Qed.

Lemma sublist_split_app_r {A: Type}:
  forall lo hi len (l1 l2: list A),
    length l1 = len ->
    len <= lo <= hi ->
    to_sublist_pos lo hi (l1 ++ l2) = to_sublist_pos (lo - len) (hi - len) l2.
Proof.
  intros.
  unfold to_sublist_pos.
  repeat rewrite skipn_firstn_comm.
  rewrite skipn_app.
  pose proof (length_skipn lo l1).
  replace (length l1 - lo) with O in H1 by lia.
  rewrite length_zero_iff_nil in H1; rewrite H1.
  simpl.
  replace (hi - len - (lo - len)) with (hi - lo) by lia.
  replace (lo - length l1) with (lo - len) by lia.
  auto.
Qed.

Lemma sublist_split {A: Type}: 
  forall (lo hi mid: nat) (l : list A),
    0 <= lo <= mid -> 
    mid <= hi <= length l ->
    to_sublist_pos lo hi l = 
    to_sublist_pos lo mid l ++ to_sublist_pos mid hi l.
Proof.
  intros.
  rewrite <- (firstn_skipn hi l).
  remember (firstn hi l) as l1.
  remember (skipn hi l) as l2.
  assert (length l1 = hi).
  {
    rewrite Heql1.
    rewrite length_firstn.
    lia.
  }
  assert (length l = length l1 + length l2)%nat.
  {
    rewrite Heql1, Heql2.
    rewrite length_firstn, length_skipn.
    lia.
  }
  rewrite H2 in H0.
  clear Heql1 Heql2 H2 l.
  do 3 (rewrite sublist_split_app_l ; try lia).
  unfold to_sublist_pos.
  replace hi%nat with (length l1) by lia.
  assert (mid <= length l1) by lia.
  clear H0 H1 l2 hi.
  rewrite firstn_all2 ; try lia.
  rename l1 into l. 
  rewrite <- (firstn_skipn ( lo) l).
  remember (firstn ( lo) l) as l1.
  remember (skipn ( lo) l) as l2.
  assert (length l1 = lo).
  {
    rewrite Heql1.
    rewrite length_firstn.
    lia.
  }
  rewrite firstn_app.
  do 3 rewrite skipn_app.
  rewrite firstn_all2 ; try lia.
  replace ( lo - length l1)%nat with O by lia.
  simpl.
  do 2 (rewrite skipn_all2 ; try lia).
  rewrite! app_nil_l.
  rewrite firstn_skipn.
  reflexivity.
Qed.

Lemma combine_skipn : forall (A B : Type) (l : list A) (l' : list B) n,
  skipn n (combine l l') = combine (skipn n l) (skipn n l').
Proof.
  intros *. revert l l'. induction n; intros; simpl.
  - auto.
  - destruct l; destruct l'; simpl in *; auto.
    rewrite combine_nil. auto.
Qed.

Lemma Forall2_split {A B : Type}: 
  forall (P : A -> B -> Prop) (n : nat) (xs: list A) (ys: list B),
  Forall2 P xs ys ->
  Forall2 P (firstn n xs) (firstn n ys) /\
  Forall2 P (skipn n xs) (skipn n ys).
Proof.
  induction n; intros; simpl.
  - split.
    + constructor.
    + auto.
  - destruct xs; destruct ys; simpl in *; inversion H.
    + split; constructor.
    + destruct (IHn _ _ H5). split.
      * constructor; auto.
      * auto.
Qed.
