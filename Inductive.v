Require Import Coq.Lists.List.
Require Import ListLib.Core.

Import ListNotations.

Lemma snoc_destruct: forall {A: Type} (l: list A),
  l = nil \/
  exists a l', l = l' ++ [a].
Proof.
  intros.
  revert l; apply rev_ind.
  + left; reflexivity.
  + intros.
    right.
    eauto.
Qed.

Lemma app_cons{A: Type}: forall (a: A) (l1 l2: list A), 
  l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  intros.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma Forall2_congr : forall (A B : Type) (p p' : A -> B -> Prop) xs ys,
  (forall x y, In x xs -> In y ys -> p x y -> p' x y) ->
  Forall2 p xs ys ->
  Forall2 p' xs ys.
Proof.
  intros. induction H0.
  - constructor.
  - constructor.
    + apply H; auto.
      * left. auto.
      * left. auto.
    + apply IHForall2. intros.
      apply H; auto.
      * right. auto.
      * right. auto.
Qed.
(* Forall2_impl *)

Lemma Forall2_map1 {A B C : Type} : 
forall (P : C -> B -> Prop) xs ys (f : A -> C),
  Forall2 (fun x y => P (f x) y) xs ys <->
  Forall2 P (map f xs) ys.
Proof.
  induction xs; intros; destruct ys; simpl; split; intros.
  - constructor.
  - constructor.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
Qed.

Lemma Forall2_map2 {A B C : Type} : 
forall (P : A -> C -> Prop) xs ys (f : B -> C),
  Forall2 (fun x y => P x (f y)) xs ys <->
  Forall2 P xs (map f ys).
Proof.
  induction xs; intros; destruct ys; simpl; split; intros.
  - constructor.
  - constructor.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
  - inversion H. subst. constructor; auto.
    apply IHxs. auto.
Qed.
