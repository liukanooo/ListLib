Require Import Coq.Lists.List.

Import ListNotations.

Definition prefix_ind {A: Type} (l1 l2: list A): Prop := exists l, l2 = l1 ++ l.

Definition suffix_ind {A: Type} (l1 l2: list A): Prop := exists l, l2 = l ++ l1. 

Definition sublist_ind {A: Type} (l1 l2: list A): Prop := exists l3 l4, l2 = l3 ++ l1 ++ l4. 

Definition sublist_pos {A: Type} (l1 l2: list A): Prop := exists lo hi, l1 = skipn lo (firstn hi l2).

Definition sublist'_pos {A: Type} (l1 l2: list A): Prop := exists lo hi, l1 = firstn lo (skipn hi l2).

Definition prefix_pos {A: Type} (l1 l2: list A): Prop := exists hi, l1 = firstn hi l2. 

Definition suffix_pos {A: Type} (l1 l2: list A): Prop := exists lo, l1 = skipn lo l2. 

(* app reverse cons nil inductive.v

(Z)lenght nth replace positional.v

app <-> nth equivalence.v

Forall In NoDup map prefix suffix sublist     *)