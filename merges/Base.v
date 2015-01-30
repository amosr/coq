Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Definition Transition a b := a -> b.

Inductive Index : list Set -> Set -> Type :=
 | here  : forall x xs, Index (x :: xs) x
 | there : forall x xs y, Index     xs  x -> Index (y :: xs) x.


Inductive Values : list Set -> Type :=
 | v_nil : Values []
 | v_cons (x : Set) xs : list x -> Values xs -> Values (x :: xs).


Inductive Indices (xs : list Set) : Type :=
 | i_nil : Indices xs
 | i_cons (x : Set) : Index xs x -> Indices xs -> Indices xs.
