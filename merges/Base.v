Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Import ListNotations.
Set Implicit Arguments.

Definition Transition a b := a -> b.

Inductive Index : list Type -> Type -> Type :=
 | here  : forall x xs, Index (x :: xs) x
 | there : forall x xs y, Index     xs  x -> Index (y :: xs) x.


Inductive HList : list Type -> Type :=
 | h_nil : HList []
 | h_cons (x : Type) xs : x -> HList xs -> HList (x :: xs).

(* Definition Values (xs : list Type) := HList (map (fun (x : Type) => list x) xs). *)

Inductive Values : list Type -> Type :=
 | v_nil : Values []
 | v_cons (x : Type) xs : list x -> Values xs -> Values (x :: xs).



Theorem value_sole_exists A (vs : Values [A])
    : exists (v : list A), vs = @v_cons A _ v v_nil.
Proof.
 dependent destruction vs.
 dependent destruction vs.
 eauto.
Qed.


Fixpoint nils (i : list Type) : Values i :=
 match i with
 | [] => v_nil
 | (_::i') => v_cons [] (nils i')
 end.


Definition Indices (xs ys : list Type)
 := HList (map (Index xs) ys).
