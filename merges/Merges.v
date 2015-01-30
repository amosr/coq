Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Base.
Import ListNotations.
Set Implicit Arguments.



Inductive Move : Type :=
 | Forward
 | Stay.

(* Let's only handle stateless merges for now *)
Definition Merge (a b c : Set)
 := option a -> option b -> (Move * Move * option c) + unit.


Definition Zip (A B : Set) : Merge A B (A*B)
 := fun a b =>
    match (a,b) with
    | (Some a, Some b) => inl (Forward, Forward, Some (a,b))
    | _                => inr tt
    end.


Search ({?a <= ?b} + {?a > ?b}).

(* Just a merge, really *)
Definition SegmentedAppend (A : Set) : Merge (nat*A) (nat*A) (nat*A)
 := fun a b =>
    match (a,b) with
    | (Some (ia,a), Some (ib, b))
    => if   le_dec ia ib
       then inl (Forward, Stay, Some (ia, a))
       else inl (Stay, Forward, Some (ib, b))
    | (Some a, None)
    => inl (Forward, Stay, Some a)
    | (None, Some b)
    => inl (Stay, Forward, Some b)
    | (None, None)
    => inr tt
    end.
