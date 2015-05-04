Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Base.
Import ListNotations.
Set Implicit Arguments.



Inductive Move : Type :=
 | Forward
 | Stay.

Definition Stream1 (a b : Type)
 := option a -> (Move * option b) + unit.

Definition Map (A B : Type) (f : A -> B) : Stream1 A B
 := fun a =>
    match a with
    | Some a => inl (Forward, Some (f a))
    | None   => inr tt
    end.

Definition Filter (A : Type) (f : A -> bool) : Stream1 A A
 := fun a =>
    match a with
    | Some a => inl (Forward, if f a then Some a else None)
    | None   => inr tt
    end.

(* Let's only handle stateless merges for now *)
Definition Stream2 (a b c : Type)
 := option a -> option b -> (Move * Move * option c) + unit.


Definition Zip (A B : Type) : Stream2 A B (A*B)
 := fun a b =>
    match (a,b) with
    | (Some a, Some b) => inl (Forward, Forward, Some (a,b))
    | _                => inr tt
    end.


Search ({?a <= ?b} + {?a > ?b}).

(* Just a merge, really *)
Definition MergeJoin (A : Type) : Stream2 (nat*A) (nat*A) (nat*A)
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
