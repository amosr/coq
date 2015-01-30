Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Base.
Import ListNotations.
Set Implicit Arguments.




(* Kahn *)
Inductive Graph : list Set -> list Set -> list Set -> Type :=
 | Empty  : Graph [] [] []
 | Inp    : forall a i n o,
            Graph i n o
         -> Graph (a::i) (a::n) o
 | Out    : forall a i n o,
            Index n a
         -> Graph i n o
         -> Graph i n (a::o)
 | Trans2 : forall a b c i n o,
            Index n a
         -> Index n b
         -> Graph i n o
         -> Graph i (c::n) o.

Inductive Propi (t : Type) : Prop :=
 Prop_c : t -> Propi t.

Inductive Typi (p : Prop) : Type :=
 Type_c : p -> Typi p.

Print Propi.
Print Typi.

Fixpoint nils (i : list Set) : Values i :=
 match i with
 | [] => v_nil
 | (_::i') => v_cons [] (nils i')
 end.

Inductive Trace : forall i n o, Graph i n o -> Values i -> Type :=
 | TDone : forall i n o (g : Graph i n o), Trace g (nils i).



