(* Non-deterministic, cycle-free petri nets.
   The functions are deterministic, but perhaps arbitrary:
   if a place is used by multiple transitions it
   will be consumed by the "first" active transition.

   This is rather different to the normal definition, but I suspect
   is able to express the same graphs as normal petri nets.
 *)

Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Require Import Base.


Inductive Petri : list Set -> list Set -> list Set -> Type :=
 | empty : MarkedGraph [] [] []
 (* An input place which would be initialised with some content *)
 | inp   : forall i d o x,
           MarkedGraph i d o ->
           MarkedGraph (x :: i) (x :: d) o
 (* A single-input transition that destructively consumes from a single place.
    Also creates output place. *)
 | trans : forall i d o a (b : Set),
           MarkedGraph i d o ->
           Index d a         ->
           Transition a b    ->
           MarkedGraph i (b :: d) o
 (* Destructive duplicate transition, that creates two new places *)
 | dup2  : forall i d o a,
           MarkedGraph i d o ->
           Index d a         ->
           MarkedGraph i (a :: a :: d) o
 (* Transition that joins two input places together *)
 | join2 : forall i d o (a b : Set),
           MarkedGraph i d o ->
           Index d a         ->
           Index d b         ->
           MarkedGraph i ((a*b)%type :: d) o
 .


