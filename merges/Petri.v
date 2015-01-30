(* Proper petri nets *)
Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Require Import Base.

Section Petri.
 (* Places - buffers *)
 Variable P : Set.
 (* Transitions - functions *)
 Variable T : Set.


 (* Places are buffers, so we need to figure out what type they store *)
 Variable Pt : P -> Set.

 (* Transitions can have multiple inputs *)
 Variable Ti : T -> list (P * nat).
 (* and, why not - multiple outputs *)
 Variable To : T -> list (P * nat).

 (* The standard way to define edges is a little different,
    but the correspondence hould be obvious:
   (* Arcs - or "flows" *)
   Definition F : Set := (P*T + T*P)%type.
   (* Does a given arc exist? If so, what is its weight *)
   (* The weight is the number of tokens passed along at any time *)
   Variable Fs : F -> option nat.
 *)


 (* Each transition's function type is based on its input and output
    places, so we to convert the list of places and naturals to
    some nested tuple structure.
    A (+) transition would be have
     Ti = [nat, 1; nat, 1]
     To = [nat, 1]
    and so its type would be
     ((nat,unit),(nat,unit),unit) -> ((nat,unit),unit)
    which is isomorphic to
     nat -> nat -> nat
 *)
 Fixpoint valuePn (p : P) (n : nat) : Set :=
  match n with
  | 0    => unit
  | S n' => (Pt p * valuePn p n')%type
  end.

 Fixpoint values (ps : list (P * nat)) : Set :=
  match ps with
  | []
    => unit
  | ((p,n)::ps')
    => (valuePn p n * values ps')%type
  end.

 (* Each transition has a function of its type *)
 Variable Tf : forall t : T, values (Ti t) -> values (To t).


 (* A marking assigns each place to its buffer of values *)
 Definition Marking := forall p : P, list (Pt p).

 




