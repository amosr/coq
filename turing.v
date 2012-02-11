Module Turing.

Require Import List.
Require Import EqNat.


Inductive Direction :=
	Left | Right.

(* A single step in each evaluation of a machine. *)
Inductive Step (State : Set) :=
	| StepDo : nat -> State -> Direction -> Step State
	| StepHalt : Step State.

(* a total mapping from State*Symbol to a Step. *)
Definition Stepper (State : Set) :=
	State -> nat -> Step State.


(* Our infinitely long tape, and its read head.
There are symbols to the left and symbols to the right.
It also has a default symbol that the whole thing is initialised to. *)
Inductive Tape : Set :=
	TTape : nat -> list nat -> list nat -> Tape.

(* Get the value at the tapehead *)
Definition get (t : Tape) :=
	match t with
	| TTape default nil _ => default
	| TTape _ (x::_) _ => x
	end.

(* Replace value at tapehead, producing new tape *)
Definition write (t : Tape) (s : nat) :=
	match t with
	| TTape d nil rs => TTape d (s::nil) rs
	| TTape d (_::ls) rs => TTape d (s::ls) rs
	end.

(* Move tapehead to left *)
Definition move_left (t : Tape) :=
	match t with
	| TTape default nil rs => TTape default nil (default :: rs)
	| TTape default (l::ls) rs => TTape default ls (l::rs)
	end.

Definition move_right (t : Tape) :=
	match t with
	| TTape default ls nil => TTape default (default :: ls) nil
	| TTape default ls (r::rs) => TTape default (r::ls) rs
	end.

Definition move (t : Tape) (d : Direction) :=
	match d with
	| Left => move_left t
	| Right => move_right t
	end.

Definition empty (default : nat) :=
	TTape default nil nil.

(* What do we know about our infinite tape? *)

(* How do we say that two tapes are equivalent?
Chop any defaults off the ends and then compare? *)

Definition chopList (d : nat) (l : list nat) :=
	let fix go l' :=
		match l' with
		| nil => nil
		| x::xs =>
			match beq_nat x d with
			| true => go xs
			| false => x::xs
			end
		end
	in rev (go (rev l)).

Definition chop (t : Tape) :=
	match t with
	| TTape d ls rs => TTape d (chopList d ls) (chopList d rs)
	end.

Definition equiv (l r : Tape) :=
	chop l = chop r.

Notation "l ~= r" := (equiv l r) (at level 70).

Theorem chopList_one (d : nat) :
	chopList d (d::nil) = nil.
Proof.
  intros. unfold chopList. simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

(* left.right = id *)
Theorem tape_lr_id (t : Tape) :
	move_left (move_right t) ~= t.
Proof.
  intros. unfold equiv.
  destruct t; destruct l0; simpl.
    rewrite chopList_one. reflexivity.
    reflexivity.
Qed.

Theorem tape_rl_id (t : Tape) :
	move_right (move_left t) ~= t.
Proof.
  intros. unfold equiv.
  destruct t; destruct l; simpl.
    rewrite chopList_one. reflexivity.
    reflexivity.
Qed.

(* write.write = write *)
Theorem tape_ww (t : Tape) (s1 s2 : nat) :
	write (write t s2) s1 ~= write t s1.
Proof.
  intros. unfold equiv.
  destruct t; destruct l; auto.
Qed.

(* The whole thing, with current state, tape and a stepper function *)
Inductive Machine (State : Set) : Set :=
	MMachine : State
			-> Tape
			-> Stepper State
			-> Machine State.

Definition step {State : Set}
	(m : Machine State) :=
	match m with
	| MMachine state tape stepper =>
		match stepper state (get tape) with
		| StepDo sy st' dir  =>
			Some (MMachine _ st' (move (write tape sy) dir) stepper)
		| StepHalt => None
		end
	end.


(* fill *)
Module Fill.
  Inductive FState := FLeft | FRight.
  
  Definition stepper : Stepper FState :=
    fun st => fun sym =>
      match st with
      | FLeft =>
        match sym with
        | 0 => StepDo _ 0 FRight Right
        | 1 => StepDo _ 1 FLeft Left
        | _ => StepHalt _
        end
      | FRight =>
        match sym with
        | 0 => StepDo _ 1 FLeft Left
        | 1 => StepDo _ 1 FRight Right
        | _ => StepHalt _
        end
      end.
  
  Definition machine := MMachine _ FRight (empty 0) stepper.

  Eval compute in step machine.
End Fill.
