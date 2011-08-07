Require Import Coq.Lists.List.
Set Implicit Arguments.

Inductive Step A S :=
	| Done : Step A S
	| Skip : S -> Step A S
	| Yield: A -> S -> Step A S.

Inductive Stream A S : S -> Type :=
	| StreamC : forall (s:S),
		(S -> Step A S) -> Stream A s.

(* repeated application of step/next function.
   needs to be an inductive type instead of a fixpoint because
   the fixpoint wouldn't terminate given e.g. (fun s => Skip s) *)
Inductive StepEval A S (f : S -> Step A S): S -> Step A S -> Type :=
	| SE_Done: forall (s : S),
		f s = Done A S ->
		StepEval f s (Done A S)
        | SE_Skip: forall (s s': S) (st: Step A S),
		f s' = st ->
		f s = Skip A s' ->
		StepEval f s' st ->
		StepEval f s (Skip A s')
	| SE_Yield: forall (a : A) (s s' : S) (st: Step A S),
		f s' = st ->
		f s = Yield a s' ->
		StepEval f s' st -> StepEval f s (Yield a s').

Inductive StreamEval A S (f: S -> Step A S) (s: S): Stream A s -> Type :=
	| StreamE :
		StepEval f s (f s) ->
		StreamEval f (StreamC s f).

(* can convert a list to a stream very simply *)
Definition stream_next {A} (ls : list A) :=
  match ls with
  | nil   => Done A (list A)
  | x::xs => Yield x xs
  end.

Definition stream {A} (ls: list A) : Stream A ls :=
  StreamC ls stream_next.


(* harder if you want to know results *)
Definition streamE_next:
	forall {A : Type} (ls : list A),
	StepEval stream_next ls (stream_next ls).
  intros A ls.
  induction ls.
    constructor. reflexivity.
  apply SE_Yield with (st := stream_next ls).
    reflexivity.
    reflexivity.
    apply IHls.
Defined.

Definition streamE {A : Type} (ls : list A):
	StreamEval stream_next (stream ls) :=
  StreamE (streamE_next ls).


(* however, if you want to convert a stream to a list you need to have
   the steps already evaluated so you know it's finite *)
Fixpoint unstream_unfold {A S} (next : S -> Step A S) (s : S) (st : Step A S) (seval : StepEval next s st) :=
  match seval with
  | SE_Done h s' => nil
  | SE_Skip s s' st h1 h2 se' => unstream_unfold se'
  | SE_Yield a s s' st h1 h2 se' => a :: unstream_unfold se'
  end.

Definition unstream {A S : Type} {f : S -> Step A S}
	{s : S}
	{str : Stream A s}
	(strE: StreamEval f str)
	: list A :=
  match strE with
  | StreamE steps => unstream_unfold steps
  end.

(* converting a list to a stream and then back should be exactly the same *)
Theorem unstream_stream__id: forall A (ls: list A),
	unstream (streamE ls) = ls.
  intros A ls.
  simpl.
  induction ls.
    reflexivity.
    simpl. rewrite IHls. reflexivity.
Qed.

(* the actual rewrite rule in the paper is
	forall s. stream (unstream s) => s
   but because stream.unstream will eliminate skips, can't say "=".
   instead we'll say conversion to list is the same.
   paper seems to suggest just filtering skip to check equivalence.
   fine, but I already had 'unstream' defined.
*)

Definition StreamEquiv {A S1 S2 : Type}
	(f1   : S1 -> Step A S1)
	(s1   : S1)
	(str1 : Stream A s1)
	(strE1: StreamEval f1 str1)

	(f2   : S2 -> Step A S2)
	(s2   : S2)
	(str2 : Stream A s2)
	(strE2: StreamEval f2 str2)
	 := unstream strE1 = unstream strE2.

Theorem stream_unstream__id: forall {A S : Type}
	(f   : S -> Step A S)
	(s   : S)
	(str : Stream A s)
	(strE: StreamEval f str),
	StreamEquiv
		strE
		(streamE (unstream strE)).
  intros A S f s str strE.
  unfold StreamEquiv.
  rewrite unstream_stream__id.
  reflexivity.
Qed.


(* apply single function to each step *)
Definition map_next {A B S} (f: A -> B) (step: Step A S) : Step B S :=
  match step with
  | Done => Done B S
  | Skip s' => Skip B s'
  | Yield x s' => Yield (f x) s'
  end.

(* slightly easier to work with - updated next function *)
Definition map_f {A B S} (f: A -> B) (next : S -> Step A S) (s : S) : Step B S :=
  map_next f (next s).


(* map whole step evaluation - including its children *)
Definition map_step {A B S} (f : A -> B)
	(next: S -> Step A S)
	(s   : S)
	(step: Step A S)
	(se: StepEval next s step):

	(StepEval (map_f f next) s (map_next f step)).
  intros A B S f next s step se.
  unfold map_f.
  induction se.
  eapply SE_Done. rewrite e. reflexivity.
  eapply SE_Skip.
    reflexivity.
    rewrite e0. reflexivity.
    rewrite e. apply IHse.
  eapply SE_Yield.
    reflexivity.
    rewrite e0. reflexivity.
    rewrite e. apply IHse.
Defined.

(* map a whole evaluated stream *)
Definition map_s {A B S} (f : A -> B)
	(next: S -> Step A S)
	(s   : S)
	(str : Stream A s)
	(strE: StreamEval next str):

	(StreamEval (map_f f next) (StreamC s (map_f f next))) :=
  match strE with
  | StreamE step => StreamE (map_step f step)
  end.



Theorem map__map_s: forall {A B}
	(f : A -> B)
	(ls: list A),
	map f ls = unstream (map_s f (streamE ls)).
Proof.
  intros A B f ls.
  induction ls.
  reflexivity.
  simpl. rewrite IHls. reflexivity.
Qed.


(* should be trivial to prove that
   forall f g ls,
     map (f.g) ls =
     (map f . map g) ls =
     unstream . map_s f . map_s g . streamE =
     unstream . map_s f . streamE . unstream . map_s g . streamE =
   and so on... *)



