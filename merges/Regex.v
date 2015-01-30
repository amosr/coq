Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.
Set Implicit Arguments.


Inductive Regex (n : Set) :=
 | Elem  : n -> Regex n
 | Empty :      Regex n
 | Seq   :      Regex n -> Regex n -> Regex n
 | Alt   :      Regex n -> Regex n -> Regex n
 | Star  :      Regex n -> Regex n
 .

Inductive Match (n : Set) : Regex n -> list n -> Prop :=
 | MElem  : forall e:n, Match (Elem e)  [e]
 | MEmpty :             Match (Empty _) []

 | MSeq   : forall r1 r2 l1 l2,
            Match r1 l1
         -> Match r2 l2
         -> Match (Seq r1 r2) (l1 ++ l2)

 | MAlt_L : forall r1 r2 l,
            Match r1 l
         -> Match (Alt r1 r2) l
 | MAlt_R : forall r1 r2 l,
            Match r2 l
         -> Match (Alt r1 r2) l

 | MStar_0: forall r,
            Match (Star r) []
 | MStar_1: forall r l l',
            Match r l
         -> Match (Star r) l'
         -> Match (Star r) (l ++ l')
 .

Definition RegexEq (n : Set) (r1 r2 : Regex n) :=
  forall l, Match r1 l -> Match r2 l
   /\       Match r2 l -> Match r1 l.

(* I promise! *)
Axiom RegexEq_dec : forall (n : Set) (r1 r2 : Regex n), RegexEq r1 r2 \/ ~ RegexEq r1 r2.


Check filter.

Fixpoint filterRx (A : Set) (f : A -> bool) (rx : Regex A) :=
 match rx with
 | Empty => Empty _
 | Elem n => if f n then Elem n else Empty _
 | Seq p q => Seq (filterRx f p) (filterRx f q)
 | Alt p q => Alt (filterRx f p) (filterRx f q)
 | Star p  => Star (filterRx f p)
 end.

Theorem filter_app_dist (A : Set) (f : A -> bool) (a b : list A) :
   filter f (a ++ b) = filter f a ++ filter f b.
Proof.
 induction a; simpl;
   try destruct (f a);
   try rewrite IHa;
   eauto.
Qed.

Theorem filter_same (A : Set) (f : A -> bool) (rx : Regex A) (w : list A) :
 Match rx w -> Match (filterRx f rx) (filter f w).
Proof.
 intros.
 induction H; eauto; simpl;
  try rewrite filter_app_dist;
  try (destruct (f e));
  try solve [constructor; eauto];
  eauto.

 apply MAlt_R; eauto.
Qed.

