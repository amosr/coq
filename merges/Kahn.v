Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Base.
Require Import Merges.
Import ListNotations.
Set Implicit Arguments.




(* Kahn *)
Inductive Graph : list Type -> list Type -> list Type -> Type :=
 | Empty  : Graph [] [] []
 | Inp    : forall a i n o,
            Graph i n o
         -> Graph (a::i) (a::n) o
 | Out    : forall a i n o,
            Index n a
         -> Graph i n o
         -> Graph i n (a::o)
 | Trans1 : forall a b i n o,
            Index n a
         -> Stream1 a b
         -> Graph i n o
         -> Graph i (b::n) o
 | Trans2 : forall a b c i n o,
            Index n a
         -> Index n b
         -> Stream2 a b c
         -> Graph i n o
         -> Graph i (c::n) o.
Definition in_out (A : Type) : Graph [A] [A] [A] := Out (here _ _) (Inp _ Empty).

Inductive BuffEmpty := BuffEmptyC : BuffEmpty.
Inductive BuffInp A := BuffInpC  : list A -> BuffInp A.
Inductive BuffT1  B := BuffT1C   : nat -> list B -> BuffT1  B.
Inductive BuffT2  C := BuffT2C   : nat -> nat -> list C -> BuffT2 C.


Fixpoint BuffState (i n o : list Type) (g : Graph i n o) : Type :=
 match g with
 | Empty => BuffEmpty
 | Inp a i n o g => (BuffInp a * BuffState g)%type
 | Out a i n o ix g => BuffState g
 | Trans1 a b i n o ix s g => (BuffT1 b * BuffState g)%type
 | Trans2 a b c i n o ix1 ix2 s g => (BuffT2 c * BuffState g)%type
 end.

Definition inpOfValues i is (inp : Values (i::is)) : BuffInp i :=
 match inp with
 | v_cons _ _ x _ => BuffInpC x
 end.

Print inpOfValues.
Eval compute in (inpOfValues (v_cons [1;2] v_nil)).

(* ughrughrguhr *)
Definition buffsOfInps (i n o : list Type) (g : Graph i n o)
                     (is : Values i) : BuffState g.
 induction g;
  try apply pair; fold BuffState;
  try apply IHg; eauto;
  try solve
            [  eapply inpOfValues; eauto 
            |  eapply BuffEmptyC
            |  apply BuffT1C;  try apply 0; try apply []
            |  apply BuffT2C;  try apply 0; try apply []
            ].
 inversion is; eauto.
Defined.
Eval compute in buffsOfInps (in_out _) (v_cons [1;2;3] v_nil).

Print buffsOfInps.


Definition zinpOfValues i is (inp : Values (i::is)) : BuffInp i.
 inversion inp. constructor. eauto.
Defined.
Print zinpOfValues.
Eval compute in (inpOfValues (v_cons [1;2] v_nil)).



Definition indexBuffState n' (i n o : list Type) (g : Graph i n o)
                      (bs : BuffState g)
                      (ix : Index n n')
                  : list n'.
 induction g;
  try destruct bs; try destruct b; try destruct b0;
  try inversion ix; subst;
  try assumption;
  try apply IHg;
  try assumption.
Defined.

Definition outOfBuffState (i n o : list Type) (g : Graph i n o)
                      (bs : BuffState g) : Values o.
 induction g;
  try solve [apply v_nil];
  try solve [inversion bs; apply IHg; eauto].
 apply v_cons.
 eapply indexBuffState; eauto.
 apply IHg. eauto.
Defined.

Theorem in_out_id A (vs : list A):
        outOfBuffState (in_out A) (buffsOfInps (in_out A) (v_cons vs v_nil)) = (v_cons vs v_nil).
Proof.
 compute. eauto.
Qed.




Definition PortId := (nat * nat)%type.

Inductive Status :=
 | Running : list PortId -> Status
 | Finished : Status
 | NotStarted : Status.


Inductive Trace : forall i n o, Graph i n o -> Values i -> Type :=
 | TDone : forall i n o (g : Graph i n o), Trace g (nils i).



