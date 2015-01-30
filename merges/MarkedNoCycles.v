Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Inductive MarkedGraph : list Set -> list Set -> list Set -> Type :=
 | empty : MarkedGraph [] [] []
 | inp   : forall i d o x,
           MarkedGraph i d o ->
           MarkedGraph (x :: i) (x :: d) o
 | out   : forall i d o x,
           MarkedGraph i d o ->
           Index d x         ->
           MarkedGraph i d (x :: o)
 | trans : forall i d o a (b : Set),
           MarkedGraph i d o ->
           Index d a         ->
           Transition a b    ->
           MarkedGraph i (b :: d) o
 | join2 : forall i d o (a b : Set),
           MarkedGraph i d o ->
           Index d a         ->
           Index d b         ->
           MarkedGraph i ((a*b)%type :: d) o
 .

Definition plus_left : MarkedGraph [nat] [option nat; nat; nat] [option nat].
 apply out.
 eapply trans.
 eapply trans.
 apply inp.
 apply empty.
 apply here.
 unfold Transition. apply (plus 1).
 apply here.
 unfold Transition. apply Some.
 apply here.
Defined.
Print plus_left. 

 

Inductive Values : list Set -> Type :=
 | v_nil : Values []
 | v_cons (x : Set) xs : list x -> Values xs -> Values (x :: xs).


Fixpoint inputs_to_places i d o
   (m : MarkedGraph i d o)
   (v : Values i) :
   Values d.
 induction m;
 eauto;
  inversion v; subst; eauto;
  try apply IHm in X0;
  try apply IHm in v;
  try solve [constructor; eauto].
  (* trans case. introduces new variables so set them to nil *)
  constructor. apply []. eauto.
  constructor. apply []. eauto.
Defined.


Eval compute in (inputs_to_places plus_left (v_cons [1;2;3] v_nil)).

Fixpoint find_output vs x
   (v : Values vs)
   (i : Index vs x)
      : list x.
 induction i;
 inversion v; eauto.
Defined.

Fixpoint outputs_of_places i d o
   (m : MarkedGraph i d o)
   (v : Values d) :
   Values o.
 induction m; inversion v; subst; eauto.
 inversion i0.
 constructor.
 eapply find_output; eauto.
 eauto.
Defined.

Eval compute in (outputs_of_places plus_left (v_cons [Some 1] (v_cons [] (v_cons [] v_nil)))).


Definition onfirst
  (x y : Set)    (d : list Set)
  (f   : list x -> list y) (v : Values (x::d))
       : Values (y::d).
 inversion v; subst; constructor; eauto.
Defined.

Fixpoint step i d o
   (m : MarkedGraph i d o)
   (v : Values d)
      : Values d.
 induction m.
  * (* empty *) eauto.
  * (* inp   *) inversion v; subst.
                constructor. assumption.
                apply IHm. assumption.
  * (* out   *) apply IHm. assumption.


 :=
 match m with
 | empty
   => v
 | inp i d o x m'
   => onfirst id v
 end.
