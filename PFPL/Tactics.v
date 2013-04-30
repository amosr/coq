(* Some helper tactics *)
(* Mostly playing around *)


Tactic Notation "induct_invert" ident(X) ident(Y) :=
 induction X; intros; inversion Y; subst.

Ltac eqall :=
 repeat (match goal with 
 | [ H : ?f ?p = ?g ?q |- _ ]
     => injection H; intros; subst; clear H
 end).

Ltac appall :=
 repeat
 (match goal with
  | [ F : forall a, ?x a -> ?p a
    , X : ?x ?t
    |- _ ]
    => eapply F in X
  | [ F : ?x -> ?p
    , X : ?x
    |- _ ]
    => eapply F in X
 end).

Ltac appallf :=
 repeat
 (match goal with
  | [ F : forall a, ?x a -> ?p a
    |- ?p ?a ]
    => eapply F
  | [ F : ?x -> ?p
    |- ?p ]
    => eapply F
 end).

Ltac screw :=
 repeat
 (match goal with
  | [ F : ?x = ?y
    |- _ ]
    => rewrite F in *
  | [ F : forall a, ?x = ?y
    |- _ ]
    => rewrite F in *
  | [ F : forall a b, ?x = ?y
    |- _ ]
    => rewrite F in *
  | [ F : forall a b c, ?x = ?y
    |- _ ]
    => rewrite F in *
  end).

Ltac screwback :=
 repeat
 (match goal with
  | [ F : ?x = ?y
    |- _ ]
    => rewrite <- F in *
  | [ F : forall a, ?x = ?y
    |- _ ]
    => rewrite <- F in *
  | [ F : forall a b, ?x = ?y
    |- _ ]
    => rewrite <- F in *
  | [ F : forall a b c, ?x = ?y
    |- _ ]
    => rewrite <- F in *
  end).



Ltac refl_ap :=
 repeat (match goal with
  [ H : ?x = ?x -> ?y |- _ ]
  => let X := fresh H in
     assert (x = x) as X by reflexivity;
     apply H in X;
     clear H
  end).

Ltac smash :=
 repeat (match goal with
 | [ H : _ \/ _ |- _ ]
   => destruct H
 | [ H : exists _, _ |- _ ]
   => destruct H

 | [ H : False |- _ ]
   => destruct H
 end).

Ltac invertlike f :=
 match goal with
 | [ H : f |- _ ]
   => inversion H; subst
 | [ H : f ?a |- _ ]
   => inversion H; subst
 | [ H : f ?a ?b |- _ ]
   => inversion H; subst
 | [ H : f ?a ?b ?c |- _ ]
   => inversion H; subst
 end.
