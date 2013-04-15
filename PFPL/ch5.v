
Require Import Omega.
Require Import List.
Import ListNotations.

Require Import Coq.Arith.Bool_nat.


Inductive transitive_closure (S : Type) (step : S -> S -> Type) : S -> S -> Prop :=
  | tc_refl (s : S) : transitive_closure S step s s
  | tc_step (s s' s'' : S) :
            step s s' ->
            transitive_closure S step s' s'' ->
            transitive_closure S step s  s''.

Inductive n_steps (St : Type) (step : St -> St -> Type) : nat -> St -> St -> Prop :=
  | n_s_0   (s : St) : n_steps St step 0 s s
  | n_s_S   (s s' s'' : St) (n : nat) :
            step s s' ->
            n_steps St step n s' s'' ->
            n_steps St step (S n) s  s''.


Theorem tc__n_steps St step s s' :
        transitive_closure St step s s' <->
        exists k, n_steps St step k s s'.
Proof.
 split; intros.
  induction H.
   exists 0; constructor.
   destruct IHtransitive_closure.
   exists (S x). eapply n_s_S; eassumption.
  destruct H.
  induction H.
   constructor.
   econstructor; eassumption.
Qed.


Require Import numstr2.

Inductive val : Exp -> Prop :=
  | v_num (n : Num) : val (num n)
  | v_str (s : String) : val (str s).

(* CHEATING but I don't care *)
Definition f_cat (s1 s2 : String) : String := tt.
Definition f_len (s : String) : Num := 0.

Inductive e_step : Exp -> Exp -> Prop :=
  | e_plus   (n1 n2 : nat) : e_step (plus (num n1) (num n2)) (num (n1+n2))
  | e_plus1  (e e' e2 : Exp) :
             e_step e e' ->
             e_step (plus e e2) (plus e' e2)
  | e_plus2  (e1 e e' : Exp) :
             val e1 ->
             e_step e e' ->
             e_step (plus e1 e) (plus e1 e')

  | e_times  (n1 n2 : nat) : e_step (times (num n1) (num n2)) (num (n1*n2))
  | e_times1 (e e' e2 : Exp) :
             e_step e e' ->
             e_step (times e e2) (times e' e2)
  | e_times2 (e1 e e' : Exp) :
             val e1 ->
             e_step e e' ->
             e_step (times e1 e) (times e1 e')

  | e_cat    (n1 n2 : String) : e_step (cat (str n1) (str n2)) (str (f_cat n1 n2))
  | e_cat1   (e e' e2 : Exp) :
             e_step e e' ->
             e_step (cat e e2) (cat e' e2)
  | e_cat2   (e1 e e' : Exp) :
             val e1 ->
             e_step e e' ->
             e_step (cat e1 e) (cat e1 e')


  | e_len    (n1 : String) : e_step (len (str n1)) (num (f_len n1))
  | e_len1   (e e' : Exp) :
             e_step e e' ->
             e_step (len e) (len e')

  | e_let1   (e e' eB : Exp) :
             e_step e e' ->
             e_step (lett e eB) (lett e' eB)
  | e_letSub (eD eB : Exp) :
             val eD ->
             e_step (lett eD eB) (subst eB eD 0)
.



Lemma finality_a e :
      val e ->
      not (exists e', e_step e e').
Proof.
 unfold not.
 intros.
 induction H; destruct H0; inversion H.
Qed.

Lemma finality_b e e' :
      e_step e e' ->
      not (val e).
Proof.
 unfold not.
 intros.
 induction H; inversion H0.
Qed.


Lemma determinacy e e' e'':
      e_step e e'  ->
      e_step e e'' ->
      e' = e''.
Proof.
 intros He1 He2.
 revert e'' He2.
 induction He1; intros; inversion He2; subst; auto.

 inversion H2. inversion H3.

 inversion He1.
 apply IHHe1 in H2. rewrite H2. reflexivity.
 apply finality_a in H1.
 unfold not in H1.
 assert (exists e', e_step e e') by (eexists; eassumption).
 apply H1 in H. destruct H.

 inversion He1.

 apply finality_a in H.
 unfold not in H.
 assert (exists e', e_step e1 e') by (eexists; eassumption).
 apply H in H0. destruct H0.
 
 apply IHHe1 in H4. subst. reflexivity.

 inversion H2. inversion H3.
 inversion He1.

 apply IHHe1 in H2. subst. reflexivity.
 apply finality_b in He1. apply He1 in H1. destruct H1.
 inversion He1.
 apply finality_b in H3. apply H3 in H. destruct H.
 
 apply IHHe1 in H4. subst. reflexivity.

 inversion H2. inversion H3. inversion He1.
 apply IHHe1 in H2. subst. reflexivity.

 inversion H1; subst; inversion He1.

 inversion He1.
 inversion H; subst; inversion H3.
 apply IHHe1 in H4. subst. reflexivity.

 inversion H0.
 inversion He1.
 apply IHHe1 in H0. subst. reflexivity.

 apply IHHe1 in H2. subst. reflexivity.
 inversion H2; subst; inversion He1.
 inversion H; subst; inversion H3.
Qed.


Theorem preservation env e e' t:
        TyRules env e  t ->
        e_step e e'      ->
        TyRules env e' t.
Proof.
 intros Hty Hstep.
 revert t Hty.
 induction Hstep; intros; inversion Hty; try econstructor; try eapply IHHstep; try eassumption.

 eapply substitution; eassumption.
Qed.


Theorem progress e t:
        TyRules [] e t ->
        val e \/ (exists e', e_step e e').
Proof.
 intros Hty.
 remember [] as ENV_NIL.
 induction Hty; try (left; constructor); right; subst.

 destruct v; simpl in H; inversion H.
 assert (@nil Ty = @nil Ty) as HT1 by reflexivity; apply IHHty1 in HT1.
 assert (@nil Ty = @nil Ty) as HT2 by reflexivity; apply IHHty2 in HT2.

 destruct HT1; destruct HT2.
 inversion H; inversion H0; subst; inversion Hty1; inversion Hty2.
 exists (num (n + n0)). constructor.

 destruct H0.
 exists (plus e1 x); constructor; auto.

 destruct H.
 exists (plus x e2); constructor; auto.

 destruct H.
 exists (plus x e2); constructor; auto.

 (* times, cat, len - boring *)

 assert (@nil Ty = @nil Ty) as HT1 by reflexivity; apply IHHty1 in HT1.
 assert (@nil Ty = @nil Ty) as HT2 by reflexivity; apply IHHty2 in HT2.

 destruct HT1; destruct HT2.
 inversion H; inversion H0; subst; inversion Hty1; inversion Hty2.
 eexists. constructor.

 destruct H0.
 exists (times e1 x); constructor; auto.

 destruct H.
 exists (times x e2); constructor; auto.

 destruct H.
 exists (times x e2); constructor; auto.


 assert (@nil Ty = @nil Ty) as HT1 by reflexivity; apply IHHty1 in HT1.
 assert (@nil Ty = @nil Ty) as HT2 by reflexivity; apply IHHty2 in HT2.

 destruct HT1; destruct HT2.
 inversion H; inversion H0; subst; inversion Hty1; inversion Hty2.
 eexists. constructor.

 destruct H0.
 exists (cat e1 x); constructor; auto.

 destruct H.
 exists (cat x e2); constructor; auto.

 destruct H.
 exists (cat x e2); constructor; auto.


 assert (@nil Ty = @nil Ty) as HT by reflexivity; apply IHHty in HT.

 destruct HT.
 inversion H; inversion H0; subst; inversion Hty.
 eexists. constructor.

 destruct H.
 exists (len x); constructor; auto.


 assert (@nil Ty = @nil Ty) as HT1 by reflexivity; apply IHHty1 in HT1.
 destruct HT1.
 eexists. eapply e_letSub. assumption.

 destruct H. eexists. apply e_let1. eassumption.
Qed.
  



Inductive bigstep : Exp -> Exp -> Prop :=
  | bs_num n : bigstep (num n) (num n)
  | bs_str n : bigstep (str n) (str n)
  | bs_plus e1 e2 n1 n2 :
            bigstep e1 (num n1) ->
            bigstep e2 (num n2) ->
            bigstep (plus e1 e2) (num (n1 + n2))
  | bs_times e1 e2 n1 n2 :
            bigstep e1 (num n1) ->
            bigstep e2 (num n2) ->
            bigstep (times e1 e2) (num (n1 * n2))
  | bs_cat e1 e2 n1 n2 :
            bigstep e1 (str n1) ->
            bigstep e2 (str n2) ->
            bigstep (cat e1 e2) (str (f_cat n1 n2))
  | bs_len e1 n1 :
            bigstep e1 (str n1) ->
            bigstep (len e1) (num (f_len n1))
  | bs_let e1 e2 v1 v2 :
            bigstep e1 v1 ->
            bigstep (subst e2 e1 0) v2 ->
            bigstep (lett e1 e2) v2.


Lemma bigstep_val e v:
      bigstep e v ->
      val v.
Proof.
 intros Hbs. induction Hbs; try constructor.
 assumption.
Qed.
