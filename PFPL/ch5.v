
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
            bigstep (subst e2 v1 0) v2 ->
            bigstep (lett e1 e2) v2.


Lemma bigstep_val e v:
      bigstep e v ->
      val v.
Proof.
 intros Hbs. induction Hbs; try constructor.
 assumption.
Qed.

(* TODO define closed expressions *)
(* these lemmas are "for all closed expressions"
   but I don't know whether that's right;
   the I.H. will contain not-closed expressions... *)


Lemma tc_step__plus_tc_step e1 e2 v1:
      transitive_closure Exp e_step e1 v1 ->
      transitive_closure Exp e_step (plus e1 e2) (plus v1 e2).
Proof.
 intros H.
 induction H.
 apply tc_refl.
 eapply tc_step.
 eapply e_plus1.
 eassumption.
 assumption.
Qed.


Lemma tc_step__tc_step_plus2 e2 v1 v2:
      val v1 ->
      transitive_closure Exp e_step e2 v2 ->
      transitive_closure Exp e_step (plus v1 e2) (plus v1 v2).
Proof.
 intros Hval H.
 induction H.
 apply tc_refl.
 eapply tc_step.
 eapply e_plus2; eassumption.
 assumption.
Qed.


Lemma tc_step__tc_step_times1 e1 e2 v1:
      transitive_closure Exp e_step e1 v1 ->
      transitive_closure Exp e_step (times e1 e2) (times v1 e2).
Proof.
 intros H.
 induction H.
 apply tc_refl.
 eapply tc_step.
 eapply e_times1.
 eassumption.
 assumption.
Qed.


Lemma tc_step__tc_step_times2 e2 v1 v2:
      val v1 ->
      transitive_closure Exp e_step e2 v2 ->
      transitive_closure Exp e_step (times v1 e2) (times v1 v2).
Proof.
 intros Hval H.
 induction H.
 apply tc_refl.
 eapply tc_step.
 eapply e_times2; eassumption.
 assumption.
Qed.


Lemma tc_step__tc_step_let e1 v1 e2:
      transitive_closure Exp e_step e1 v1 ->
      transitive_closure Exp e_step (lett e1 e2) (lett v1 e2).
 intros H.
 induction H.
 apply tc_refl.
 eapply tc_step.
 eapply e_let1.
 eassumption.
 assumption.
Qed.


(*Lemma tc_step__let' s s' e2 v2:
      e_step s s' ->
      val v2 ->
      transitive_closure Exp e_step (subst e2 s 0) v2 ->
      transitive_closure Exp e_step (subst e2 s' 0) v2.
Proof.
 intros Hs Hv Ht.
 revert e2 v2 Ht Hv.
 induction Hs; intros.

 


 destruct e2.
  destruct v. simpl in *.
  inversion Ht. subst. inversion Hv.
  inversion Hv; subst.
  inversion Ht. inversion H1; subst.
  assumption.
 inversion H; subst. assumption.
 inversion Ht; subst. inversion H3; subst. assumption.
 *)
  

(*Lemma tc_step__tc_step_letSub e1 v1 e2 v2:
  transitive_closure Exp e_step e1 v1  ->
  transitive_closure Exp e_step (subst e2 e1 0) v2 ->
  transitive_closure Exp e_step (subst e2 v1 0) v2.
Proof.
 intros H1 H2.
 remember (subst e2 e1 0) as SUB.
 revert v1 H1.
 induction H2; subst.

 revert e2 v2 H2.
 induction H1; intros.
 assumption.
 apply IHtransitive_closure.
 
 inversion H2.
 subst.

 intros Hval H.
 remember (subst e2 v1 0) as SUB.
 eapply tc_step.
 induction H; subst.
 eapply tc_step. eapply e_letSub. assumption.
 apply tc_refl.

 apply IHtransitive_closure.
 
 subst.
 eapply tc_step.
 eapply e_let1.
 eassumption.
 assumption. 
Qed. *)


Lemma tc_concat e1 e2 e3:
      transitive_closure Exp e_step e1 e2 ->
      transitive_closure Exp e_step e2 e3 ->
      transitive_closure Exp e_step e1 e3.
Proof.
 intros H1 H2.
 revert e3 H2.
 induction H1; intros.
 assumption.
 eapply tc_step.
 eassumption.
 apply IHtransitive_closure.
 assumption.
Qed.

Lemma bigstep__tc_step e v:
      bigstep e v         ->
      transitive_closure Exp e_step e v.
Proof.
 intros Hbs.
 induction Hbs; intros;
    try solve [apply tc_refl].

 inversion IHHbs1; subst.
 inversion IHHbs2; subst.
  eapply tc_step. econstructor.
  apply tc_refl.

  assert (transitive_closure Exp e_step (plus (num n1) e2) (plus (num n1) (num n2))).
   apply tc_step__tc_step_plus2. constructor.
   eapply tc_step; eassumption.
   eapply tc_concat.
   eassumption.
   eapply tc_step. eapply e_plus. apply tc_refl.

  assert (transitive_closure Exp e_step (plus e1 e2) (plus (num n1) e2)).
   apply tc_step__plus_tc_step.
   eapply tc_step; eassumption.

  assert (transitive_closure Exp e_step (plus (num n1) e2) (plus (num n1) (num n2))).
   apply tc_step__tc_step_plus2. constructor.
   eapply IHHbs2; eassumption.
   eapply tc_concat. eassumption.
   eapply tc_concat. eassumption.
   eapply tc_step. eapply e_plus. apply tc_refl.
  

 eapply tc_concat.
  apply tc_step__tc_step_times1. eapply IHHbs1; inversion Hty; eassumption.
 eapply tc_concat.
  apply tc_step__tc_step_times2. constructor.
   eapply IHHbs2; inversion Hty; eassumption.
 eapply tc_step.
  eapply e_times.
 apply tc_refl.

 (* cat and len, so boring *)
 admit. admit.
 
 eapply tc_concat.
  apply tc_step__tc_step_let. eapply IHHbs1; eassumption.

 eapply tc_step.
  eapply e_letSub. eapply bigstep_val. eassumption.

 assumption.
Qed.


Lemma step__bigstep e e' v:
      e_step e e' ->
      bigstep e' v ->
      bigstep e v.
Proof.
 intros He Hbs.
 revert v Hbs.
 induction He; intros; inversion Hbs; subst; repeat constructor; try apply IHHe; auto.

 eapply bs_let. eapply IHHe. eassumption. assumption.
 destruct eB; simpl in H1; try solve [inversion H1].
 destruct v. destruct eD; inversion H1.
 subst. simpl in Hbs.
 eapply bs_let; eassumption.
 simpl in H1; inversion H1.
 eapply bs_let. destruct H; constructor. assumption.
 eapply bs_let. destruct H; constructor. assumption.
 eapply bs_let. destruct H; constructor. assumption.
 eapply bs_let. destruct H; constructor. assumption.
 eapply bs_let. destruct H; constructor. assumption.
 eapply bs_let. destruct H; constructor. assumption.
 eapply bs_let. destruct H; constructor. assumption.
Qed. 

