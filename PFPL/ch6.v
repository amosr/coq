Require Import Env.
Require Import TransitiveClosure.

Inductive Ty :=
        | t_num   : Ty
        | t_arrow : Ty -> Ty -> Ty.

Definition Num := nat.

Inductive Exp :=
        | var    : Var -> Exp
        | num    : Num -> Exp
        | lambda : Ty  -> Exp -> Exp
        | app    : Exp -> Exp -> Exp.
(* does lambda need Ty? *)

Definition TEnv := Env Ty.

Inductive TYPE (env : TEnv) : Exp -> Ty -> Prop :=
	| ty_env (v : Var) (t : Ty): (InEnv v t env) -> TYPE env (var v) t
	| ty_num (n : Num) : TYPE env (num n) t_num
	| ty_lambda (body : Exp) (ty tbody : Ty) :
		TYPE (ty :: env) body tbody ->
		TYPE env (lambda ty body) (t_arrow ty tbody)
	| ty_app (f x : Exp) (t1 t2 : Ty) :
		TYPE env f (t_arrow t1 t2) ->
		TYPE env x t1 ->
		TYPE env (app f x) t2.


Lemma unicity
	(env: TEnv) (e : Exp) (t1 t2 : Ty)
	(Ht1 : TYPE env e t1)
	(Ht2 : TYPE env e t2)
	: t1 = t2.
Proof.
  revert t2 Ht2.
  induction Ht1; intros; inversion Ht2; subst; try congruence.
  f_equal. apply IHHt1. assumption.
  
  apply IHHt1_1 in H1.
  apply IHHt1_2 in H3.
  congruence.
Qed.

Fixpoint raise (e : Exp) (a b : nat) :=
 match e with
 | var v      => var (raise' a b v)
 | num n      => num n
 | lambda t x => lambda t (raise x a (S b))
 | app f x    => app (raise f a b) (raise x a b)
 end.

Lemma raise_0_id (e : Exp) (n : nat) :
	raise e 0 n = e.
Proof.
 revert n.
 induction e; intros; simpl; try (rewrite IHe1, IHe2); try reflexivity.
 unfold raise, raise'.
 destruct (ge_dec v n); auto.
 rewrite IHe. reflexivity.
Qed. 

Lemma weakening_insert
        (env : TEnv) (e : Exp) (te tvi : Ty) (vi : Var) :
        TYPE env e te ->
        TYPE (insert env vi tvi) (raise e 1 vi) te.
 intros Hte.
 revert vi tvi.
 induction Hte; intros; try solve [constructor; auto].
 apply ty_env.
 unfold raise', InEnv, getEnv in *.
 destruct (ge_dec v vi).
 apply get_insert_ge; assumption.
 apply get_insert_lt. assumption.
 omega.

 apply ty_lambda; fold raise.
 rewrite <- uninsert; auto.
 eapply ty_app; fold raise; auto.
Qed.

Lemma weakening_cons
	(env : TEnv) (e : Exp) (te : Ty) tv : 
	TYPE env e te ->
	TYPE (tv :: env) (raise e 1 0) te.
Proof.
 rewrite <- insert_0.
 apply weakening_insert.
Qed.



Fixpoint subst (e e' : Exp) (v : Var) :=
 match e with
 | var v'     => subst' v v' var e'
 | num n      => num n
 | lambda t x => lambda t (subst x (raise e' 1 0) (S v))
 | app    f x => app (subst f e' v) (subst x e' v)
 end.

Lemma minus_n_1 v:
      S v - 1 = v.
 simpl. rewrite minus_n_O. reflexivity.
Qed.

Lemma substitution_ix env x t t' e e':
      TYPE (insert env x t) e'             t' ->
      TYPE env              e              t  ->
      x <= length env                         ->
      TYPE env              (subst e' e x) t'.
Proof.
 intros Ht' Ht Hlen.
 remember (insert env x t) as ENV.
 revert env x t e HeqENV Ht Hlen.
 induction Ht'; intros; try solve [constructor; auto].
   unfold subst, subst'.
   destruct (eq_nat_dec x v); subst.
    apply InEnv_insert in H. subst. assumption.
   destruct (lt_dec x v); subst.
    apply ty_env.
    destruct v. omega.
     rewrite minus_n_1.
     eapply insert_minus1; eassumption.
   apply ty_env. eapply insert_pre; try eassumption; try omega.

 simpl; subst; apply ty_lambda.
 eapply IHHt'. reflexivity.
 apply weakening_cons; assumption.
 simpl. omega.
 
 simpl; subst; eapply ty_app.
 eapply IHHt'1. reflexivity. assumption. assumption.
 eapply IHHt'2. reflexivity. assumption. assumption.
Qed.


Lemma substitution env t t' e e':
      TYPE (t :: env)       e'             t' ->
      TYPE env              e              t  ->
      TYPE env              (subst e' e 0) t'.
Proof.
 intros.
 eapply substitution_ix; try rewrite insert_0; try eassumption; try omega.
Qed.

Lemma decomposition env x t t' e e':
      TYPE env              (subst e' e x) t' ->
      TYPE env              e              t  ->
      x <= length env                         ->
      TYPE (insert env x t) e'             t'.
Proof.
 intros Hsub Ht Hlen.
 revert env x t t' e Hsub Ht Hlen.
 induction e'; intros.
 simpl in Hsub; unfold subst' in Hsub.
  apply ty_env.
  destruct (eq_nat_dec x v).
    replace t with t' by (eapply unicity; eassumption).
    replace v with x  by assumption.
    apply InEnv_insert_n. assumption.
   destruct (lt_dec x v).
   inversion Hsub.
   assert (v = S v0) as HvSv0. destruct v. omega. subst. simpl. rewrite <- minus_n_O. reflexivity.
   rewrite HvSv0.
   apply get_insert_ge. rewrite H. assumption.
   omega.
  apply get_insert_lt. inversion Hsub. assumption. omega.

 inversion Hsub. constructor.
 inversion Hsub. constructor.
 rewrite <- uninsert.
 eapply IHe'.
 eassumption.
 apply weakening_cons.
 assumption.
 simpl; omega.

 inversion Hsub; subst; eapply ty_app.
 eapply IHe'1; eassumption.
 eapply IHe'2; eassumption.
Qed.


Inductive val : Exp -> Prop :=
  | v_num n : val (num n)
  | v_lambda t b : val (lambda t b).

Inductive e_step : Exp -> Exp -> Prop :=
  | e_app1 e1 e1' e2 : e_step e1 e1' -> e_step (app e1 e2) (app e1' e2)
  | e_app2 e1 e2 e2' : val e1 -> e_step e2 e2' -> e_step (app e1 e2) (app e1 e2')
  | e_lam  t b x     : val x -> e_step (app (lambda t b) x) (subst b x 0).


Lemma preservation e e' t:
      TYPE [] e t ->
      e_step e e' ->
      TYPE [] e' t.
Proof.
 intros Ht He.
 revert t Ht.
 induction He; intros; inversion Ht; subst;
 try econstructor; try apply IHHe; try eassumption.
 inversion H2;
 eapply substitution;
 eassumption.
Qed.


Lemma progress e t:
      TYPE [] e t ->
      val e \/ (exists e', e_step e e').
Proof.
 intros Ht.
 remember [] as ENV.
 induction Ht; try solve [left; constructor].
 subst. apply not_InEnv_nil in H. destruct H.
 right.
  destruct IHHt1. assumption.
  destruct IHHt2. assumption.
  inversion H; subst; inversion Ht1; subst.
  eexists. eapply e_lam. assumption.

  destruct H0.
  eexists. eapply e_app2; eassumption.

  destruct H.
  eexists. eapply e_app1; eassumption.
Qed.


Inductive bigstep: Exp -> Exp -> Prop :=
  | b_num n    : bigstep (num n) (num n)
  | b_lam t b  : bigstep (lambda t b) (lambda t b)
  | b_app f t b x x' v :
        bigstep f (lambda t b)   ->
        bigstep x x'             ->
        bigstep (subst b x' 0) v ->
        bigstep (app f x) v.

Definition tc := transitive_closure Exp e_step.

Lemma bigstep__val e v:
      bigstep e v -> val v.
Proof.
 intros. induction H; try constructor; try assumption.
Qed.

Lemma e_step_noval e e':
      e_step e e' ->
      ~ val e.
Proof.
 intros H Hv.
 induction Hv;
 inversion H.
Qed.

Lemma e_step_deterministic e e' e'':
      e_step e e'  ->
      e_step e e'' ->
      e' = e''.
 intros He1 He2.
 revert e'' He2.
 induction He1; intros.
 inversion He2; subst.

 replace e1' with e1'0 in *.
  reflexivity. symmetry. apply IHHe1. assumption.
 eapply e_step_noval in H1. destruct H1.
 eassumption.

 inversion He1.

 inversion He2; subst.
 eapply e_step_noval in H. destruct H. eassumption.
 apply IHHe1 in H4. rewrite H4. reflexivity.

 eapply e_step_noval in H3. destruct H3. eassumption.

 inversion He2; subst.
 inversion H3.
 eapply e_step_noval in H. destruct H. eassumption.
 reflexivity.
Qed.

 


Lemma tc_app t b s s' v:
      tc (app (lambda t b) s) v ->
      tc s s' ->
      val v   ->
      tc (app (lambda t b) s') v.
Proof.
 intros Ha Hs Hv.
 revert t b v Ha Hv.
 induction Hs; intros; subst.
 assumption.
 apply IHHs.
 inversion Ha; subst.
 inversion Hv.
 inversion H0; subst.
 inversion H5.
 replace e2' with s' in *.
 eassumption.
 eapply e_step_deterministic; eassumption.

 eapply e_step_noval in H6. destruct H6. eassumption.
 assumption.
Qed.
  


Lemma tc_app2 t b s s' v:
      tc (app (lambda t b) s') v ->
      tc s s' ->
      val v   ->
      tc (app (lambda t b) s) v.
Proof.
 intros Ha Hs Hv.
 revert t b v Ha Hv.
 induction Hs; intros; subst.
 assumption.
 eapply tc_step. apply e_app2. constructor. eassumption.
 apply IHHs; assumption.
Qed.


Lemma tc_app1 e1 e1' e2 v:
      tc (app e1' e2) v ->
      tc e1 e1' ->
      tc (app e1 e2) v.
Proof.
 intros Ha Hs.
 revert e2 v Ha.
 induction Hs; intros; subst.
 assumption.
 eapply tc_step. apply e_app1. eassumption.
 apply IHHs; assumption.
Qed.

(* H0 : bigstep x x'
H1 : bigstep (subst b x' 0) v
IHbigstep2 : tc x x'
IHbigstep3 : tc (subst b x' 0) v
H : bigstep (lambda t b) (lambda t b)
IHbigstep1 : tc (lambda t b) (lambda t b)
s' : Exp
H2 : e_step x s'
H3 : transitive_closure Exp e_step s' x'
______________________________________(1/3)
transitive_closure Exp e_step (app (lambda t b) s') v
*)

Lemma bigstep__e_step e v:
      bigstep e v ->
      tc e v.
Proof.
 intros. induction H; try constructor.
 eapply tc_concat.
  inversion IHbigstep1; subst.
   inversion IHbigstep2; subst.
   eapply tc_step. eapply e_lam. eapply bigstep__val; eassumption.
  eassumption.
   eapply tc_step. eapply e_app2; try constructor; eassumption.

   inversion H3; subst.
    eapply tc_step. eapply e_lam. eapply bigstep__val. eassumption.
    assumption.

   

   eapply tc_app2 with (s' := x').
    eapply tc_step. eapply e_lam.
    eapply bigstep__val. eassumption.
    assumption. assumption.
    eapply bigstep__val; eassumption.


   eapply tc_app1 with (e1' := lambda t b).
    eapply tc_app2 with (s' := x').
     eapply tc_step. eapply e_lam. eapply bigstep__val; eassumption.
     assumption.
     assumption.
    eapply bigstep__val; eassumption.
    eassumption.

 apply tc_refl.
Qed.

Lemma val__bigstep v:
      val v ->
      bigstep v v.
Proof.
 intros Hv.
 destruct Hv; constructor.
Qed.

Lemma e_step__bigstep e e' v:
      e_step e e'  ->
      bigstep e' v ->
      bigstep e  v.
Proof.
 intros He Hbs.
 revert v Hbs.
 induction He; intros.
 inversion Hbs; subst.
 eapply b_app.
 apply IHHe; eassumption.
 eassumption.
 assumption.

 inversion Hbs; subst.
 eapply b_app; try eassumption.
 eapply IHHe; eassumption.

 apply val__bigstep in H.
 eapply b_app; try constructor; try eassumption.
Qed.

