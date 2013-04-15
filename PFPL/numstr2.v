Require Import Omega.
Require Import List.
Import ListNotations.

Require Import Coq.Arith.Bool_nat.

Inductive Ty :=
	t_num | t_str.

Definition Var := nat.
Definition Num := nat.
Definition String := unit.

Inductive Exp :=
	| var : Var -> Exp
	| num : Num -> Exp
	| str : String -> Exp
	| plus : Exp -> Exp -> Exp
	| times : Exp -> Exp -> Exp
	| cat : Exp -> Exp -> Exp
	| len : Exp -> Exp
	| lett : Exp -> Exp -> Exp.

Definition Env := list Ty.

Definition getEnv (env : Env) n := nth_error env n.
Definition InEnv v t env := getEnv env v = Some t.

Hint Unfold Env.
Hint Unfold getEnv.
Hint Unfold InEnv.

Fixpoint insert (env : Env) v tv :=
 match env,v with
 | _, 0          => tv :: env
 | [],      S v' => tv :: env
 | (x::xs), S v' => x  :: insert xs v' tv
 end.

Lemma insert_0 env t :
      insert env 0 t = t :: env.
Proof.
 destruct env; auto.
Qed.

Inductive TyRules (env : Env) : Exp -> Ty -> Prop :=
	| ty_env (v : Var) (t : Ty): (InEnv v t env) -> TyRules env (var v) t
	| ty_str (s : String) : TyRules env (str s) t_str
	| ty_num (n : Num) : TyRules env (num n) t_num
	| ty_plus (e1 e2 : Exp) : TyRules env e1 t_num -> TyRules env e2 t_num
					-> TyRules env (plus e1 e2) t_num
	| ty_times (e1 e2 : Exp) : TyRules env e1 t_num -> TyRules env e2 t_num
					-> TyRules env (times e1 e2) t_num
	| ty_cat (e1 e2 : Exp) : TyRules env e1 t_str -> TyRules env e2 t_str
					-> TyRules env (cat e1 e2) t_str
	| ty_len (e : Exp) : TyRules env e t_str
					-> TyRules env (len e) t_num
	| ty_lett (def body : Exp) (tdef tbody : Ty) :
		TyRules env def tdef ->
		TyRules (cons tdef env) body tbody ->
		TyRules env (lett def body) tbody.

Lemma unicity_of_typing
	(env: Env) (e : Exp) (t1 t2 : Ty)
	(Ht1 : TyRules env e t1)
	(Ht2 : TyRules env e t2)
	: t1 = t2.
Proof.
  revert t2 Ht2.
  induction Ht1; intros; inversion Ht2; try congruence.
   subst.
    apply IHHt1_1 in H1.
    subst.
    apply IHHt1_2 in H3.
    assumption.
Qed.



Lemma inversion_of_typing__plus
	(env : Env) (e e1 e2 : Exp) (t t1 t2 : Ty) :
	TyRules env e t ->
	e = plus e1 e2 ->
	TyRules env e1 t1 ->
	TyRules env e2 t2 ->
	t = t_num /\
	t1 = t_num /\
	t2 = t_num.
Proof.
 intros Ht Heplus. subst.
 revert t1 t2.
 inversion Ht; intros.
  inversion H.
 subst.
 assert (t1 = t_num) by (apply (unicity_of_typing env e1); assumption).
 assert (t2 = t_num) by (apply (unicity_of_typing env e2); assumption).
 auto.
Qed.


Lemma InEnv_app_end
  (env env' : Env) (t : Ty) (v : Var) :
  InEnv v t env -> InEnv v t (env ++ env').
Proof.
 unfold InEnv, getEnv.
 revert env' v.
 induction env; intros.
  destruct v; simpl in H; inversion H.
 destruct v.
  auto.
 simpl in H.
 simpl.
 eapply IHenv in H.
 eassumption.
Qed.


Lemma InEnv_app_start
  (env env' : Env) (t : Ty) (v : Var) :
  InEnv v t env -> InEnv (length env' + v) t (env' ++ env).
Proof.
 unfold InEnv, getEnv.
 revert v.
 induction env'; intros.
  simpl. assumption.
 
 simpl.
 apply IHenv' in H.
 assumption.
Qed.

Lemma weakening_app_end
	(env env' : Env) (e : Exp) (te : Ty) : 
	TyRules env e te ->
	TyRules (env ++ env') e te.
 intros Hte.
 revert env'.
 induction Hte; intros; try solve [constructor; auto].
 apply ty_env; apply InEnv_app_end; assumption.
 apply ty_lett with (tdef := tdef).
 auto.
 apply IHHte2.
Qed.


Definition raise' (a b v : nat) :=
 if   ge_dec v b
 then a + v
 else v.

Fixpoint raise (e : Exp) (a b : nat) :=
 match e with
 | var v     => var (raise' a b v)
 | num n     => num n
 | str s     => str s
 | plus  p q => plus  (raise p a b) (raise q a b)
 | times p q => times (raise p a b) (raise q a b)
 | cat   p q => cat   (raise p a b) (raise q a b)
 | len p     => len   (raise p a b)
 | lett  d i => lett  (raise d a b) (raise i a (S b))
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

Lemma get_insert_lt (env : Env) i v ti tv :
      InEnv i ti env ->
      i < v ->
      InEnv i ti (insert env v tv).
Proof.
 intros Hget Hlt.
 revert v tv Hlt env Hget.
 induction i; intros; unfold InEnv, getEnv in *.
  destruct env. inversion Hget.
  simpl in Hget. destruct v. omega.  
 simpl. auto.
 
 destruct env. inversion Hget.
 simpl in Hget. destruct v. omega.
 simpl.
 apply IHi; try omega; auto.
Qed.

Lemma get_insert_ge (env : Env) i v ti tv :
      InEnv i ti env ->
      i >= v ->
      InEnv (S i) ti (insert env v tv).
Proof.
 intros Hget Hge.
 revert v tv env Hge Hget.
 unfold InEnv, getEnv.
 induction i; intros.

 destruct env. inversion Hget.
 simpl in Hget.
 destruct v. simpl. assumption.
 omega.
 destruct env. inversion Hget.
 destruct v. auto.
 apply IHi.
 omega.
 assumption.
Qed.

Lemma uninsert t1 e v t2:
      insert (t1::e) (S v) t2 =
      t1 :: (insert e v t2).
Proof.
 auto.
Qed.

Lemma weakening_insert
        (env : Env) (e : Exp) (te tvi : Ty) (vi : Var) :
        TyRules env e te ->
        TyRules (insert env vi tvi) (raise e 1 vi) te.
 intros Hte.
 revert vi tvi.
 induction Hte; intros; try solve [constructor; auto].
 apply ty_env.
 unfold raise', InEnv, getEnv in *.
 destruct (ge_dec v vi).
 apply get_insert_ge; assumption.
 apply get_insert_lt. assumption.
 omega.

 apply ty_lett with (tdef := tdef); fold raise.
 auto.
 rewrite <- uninsert.
 apply IHHte2.
Qed.


Lemma weakening_cons
	(env : Env) (e : Exp) (te : Ty) tv : 
	TyRules env e te ->
	TyRules (tv :: env) (raise e 1 0) te.
Proof.
 replace (tv :: env) with (insert env 0 tv).
 apply weakening_insert.
 destruct env; auto.
Qed.


Fixpoint subst (e e' : Exp) (v : Var) :=
 match e with
 | var v' => if   eq_nat_dec v v'
             then e'
             else if lt_dec v v'
             then var (v' - 1)
             else var v'
 | num n     => num n
 | str s     => str s
 | plus  p q => plus  (subst p e' v) (subst q e' v)
 | times p q => times (subst p e' v) (subst q e' v)
 | cat   p q => cat   (subst p e' v) (subst q e' v)
 | len p     => len   (subst p e' v)
 | lett  d i => lett  (subst d e' v) (subst i (raise e' 1 0) (S v))
 end.

Lemma InEnv_insert env v t t':
      InEnv v t' (insert env v t) ->
      t = t'.
Proof.
 unfold InEnv, getEnv.
 intros HIE. revert t t' env HIE.
 induction v; intros.
 destruct env; simpl in *; unfold value in *; congruence.
 
 destruct env. simpl in *. destruct v; inversion HIE.
 simpl in HIE.
 apply IHv in HIE. assumption.
Qed.



Lemma insert_minus1 (env : Env) i v ti tv :
      InEnv (S i) ti (insert env v tv) ->
      S i > v ->
      InEnv i ti env.
Proof.
 intros Hin Hge.
 revert env v ti tv Hin Hge.
 unfold InEnv, getEnv.
 induction i; intros.
 destruct v; destruct env; auto.
 omega.

 destruct env; destruct v; auto.
 simpl.
 eapply IHi.
 simpl in Hin.
 eassumption.
 omega.
Qed.


Lemma insert_pre (env : Env) i v ti tv :
      InEnv i ti (insert env v tv) ->
      v <= length env ->
      i < v ->
      InEnv i ti env.
Proof.
 intros Hin Hlen Hge.
 revert env v ti tv Hin Hge Hlen.
 unfold InEnv, getEnv.
 induction i; intros.
 destruct v; destruct env; auto.
 omega. omega. simpl in Hlen. omega.
  

 destruct env; destruct v; auto.
 omega. simpl in Hlen. omega. omega.
 simpl. 
 eapply IHi.
 simpl in Hin.
 eassumption.
 omega.
 simpl in Hlen.
 omega.
Qed.


Lemma substitution_ix env x t t' e e':
      TyRules (insert env x t) e'             t' ->
      TyRules env              e              t  ->
      x <= length env                             ->
      TyRules env              (subst e' e x) t'.
Proof.
 intros Ht' Ht Hlen.
 remember (insert env x t) as ENV.
 revert env x t e HeqENV Ht Hlen.
 induction Ht'; intros; try solve [constructor; auto].
   simpl.
   destruct (eq_nat_dec x v).
  subst. 
  apply InEnv_insert in H.
   subst; auto.
   destruct (lt_dec x v).
   subst.
   apply ty_env.
  destruct v. omega.
  simpl. rewrite <- minus_n_O.
  eapply insert_minus1.
  eassumption. omega.
  
  apply ty_env.
  subst.
  eapply insert_pre.
  eassumption. assumption. omega.

  simpl; subst; constructor.
  eapply IHHt'1; auto.
  eapply IHHt'2; auto.

  simpl; subst; constructor.
  eapply IHHt'1; auto.
  eapply IHHt'2; auto.

  simpl; subst; constructor.
  eapply IHHt'1; auto.
  eapply IHHt'2; auto.

  simpl; subst; constructor.
  eapply IHHt'; auto.


  subst.
  simpl.
  eapply ty_lett.
  eapply IHHt'1; auto.

  eapply IHHt'2.
  simpl. auto.
  apply weakening_cons. auto.
  simpl. omega.
Qed.



Lemma substitution env t t' e e':
      TyRules (t :: env)       e'             t' ->
      TyRules env              e              t  ->
      TyRules env              (subst e' e 0) t'.
Proof.
 intros.
 eapply substitution_ix.
 rewrite insert_0. eassumption.
 eassumption.
 omega.
Qed.



Lemma InEnv_insert_n env v t:
      v <= length env ->
      InEnv v t (insert env v t).
Proof.
 unfold InEnv, getEnv.
 revert v t.
 induction env; intros.
 destruct v; auto. simpl in H. omega.
 
 destruct v; auto.
 simpl in *.
 apply IHenv. omega.
Qed.

Lemma decomposition env x t t' e e':
      TyRules env              (subst e' e x) t' ->
      TyRules env              e              t  ->
      x <= length env                            ->
      TyRules (insert env x t) e'             t'.
Proof.
 intros Hsub Ht Hlen.
 revert env x t t' e Hsub Ht Hlen.
 induction e'; intros.
 simpl in Hsub.
  apply ty_env.
  destruct (eq_nat_dec x v).
    assert (t = t'). eapply unicity_of_typing; eassumption.
  subst. apply InEnv_insert_n. assumption.
   destruct (lt_dec x v).
   inversion Hsub.
   assert (v = S v0) as HvSv0. destruct v. omega. subst. simpl. rewrite <- minus_n_O. reflexivity.
   rewrite HvSv0.
   apply get_insert_ge. rewrite H. assumption.
   omega.
  apply get_insert_lt. inversion Hsub. assumption. omega.

 inversion Hsub. constructor.
 inversion Hsub. constructor.

 inversion Hsub. constructor.
 eapply IHe'1; eassumption.
 eapply IHe'2; eassumption.

 inversion Hsub. constructor.
 eapply IHe'1; eassumption.
 eapply IHe'2; eassumption.

 inversion Hsub. constructor.
 eapply IHe'1; eassumption.
 eapply IHe'2; eassumption.

 inversion Hsub. constructor.
 eapply IHe'; eassumption.

 inversion Hsub.
 eapply ty_lett.
 eapply IHe'1; eassumption.
 rewrite <- uninsert.
 eapply IHe'2.
 eassumption.
 subst. apply weakening_cons. assumption.
 simpl. omega.
Qed.

