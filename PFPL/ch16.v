(* Recursive types *)

Require Import Env.
Require Import TransitiveClosure.

Inductive Ty :=
        | t_arr  : Ty -> Ty -> Ty
        | t_unit : Ty
        | t_fix  : Ty -> Ty
        | t_var  : Var -> Ty.

Inductive Exp :=
        | var    : Var -> Exp
        | lambda : Ty  -> Exp -> Exp
        | app    : Exp -> Exp -> Exp
        | fixx   : Ty  -> Exp -> Exp
        
        | fold   : Ty  -> Exp -> Exp
        | unfold : Exp -> Exp
        
        | unitt  : Exp.


Definition TTEnv := Env unit.
Definition TEnv := Env Ty.


Fixpoint raiseT (e : Ty) (a b : nat) :=
 match e with
 | t_var v     => t_var  (raise' a b v)
 | t_arr  p q  => t_arr  (raiseT p a b) (raiseT p a b)
 | t_unit      => t_unit
 | t_fix  x    => t_fix  (raiseT x a (S b))
 end.

Fixpoint subT' (e e' : Ty) (v : Var) :=
 match e with
 | t_var v'     => subst' v v' t_var e'
 | t_fix t      => t_fix (subT' t (raiseT e' 1 0) (S v))

 | t_arr  p q  => t_arr  (subT' p e' v) (subT' p e' v)
 | t_unit      => t_unit
 end.

Definition subT e e' := subT' e e' 0.


Inductive TyWf (env:TTEnv) : Ty -> Prop :=
 | twf_env v : InEnv v tt env -> TyWf env (t_var v)
 | twf_arr t1 t2
   : TyWf env t1
  -> TyWf env t2
  -> TyWf env (t_arr t1 t2)
 | twf_fix t
   : TyWf (tt :: env) t 
  -> TyWf        env  (t_fix t)

 | twf_unit : TyWf env t_unit.

(* Is TyWf necessary?
   Is there a way to make the TyWf[]t requirements neater or less repetitive? *)
Inductive TYPE (env : TEnv) : Exp -> Ty -> Prop :=
 | ty_env (v : Var) (t : Ty)
   : InEnv v t env
  -> TyWf [] t
  -> TYPE env (var v) t

 | ty_lam b t1 t2
   : TYPE (t1 :: env) b t2
  -> TyWf [] (t_arr t1 t2)
  -> TYPE env (lambda t1 b) (t_arr t1 t2)

 | ty_app e1 e2 t1 t2
   : TYPE env e1 (t_arr t1 t2)
  -> TYPE env e2 t1
  -> TyWf [] t2
  -> TYPE env (app e1 e2) t2

 | ty_fixx t e
   : TYPE (t :: env) e t
  -> TyWf [] t
  -> TYPE env (fixx t e) t


 | ty_fold t e
   : TYPE env e          (subT t (t_fix t))
  -> TyWf [] (t_fix t)
  -> TYPE env (fold t e) (t_fix t)

 | ty_unfold t e
   : TYPE env e          (t_fix t)
  -> TyWf [] (subT t (t_fix t))
  -> TYPE env (unfold e) (subT t (t_fix t)).


Lemma unicity
	(env: TEnv) (e : Exp) (t1 t2 : Ty)
	(Ht1 : TYPE env e t1)
	(Ht2 : TYPE env e t2)
	: t1 = t2.
Proof.
  revert t2 Ht2.
  induction Ht1; intros; inversion Ht2; subst; try congruence.
  
  apply IHHt1 in H2. congruence.

  apply IHHt1_1 in H2. congruence.

  apply IHHt1 in H1. congruence.
Qed.


Fixpoint raise (e : Exp) (a b : nat) :=
 match e with
 | var v       => var (raise' a b v)
 | lambda t x  => lambda t (raise x a (S b))
 | app f x     => app (raise f a b) (raise x a b)
 | fixx t x    => fixx t (raise x a (S b))

 | fold t e    => fold t (raise e a b)
 | unfold e    => unfold (raise e a b)

 | unitt       => unitt
 end.

Lemma raise_0_id (e : Exp) (n : nat) :
	raise e 0 n = e.
Proof.
 revert n.
 induction e; intros; simpl; try (rewrite IHe1, IHe2); try rewrite IHe; try rewrite IHe3; try reflexivity.
 unfold raise, raise'.
 destruct (ge_dec v n); auto.
Qed.

Lemma raise_S (e : Exp) (a b : nat) :
	raise e (S a) b = raise (raise e a b) 1 b.
Proof.
 revert a b.
 induction e; intros; simpl; try (rewrite IHe1, IHe2); try rewrite IHe; try rewrite IHe3; try reflexivity.
 unfold raise, raise'.
 destruct (ge_dec v b); auto.
 destruct (ge_dec (a+v) b); auto.
  omega.
 destruct (ge_dec v b); auto.
  omega. 
Qed.



Fixpoint subst (e e' : Exp) (v : Var) :=
 match e with
 | var v'       => subst' v v' var e'
 | lambda t x   => lambda t (subst x (raise e' 1 0) (S v))
 | app    f x   => app (subst f e' v) (subst x e' v)
 | fixx   t x   => fixx t (subst x (raise e' 1 0) (S v))

 | fold t e    => fold t (subst e e' v)
 | unfold e    => unfold (subst e e' v)

 | unitt       => unitt
 end.



Lemma weakening_insert
        (env : TEnv) (e : Exp) (te tvi : Ty) (vi : Var) :
        TYPE env e te ->
        TYPE (insert env vi tvi) (raise e 1 vi) te.
 intros Hte.
 revert vi tvi.
 induction Hte; intros; try solve [constructor; auto]; simpl.

 apply ty_env.
  unfold raise'.
   destruct (ge_dec v vi).
   apply get_insert_ge; assumption.
   apply get_insert_lt; try assumption; omega.
  assumption.

 apply ty_lam.
  rewrite <- uninsert.
  apply IHHte. assumption.

 eapply ty_app; eauto.

 eapply ty_fixx.
  rewrite <- uninsert; auto.
  assumption.
Qed.

Lemma weakening_cons
	(env : TEnv) (e : Exp) (te : Ty) tv : 
	TYPE env e te ->
	TYPE (tv :: env) (raise e 1 0) te.
Proof.
 rewrite <- insert_0.
 apply weakening_insert.
Qed.




Lemma substitution_ix env x t t' e e':
      TYPE (insert env x t) e'             t' ->
      TYPE env              e              t  ->
      x <= length env                         ->
      TYPE env              (subst e' e x) t'.
Proof.
 intros He' He Hlen.
 remember (insert env x t) as ENV.
 revert e x t env HeqENV He Hlen.
 induction He'; intros; subst; simpl; try constructor; try assumption.
  apply subst_cases; intros; subst.
   eapply InEnv_insert in H. rewrite <- H. assumption.
   apply insert_minus in H; try apply ty_env; try assumption; try omega.
   apply insert_pre in H; try apply ty_env; try assumption; try omega.

 eapply IHHe'; eauto; try reflexivity.
  apply weakening_cons; assumption.
  simpl; omega.

 eapply ty_app.
  eapply IHHe'1; auto.
  eapply IHHe'2; auto.
  assumption.

 eapply IHHe'; simpl; try omega; try reflexivity.
  apply weakening_cons.
  assumption.

 eapply IHHe'; eauto.
 eapply IHHe'; eauto.
Qed.


Lemma substitution env t t' e e':
      TYPE (t :: env)       e'             t' ->
      TYPE env              e              t  ->
      TYPE env              (subst e' e 0) t'.
Proof.
 intros.
 eapply substitution_ix; try rewrite insert_0; try eassumption; try omega.
Qed.


Inductive val : Exp -> Prop :=
 | v_lambda t b
   : val (lambda t b)
 | v_fold t e
   : val e
  -> val (fold t e)
 | v_u
   : val unitt.

Inductive e_step: Exp -> Exp -> Prop :=
 | e_ap1 e1 e1' e2
   : e_step      e1          e1'
  -> e_step (app e1 e2) (app e1' e2)
 | e_ap2 e1 e2 e2'
   : val e1
  -> e_step         e2          e2'
  -> e_step (app e1 e2) (app e1 e2')

 | e_lam  t b x
   : val x
  -> e_step (app (lambda t b) x) (subst b x 0)

 | e_fixx t e
   : e_step (fixx t e) (subst e (fixx t e) 0)


 | e_fold t e e'
   : e_step e e'
  -> e_step (fold t e) (fold t e')

 | e_unfold1 e e'
   : e_step e e'
  -> e_step (unfold e) (unfold e')
 | e_unfoldF t e
   : val (fold t e)
  -> e_step (unfold (fold t e)) e.



Theorem preservation env e e' t:
        TYPE env e t ->
        e_step e e'  ->
        TYPE env e' t.
Proof.
 intros Ht He.
 revert env t Ht.
 induction He; intros; inversion Ht; subst;
   try solve [try econstructor; try eapply IHHe; eassumption];
   try (eapply substitution; eassumption).
  inversion H2. subst.
  eapply substitution; eassumption.
  inversion H1; subst; assumption.
Qed.


Theorem progress e t:
        TYPE [] e t ->
        val e \/ exists e', e_step e e'.
Proof.
 remember [] as ENV.
 intros Ht.
 induction Ht; subst;
  try solve [apply not_InEnv_nil in H; destruct H];
  try solve [left; econstructor; eassumption].

 destruct IHHt1; try reflexivity.
 destruct IHHt2; try reflexivity.
 inversion H0; subst; inversion Ht1; subst.
 right.
  eexists. apply e_lam. assumption.
 destruct H1.
 right.
  eexists. apply e_ap2; eassumption.
 
 destruct H0.
 right.
  eexists. apply e_ap1; eassumption.

 right. eexists. eapply e_fixx.

 destruct IHHt; try reflexivity.
  left. constructor. assumption.
  destruct H0.
   right. eexists. constructor. eassumption.

 destruct IHHt; auto.
  inversion H0; subst; inversion Ht; subst.
  right. eexists. apply e_unfoldF. assumption.

  destruct H0.
  right. eexists. apply e_unfold1. eassumption.
Qed.