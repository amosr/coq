(* Plotkin's PCF *)

Require Import Env.
Require Import TransitiveClosure.

(* arrow is partial *)
Inductive Ty :=
        | t_num   : Ty
        | t_parr : Ty -> Ty -> Ty.

Inductive Exp :=
        | var    : Var -> Exp
        | z      : Exp
        | s      : Exp -> Exp
        | ifz    : Exp -> Exp -> Exp -> Exp
        | lambda : Ty  -> Exp -> Exp
        | app    : Exp -> Exp -> Exp
        | fixx   : Ty  -> Exp -> Exp.

Fixpoint numof n := match n with
 | O    => z
 | S n' => s (numof n')
 end.

Definition TEnv := Env Ty.

Inductive TYPE (env : TEnv) : Exp -> Ty -> Prop :=
        | ty_env (v : Var) (t : Ty): (InEnv v t env) -> TYPE env (var v) t
        | ty_z   : TYPE env z t_num
        | ty_s (n : Exp) : TYPE env n t_num -> TYPE env (s n) t_num

        | ty_ifz (n ez es : Exp) (t : Ty) :
                TYPE env n  t_num           ->
                TYPE env ez t               ->
                TYPE (t_num :: env) es t    ->
                TYPE env (ifz n ez es) t

        | ty_lambda (body : Exp) (ty tbody : Ty) :
		TYPE (ty :: env) body tbody ->
		TYPE env (lambda ty body) (t_parr ty tbody)
        | ty_app (f x : Exp) (t1 t2 : Ty) :
		TYPE env f (t_parr t1 t2) ->
		TYPE env x t1 ->
		TYPE env (app f x) t2

        | ty_fixx e t :
                TYPE (t :: env) e t ->
                TYPE env (fixx t e) t.

Lemma unicity
	(env: TEnv) (e : Exp) (t1 t2 : Ty)
	(Ht1 : TYPE env e t1)
	(Ht2 : TYPE env e t2)
	: t1 = t2.
Proof.
  revert t2 Ht2.
  induction Ht1; intros; inversion Ht2; subst; try congruence.
  
  apply IHHt1_2; assumption.

  f_equal. apply IHHt1. assumption.
  
  apply IHHt1_1 in H1.
  apply IHHt1_2 in H3.
  congruence.
Qed.

Fixpoint raise (e : Exp) (a b : nat) :=
 match e with
 | var v       => var (raise' a b v)
 | z           => z
 | s n         => s (raise n a b)
 | ifz n ez es => ifz (raise n a b) (raise ez a b) (raise es a (S b))
 | lambda t x  => lambda t (raise x a (S b))
 | app f x     => app (raise f a b) (raise x a b)
 | fixx t x    => fixx t (raise x a (S b))
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

 apply ty_ifz; auto.
  rewrite <- uninsert.
  apply IHHte3.

 apply ty_lambda.
  rewrite <- uninsert; auto.

 eapply ty_app; auto.

 eapply ty_fixx.
  rewrite <- uninsert.
  eapply IHHte.
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
 | var v'       => subst' v v' var e'
 | z            => z
 | s n          => s (subst n e' v)
 | ifz n ez es  => ifz (subst n e' v) (subst ez e' v) (subst es (raise e' 1 0) (S v))
 | lambda t x   => lambda t (subst x (raise e' 1 0) (S v))
 | app    f x   => app (subst f e' v) (subst x e' v)
 | fixx   t x   => fixx t (subst x (raise e' 1 0) (S v))
 end.

Lemma substitution_ix env x t t' e e':
      TYPE (insert env x t) e'             t' ->
      TYPE env              e              t  ->
      x <= length env                         ->
      TYPE env              (subst e' e x) t'.
Proof.
 intros He' He Hlen.
 remember (insert env x t) as ENV.
 revert e x t env HeqENV He Hlen.
 induction He'; intros; subst; simpl; try constructor.
  apply subst_cases; intros; subst.
   eapply InEnv_insert in H. rewrite <- H. assumption.
   apply insert_minus in H; try apply ty_env; try assumption; try omega.
   apply insert_pre in H; try apply ty_env; try assumption; try omega.

 eapply IHHe'; auto.
 eapply IHHe'1; auto.
 eapply IHHe'2; auto.
 eapply IHHe'3; simpl; try omega; try reflexivity.
  apply weakening_cons.
  assumption.

 eapply IHHe'; simpl; try omega; try reflexivity.
  apply weakening_cons.
  assumption.

 eapply ty_app.
  eapply IHHe'1; simpl; try omega; try reflexivity; assumption.
  eapply IHHe'2; simpl; try omega; try reflexivity; assumption.

 eapply IHHe'.
 reflexivity.

 apply weakening_cons. assumption.

 simpl. omega.
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
 | v_z     : val z
 | v_s n   : val n -> val (s n)
 | v_l t b : val (lambda t b).


Inductive e_step: Exp -> Exp -> Prop :=
 | e_s n n'
            : e_step    n     n'
           -> e_step (s n) (s n')
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

 | e_if1 e e' ez es
            : e_step e e'
           -> e_step (ifz e ez es) (ifz e' ez es)
 | e_ifz ez es
            : e_step (ifz z ez es) ez
 | e_ifs e ez es
            : val e
           -> e_step (ifz (s e) ez es)
                     (subst es e 0)

 | e_fixx t e
            : e_step (fixx t e) (subst e (fixx t e) 0).



Theorem preservation env e e' t:
        TYPE env e t ->
        e_step e e'  ->
        TYPE env e' t.
Proof.
 intros Ht He.
 revert env t Ht.
 induction He; intros; inversion Ht; subst;
   try solve [try econstructor; try eapply IHHe; eassumption].

  inversion H2. subst.
  eapply substitution; eassumption.
 
  inversion H3.
  eapply substitution;
   eassumption.

  eapply substitution; eassumption.
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

 destruct IHHt. reflexivity.
 left. constructor. assumption.
 destruct H.
  right. eexists. constructor. eassumption.

 right.
 destruct IHHt1; try reflexivity.
  destruct n; inversion H.
   eexists. apply e_ifz.
   eexists. apply e_ifs. assumption.
   inversion Ht1.
 destruct H.
 eexists. apply e_if1. eassumption.

 destruct IHHt1; try reflexivity.
 destruct IHHt2; try reflexivity.
 inversion H; subst; inversion Ht1; subst.
 right.
  eexists. apply e_lam. assumption.
 destruct H0.
 right.
  eexists. apply e_ap2; eassumption.
 
 destruct H.
 right.
  eexists. apply e_ap1; eassumption.

 right.
  eexists. apply e_fixx.
Qed.