(* Recursive types *)

Require Import Env.
Require Import TransitiveClosure.

Inductive Ty :=
        | t_arr  : Ty -> Ty -> Ty
        | t_unit : Ty
        | t_sum  : Ty -> Ty -> Ty
        | t_prod : Ty -> Ty -> Ty
        | t_fix  : Ty -> Ty
        | t_var  : Var -> Ty.

Inductive Exp :=
        | var    : Var -> Exp
        | lambda : Ty  -> Exp -> Exp
        | app    : Exp -> Exp -> Exp
        | fixx   : Ty  -> Exp -> Exp
        
        | fold   : Ty  -> Exp -> Exp
        | unfold : Exp -> Exp
        
        | unitt  : Exp
        | inl    : Exp -> Ty  -> Exp
        | inr    : Ty  -> Exp -> Exp
        | prod   : Exp -> Exp -> Exp

        | case   : Exp -> Exp -> Exp -> Exp
        | fst    : Exp -> Exp
        | snd    : Exp -> Exp.


Definition TTEnv := Env unit.
Definition TEnv := Env Ty.


Fixpoint raiseT (e : Ty) (a b : nat) :=
 match e with
 | t_var v     => t_var  (raise' a b v)
 | t_arr  p q  => t_arr  (raiseT p a b) (raiseT p a b)
 | t_unit      => t_unit
 | t_sum  p q  => t_sum  (raiseT p a b) (raiseT p a b)
 | t_prod p q  => t_prod (raiseT p a b) (raiseT p a b)
 | t_fix  x    => t_fix  (raiseT x a (S b))
 end.

Fixpoint subT' (e e' : Ty) (v : Var) :=
 match e with
 | t_var v'     => subst' v v' t_var e'
 | t_fix t      => t_fix (subT' t (raiseT e' 1 0) (S v))

 | t_arr  p q  => t_arr  (subT' p e' v) (subT' p e' v)
 | t_unit      => t_unit
 | t_sum  p q  => t_sum  (subT' p e' v) (subT' p e' v)
 | t_prod p q  => t_prod (subT' p e' v) (subT' p e' v)
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

 | twf_unit : TyWf env t_unit

 | twf_sum t1 t2
   : TyWf env t1
  -> TyWf env t2
  -> TyWf env (t_sum t1 t2)

 | twf_prod t1 t2
   : TyWf env t1
  -> TyWf env t2
  -> TyWf env (t_prod t1 t2).


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
  -> TYPE env (unfold e) (subT t (t_fix t))


 | ty_unitt
   : TYPE env unitt t_unit

 | ty_inl e t1 t2
   : TYPE env e t1
  -> TYPE env (inl e t2) (t_sum t1 t2)

 | ty_inr e t1 t2
   : TYPE env e t2
  -> TYPE env (inr t1 e) (t_sum t1 t2)

 | ty_prod e1 e2 t1 t2
   : TYPE env e1 t1
  -> TYPE env e2 t2
  -> TYPE env (prod e1 e2) (t_prod t1 t2)

 | ty_case es el er t1 t2 tR
   : TYPE env es (t_sum t1 t2)
  -> TYPE (t1::env) el tR
  -> TYPE (t2::env) er tR
  -> TYPE env (case es el er) tR

 | ty_fst e t1 t2
   : TYPE env e      (t_prod t1 t2)
  -> TYPE env (fst e) t1
 | ty_snd e t1 t2
   : TYPE env e      (t_prod t1 t2)
  -> TYPE env (snd e) t2.

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
  apply IHHt1 in H2. congruence.
  apply IHHt1 in H2. congruence.
  apply IHHt1_1 in H1.
  apply IHHt1_2 in H3. congruence.

  apply IHHt1_1 in H2.
  replace t1 with t3 in * by congruence.
  replace t2 with t4 in * by congruence.
  apply IHHt1_2 in H4.
  apply IHHt1_3 in H5.
  congruence.

  apply IHHt1 in H0. congruence.
  apply IHHt1 in H0. congruence.
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
 | inl e t     => inl (raise e a b) t
 | inr t e     => inr t (raise e a b)
 | prod x y    => prod (raise x a b) (raise y a b)

 | case s l r  => case (raise s a b) (raise l a (S b)) (raise r a (S b))
 | fst e       => fst (raise e a b)
 | snd e       => snd (raise e a b)
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
 | inl e t     => inl (subst e e' v) t
 | inr t e     => inr t (subst e e' v)
 | prod x y    => prod (subst x e' v) (subst y e' v)

 | case s l r  => case (subst s e' v) (subst l (raise e' 1 0) (S v)) (subst r (raise e' 1 0) (S v))
 | fst e       => fst (subst e e' v)
 | snd e       => snd (subst e e' v)
 end.



Lemma weakening_insert
        (env : TEnv) (e : Exp) (te tvi : Ty) (vi : Var) :
        TYPE env e te ->
        TYPE (insert env vi tvi) (raise e 1 vi) te.
 intros Hte.
 revert vi tvi.
 induction Hte; intros; try solve [econstructor; try rewrite <- uninsert; eauto]; simpl.

 apply ty_env.
  unfold raise'.
   destruct (ge_dec v vi).
   apply get_insert_ge; assumption.
   apply get_insert_lt; try assumption; omega.
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
 induction He'; intros; subst; simpl; try constructor; try assumption;
  try solve [eapply IHHe'; eauto].
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

 eapply IHHe'1; auto.
 eapply IHHe'2; auto.

 eapply ty_case; eauto.
  eapply IHHe'2.
   reflexivity.
   apply weakening_cons; auto.
   simpl. omega.
  eapply IHHe'3.
   reflexivity.
   apply weakening_cons; auto.
   simpl. omega.

 eapply ty_fst.
  eapply IHHe'; auto.
 econstructor;
  eapply IHHe'; auto.
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
   : val unitt
 | v_inl e t
   : val e
  -> val (inl e t)
 | v_inr t e
   : val e
  -> val (inr t e)
 | v_prod x y
   : val x
  -> val y
  -> val (prod x y).

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
  -> e_step (unfold (fold t e)) e


 | e_inl e e' t
   : e_step e e'
  -> e_step (inl e t) (inl e' t)
 | e_inr t e e'
   : e_step e e'
  -> e_step (inr t e) (inr t e')

 | e_prod1 e1 e1' e2
   : e_step e1 e1'
  -> e_step (prod e1 e2) (prod e1' e2)
 | e_prod2 e1 e2 e2'
   : val e1
  -> e_step e2 e2'
  -> e_step (prod e1 e2) (prod e1 e2')

 | e_case e e' l r
   : e_step e e'
  -> e_step (case e l r) (case e' l r)
 | e_caseL e t l r
   : e_step (case (inl e t) l r) (subst l e 0)
 | e_caseR t e l r
   : e_step (case (inr t e) l r) (subst r e 0)

 | e_fst e e'
   : e_step e e'
  -> e_step (fst e) (fst e')
 | e_fstP e1 e2
   : val (prod e1 e2)
  -> e_step (fst (prod e1 e2)) e1

 | e_snd e e'
   : e_step e e'
  -> e_step (snd e) (snd e')
 | e_sndP e1 e2
   : val (prod e1 e2)
  -> e_step (snd (prod e1 e2)) e2.


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

  eapply substitution. eassumption.
   inversion H2; auto.
  eapply substitution. eassumption.
   inversion H2; auto.

  inversion H1; auto.
  inversion H1; auto.
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

 destruct IHHt; auto.
  left; constructor; assumption.
  destruct H.
   right; eexists; econstructor; eauto.

 destruct IHHt; auto.
  left; constructor; assumption.
  destruct H.
   right; eexists; econstructor; eauto.

 destruct IHHt1; auto.
 destruct IHHt2; auto.
  left; constructor; auto.
  destruct H0.
  right. eexists. apply e_prod2; eauto.
 destruct H.
  right. eexists. apply e_prod1; eauto.

 destruct IHHt1; auto; right.
  inversion H; subst; inversion Ht1; subst.
   eexists. apply e_caseL.
   eexists. apply e_caseR.
  destruct H.
   eexists. apply e_case. eassumption.

 destruct IHHt; auto; right.
  inversion H; subst; inversion Ht; subst.
   eexists; apply e_fstP; auto.
  destruct H.
   eexists; apply e_fst; eauto.
 
 destruct IHHt; auto; right.
  inversion H; subst; inversion Ht; subst.
   eexists; apply e_sndP; auto.
  destruct H.
   eexists; apply e_snd; eauto.
Qed.
