Module numstr.

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
	| lett : Var -> Exp -> Exp -> Exp.

Inductive Env :=
	| nil : Env
	| cons : Var -> Ty -> Env -> Env.

Inductive InEnv' (v : Var) (t : Ty) : Env -> Prop :=
	| ie_skip (v' : Var) (t' : Ty) (e : Env) : v <> v' -> InEnv' v t e -> InEnv' v t (cons v' t' e)
	| ie_here (e : Env) : InEnv' v t (cons v t e).

Inductive InEnv : Exp -> Ty -> Env -> Prop :=
	| ie (v : Var) (t : Ty) (e : Env) : InEnv' v t e -> InEnv (var v) t e.

Inductive NotInEnv' (v : Var) : Env -> Prop :=
	| nie_nil : NotInEnv' v nil
	| nie_cons (v' : Var) (t' : Ty) (e : Env) : v <> v' -> NotInEnv' v e -> NotInEnv' v (cons v' t' e).

Inductive NotInEnv : Exp -> Env -> Prop :=
	| nie (v : Var) (e : Env) : NotInEnv' v e -> NotInEnv (var v) e.



Inductive TyRules (env : Env) : Exp -> Ty -> Prop :=
	| ty_env (x : Exp) (t : Ty): (InEnv x t env) -> TyRules env x t
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
	| ty_lett (v : Var) (def body : Exp) (tdef tbody : Ty) :
		NotInEnv' v env ->
		TyRules env def tdef ->
		TyRules (cons v tdef env) body tbody ->
		TyRules env (lett v def body) tbody.

Lemma InEnv_unique
	(v : Var) (t1 t2 : Ty) (env : Env):
	InEnv' v t1 env -> InEnv' v t2 env
	-> t1 = t2.
Proof.
  intros Ht1 Ht2.
  induction Ht1 as [v' t' e Hne Hsmall|e].
   inversion Ht2.
    auto.
   unfold not in Hne.
   apply Hne in H0.
   inversion H0.
  inversion Ht2.
   unfold not in H1.
   assert (v = v) by reflexivity.
   apply H1 in H4. inversion H4.
  reflexivity.
Qed.

Lemma unicity_of_typing
	(env: Env) (e : Exp) (t1 t2 : Ty)
	(Ht1 : TyRules env e t1)
	(Ht2 : TyRules env e t2)
	: t1 = t2.
Proof.
  revert t2 Ht2.
  induction Ht1; intros.
    destruct H.
    inversion Ht2.
    inversion H0.
    apply (InEnv_unique v t t2 e); assumption.
   inversion Ht2. inversion H. reflexivity. 
   inversion Ht2. inversion H. reflexivity. 
   inversion Ht2. inversion H. reflexivity. 
   inversion Ht2. inversion H. reflexivity.
   inversion Ht2. inversion H. reflexivity.
   inversion Ht2. inversion H. reflexivity.
   inversion Ht2. inversion H0.
    subst.
    apply IHHt1_1 in H5.
    subst.
    apply IHHt1_2 in H6.
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



Lemma InEnv_NotInEnv__noteq
	(vIn vNi : Var) (env : Env) (t : Ty) :
	InEnv' vIn t env ->
	NotInEnv' vNi env ->
	vIn <> vNi.
Proof.
 intros HIn. revert vNi.
 induction HIn; intros vNi HNi.
  inversion HNi; subst.
  apply IHHIn in H4; assumption.

 inversion HNi; subst.
 auto.
Qed.

Lemma NotInEnv_rotate
	(v v1 v2 : Var) (t1 t2 : Ty) (env : Env) :
	NotInEnv' v (cons v1 t1 (cons v2 t2 env)) ->
	NotInEnv' v (cons v2 t2 (cons v1 t1 env)).
Proof.
 intros HNi.
 remember (cons v1 t1 (cons v2 t2 env)) as env'.
 destruct HNi.
  inversion Heqenv'.
 destruct HNi.
  inversion Heqenv'.
 assert (v' = v1) by congruence.
 assert (t' = t1) by congruence.
 assert (v'0 = v2) by congruence.
 assert (t'0 = t2) by congruence.
 assert (e = env) by congruence.
 subst.
 constructor.
  assumption.
 constructor.
  assumption.
 assumption.
Qed.

Fixpoint env_app (e1 e2 : Env) :=
	match e1 with
	| nil => e2
	| cons v t e1' => cons v t (env_app e1' e2)
	end.

Lemma env_rotate
	(v1 v2 : Var) (t1 t2 : Ty) (env : Env)
	(e : Exp) (t : Ty):
	v1 <> v2 ->
	TyRules (cons v1 t1 (cons v2 t2 env)) e t ->
	TyRules (cons v2 t2 (cons v1 t1 env)) e t.
Proof.
 intros Hne Ht.
 remember (cons v1 t1 (cons v2 t2 env)) as env'.
 induction Ht.
        destruct H.
        apply ty_env; apply ie.
        destruct H. destruct H0.
          assert (v' = v1) by congruence.
          assert (v'0 = v2) by congruence.
          assert (e = env) by congruence.
          subst.
          apply ie_skip. assumption.
          apply ie_skip. assumption.
          assumption.
         assert (v = v2) by congruence.
         assert (t = t2) by congruence.
         subst.
         apply ie_here.
        assert (v = v1) by congruence.
        assert (t = t1) by congruence.
        subst.
        apply ie_skip. assumption.
        apply ie_here.
       apply ty_str.
      apply ty_num.
     apply ty_plus; auto.
    apply ty_times; auto.
   apply ty_cat; auto.
  apply ty_len; auto.

 apply (ty_lett _ _ _ _ tdef _).
   subst.
   apply NotInEnv_rotate. assumption.
  auto.
 
  auto.
 subst.


         apply ie_skip. assumption.
         assumption.
  

Lemma weakening
	(env : Env) (e : Exp) (v : Var) (te tv : Ty) : 
	TyRules env e te ->
	NotInEnv' v env ->
	TyRules (cons v tv env) e te.
Proof.
 intros Hte Hnie.
 induction Hte.
        destruct H.
        assert (v0 <> v) by (apply (InEnv_NotInEnv__noteq _ _ e t); assumption).
        apply ty_env; apply ie; apply ie_skip; assumption.
       apply ty_str.
      apply ty_num.
     apply ty_plus; auto.
    apply ty_times; auto.
   apply ty_cat; auto.
  apply ty_len; auto.
 apply (ty_lett _ v0 def body tdef tbody).
  auto.


