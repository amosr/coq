(* Pattern matching *)

Require Import Env.
Require Import TransitiveClosure.

Inductive Ty :=
        | t_unit  : Ty
        | t_arr   : Ty -> Ty -> Ty
        | t_pair  : Ty -> Ty -> Ty
        | t_sum   : Ty -> Ty -> Ty.

Inductive Pattern :=
        | p_wild  : Pattern
        | p_var   : Pattern
        | p_unit  : Pattern
        | p_pair  : Pattern -> Pattern -> Pattern
        | p_inl   : Pattern -> Pattern
        | p_inr   : Pattern -> Pattern.

Fixpoint pattern_vars p :=
 match p with
 | p_wild => 0
 | p_var  => 1
 | p_unit => 0
 | p_pair p q => pattern_vars p + pattern_vars q
 | p_inl p => pattern_vars p
 | p_inr p => pattern_vars p
 end.

(*
Inductive Pattern : nat -> Set :=
        | p_wild  : Pattern 0
        | p_var   : Pattern 1
        | p_unit  : Pattern 0
        | p_pair  n m
                  : Pattern n -> Pattern m -> Pattern (n+m)
        | p_inl   n : Pattern n -> Pattern n
        | p_inr   n : Pattern n -> Pattern n.
*)


Inductive Exp :=
        | var    : Var -> Exp
        | lambda : Ty  -> Exp -> Exp
        | app    : Exp -> Exp -> Exp
        | pair   : Exp -> Exp -> Exp
        | inl    : Exp  -> Exp
        | inr    : Exp -> Exp
        | unitt  : Exp
        | matchh 
          : Exp -> listne -> Exp
with
 listne := | lne : listPE -> Pattern -> Exp -> listne
with
 listPE := | lpe_nil : listPE
           | lpe_cons: Pattern -> Exp -> listPE -> listPE.

Check Exp_rec.

Scheme Exp_all_rec := Induction for Exp Sort Set
with listne_all_rec := Induction for listne Sort Set
with listPE_all_rec := Induction for listPE Sort Set.

Check Exp_all_rec.

Definition TEnv := Env Ty.


(* This is the ||- judgment in the book *)
Inductive DBLTACK : TEnv -> Pattern -> Ty -> Prop :=
 | dt_var t
   : DBLTACK [t] p_var t (* x : t ||- _ x : t *)
 | dt_wild t
   : DBLTACK [] p_wild t (* nil ||- _ : t *)
 | dt_unit
   : DBLTACK [] p_unit t_unit
 | dt_pair e1 e2 p1 p2 t1 t2
   : DBLTACK e1 p1 t1
  -> DBLTACK e2 p2 t2
  -> DBLTACK (e1 ++ e2) (p_pair p1 p2) (t_pair t1 t2)
 | dt_inl e1 p1 t1 t2
   : DBLTACK e1 p1 t1
  -> DBLTACK e1 (p_inl p1) (t_sum t1 t2)
 | dt_inr e2 p2 t1 t2
   : DBLTACK e2 p2 t2
  -> DBLTACK e2 (p_inr p2) (t_sum t1 t2).

Lemma DBLTACK_env_len__pattern_vars env p t :
   DBLTACK env p t ->
   length env = pattern_vars p.
Proof.
 intros Hdb.
 induction Hdb; auto.
 simpl.
 rewrite app_length.
 auto.
Qed.

Inductive TYPE (env : TEnv) : Exp -> Ty -> Prop :=
 | ty_env v t
   : InEnv v t env
  -> TYPE env (var v) t

 | ty_lambda b ty tb
   : TYPE (ty :: env) b tb
  -> TYPE env (lambda ty b) (t_arr ty tb)
 | ty_app f x t1 t2
   : TYPE env f        (t_arr t1 t2)
  -> TYPE env x         t1
  -> TYPE env (app f x) t2

 | ty_pair e1 e2 t1 t2
   : TYPE env e1 t1
  -> TYPE env e2 t2
  -> TYPE env (pair e1 e2) (t_pair t1 t2)
 | ty_inl e1 t1 t2
   : TYPE env e1 t1
  -> TYPE env (inl e1) (t_sum t1 t2)
 | ty_inr e2 t1 t2
   : TYPE env e2 t2
  -> TYPE env (inr e2) (t_sum t1 t2)

 | ty_unitt : TYPE env unitt t_unit

 | ty_matchh_nil es penv px pt ex tx
   : DBLTACK penv px pt
  -> TYPE (penv ++ env) ex tx
  -> TYPE env           es pt
  -> TYPE env   (matchh es (lne (lpe_nil) px ex)) tx

 | ty_matchh_cons es penv px pt ex tx rest pts ets
   : DBLTACK penv px pt
  -> TYPE (penv ++ env) ex tx
  -> TYPE env           es pt
  -> TYPE env   (matchh es (lne rest pts ets)) tx
  -> TYPE env   (matchh es (lne (lpe_cons px ex rest) pts ets)) tx.

(* I don't think we can prove unicity of typing
   without the explicit types on inl/inr. *)

(*Lemma unicity
	(env: TEnv) (e : Exp) (t1 t2 : Ty)
	(Ht1 : TYPE env e t1)
	(Ht2 : TYPE env e t2)
	: t1 = t2.
*)


Fixpoint raise (e : Exp) (a b : nat) :=
 match e with
 | var v       => var (raise' a b v)
 | lambda t x  => lambda t (raise x a (S b))
 | app f x     => app (raise f a b) (raise x a b)
 | pair p q    => pair (raise p a b) (raise q a b)
 | inl  x      => inl (raise x a b)
 | inr  x      => inr (raise x a b)
 | unitt       => unitt
 | matchh s l =>
        matchh (raise s a b) (raiseNE l a b)
 end
with raiseNE (p : listne) (a b : nat) :=
 match p with
 | lne r p e => (lne (raiseLIST r a b) p (raise e a (b + pattern_vars p)))
 end
with raiseLIST (p : listPE) (a b : nat) :=
 match p with
 | lpe_nil => lpe_nil
 | lpe_cons p e rest => lpe_cons p (raise e a (b + pattern_vars p)) (raiseLIST rest a b)
 end.

Lemma raise_0_id (e : Exp) (n : nat) :
	raise e 0 n = e.
Proof.
 revert n.
 einduction e using Exp_all_rec
   with 
   (P0 := (fun l => (forall n, raiseNE l 0 n = l)))
   (P1 := (fun l => (forall n, raiseLIST l 0 n = l)));
 intros; simpl; try (rewrite IHe0_1, IHe0_2); try rewrite IHe0; try rewrite IHe3; try reflexivity.
 unfold raise, raise'.
 destruct (ge_dec v n); auto.

 rewrite IHe1. reflexivity.

 rewrite IHe1. reflexivity.

 rewrite IHe1. reflexivity.
Qed.


Lemma raise_S (e : Exp) (a b : nat) :
	raise e (S a) b = raise (raise e a b) 1 b.
Proof.
 revert a b.
 einduction e using Exp_all_rec
   with
   (P0 := fun l => forall a b, raiseNE l (S a) b = raiseNE (raiseNE l a b) 1 b)
   (P1 := fun l => forall a b, raiseLIST l (S a) b = raiseLIST (raiseLIST l a b) 1 b)
; intros; simpl; try (rewrite IHe0_1, IHe0_2); try rewrite IHe0; try rewrite IHe0_3; try reflexivity.
 unfold raise, raise'.
 destruct (ge_dec v b); auto.
 destruct (ge_dec (a+v) b); auto.
  omega.
 destruct (ge_dec v b); auto.
  omega. 

 rewrite IHe1. reflexivity.
 rewrite IHe1. reflexivity.
 rewrite IHe1. reflexivity.
Qed.


Lemma insert_app_start {T} e1 e2 v (t:T) :
      (e1 ++ insert e2 v t) = insert (e1 ++ e2) (length e1 + v) t.
Proof.
 induction e1.
  reflexivity.
  simpl.
  rewrite IHe1.
  reflexivity.
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

 apply ty_lambda.
  rewrite <- uninsert; auto.

 eapply ty_app; auto.

 eapply ty_matchh_nil.
  eassumption.
  rewrite insert_app_start.
  rewrite <- DBLTACK_env_len__pattern_vars with (p := px) (t := pt) (env := penv).
  rewrite plus_comm.
  eapply IHHte1.
  assumption.
 apply IHHte2.

 eapply ty_matchh_cons.
  eassumption.
  rewrite insert_app_start.
  rewrite <- DBLTACK_env_len__pattern_vars with (p := px) (t := pt) (env := penv).
  rewrite plus_comm.
  eapply IHHte1. assumption.
  eapply IHHte2.
  eapply IHHte3.
Qed.

Lemma weakening_cons
	(env : TEnv) (e : Exp) (te : Ty) tv : 
	TYPE env e te ->
	TYPE (tv :: env) (raise e 1 0) te.
Proof.
 rewrite <- insert_0.
 apply weakening_insert.
Qed.


Lemma weakening_app
	(env1 env2 : TEnv) (e : Exp) (te : Ty) : 
	TYPE env2 e te ->
	TYPE (env1 ++ env2) (raise e (length env1) 0) te.
Proof.
 intros Ht.
 induction env1.
 simpl. rewrite raise_0_id. assumption.
 simpl.
 rewrite raise_S.
 apply weakening_cons.
 assumption.
Qed.


Fixpoint subst (e e' : Exp) (v : Var) :=
 match e with
 | var v'       => subst' v v' var e'
 | lambda t x   => lambda t (subst x (raise e' 1 0) (S v))
 | app    f x   => app (subst f e' v) (subst x e' v)
 | matchh s ps  => matchh (subst s e' v) (substNE ps e' v)

 | pair   x y   => pair (subst x e' v) (subst y e' v)
 | inl    x     => inl  (subst x e' v)
 | inr      y   => inr  (subst y e' v)
 | unitt        => unitt
 end
with substNE ps e' v :=
 match ps with
 | lne l p e => lne (substPE l e' v) p (subst e (raise e' (pattern_vars p) 0) (v + pattern_vars p))
 end
with substPE l e' v :=
 match l with
 | lpe_nil => lpe_nil
 | lpe_cons p e l' => lpe_cons p (subst e (raise e' (pattern_vars p) 0) (v + pattern_vars p)) (substPE l' e' v)
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
  reflexivity.
  apply weakening_cons. assumption.
  simpl. omega.

 apply ty_app with (t1 := t1).
  eapply IHHe'1; auto.
  eapply IHHe'2; auto.
 
 eapply IHHe'1; auto.
 eapply IHHe'2; auto.

 eapply IHHe'; auto.
 eapply IHHe'; auto.

 eapply ty_matchh_nil.
  eassumption.
  eapply IHHe'1.
  rewrite insert_app_start.
  rewrite <- DBLTACK_env_len__pattern_vars with (p := px) (t := pt) (env := penv).
  rewrite plus_comm.
  reflexivity.
  assumption.
  rewrite <- DBLTACK_env_len__pattern_vars with (p := px) (t := pt) (env := penv).
  apply weakening_app. assumption.
  assumption.
  rewrite <- DBLTACK_env_len__pattern_vars with (p := px) (t := pt) (env := penv).
  rewrite app_length.
  omega.
  assumption.
  eapply IHHe'2.
  reflexivity.
  assumption.
  assumption.

 eapply ty_matchh_cons.
  eassumption.

  eapply IHHe'1.
  rewrite insert_app_start.
  rewrite <- DBLTACK_env_len__pattern_vars with (p := px) (t := pt) (env := penv).
  rewrite plus_comm.
  reflexivity.
  assumption.
  rewrite <- DBLTACK_env_len__pattern_vars with (p := px) (t := pt) (env := penv).
  apply weakening_app. assumption.
  assumption.
  rewrite <- DBLTACK_env_len__pattern_vars with (p := px) (t := pt) (env := penv).
  rewrite app_length.
  omega.
  assumption.
  eapply IHHe'2.
  reflexivity.
  assumption.
  assumption.

 eapply IHHe'3.
 reflexivity.
 assumption.
 assumption.
Qed.

Lemma substitution env t t' e e':
      TYPE (t :: env)       e'             t' ->
      TYPE env              e              t  ->
      TYPE env              (subst e' e 0) t'.
Proof.
 intros.
 eapply substitution_ix; try rewrite insert_0; try eassumption; try omega.
Qed.


Definition Sub(*stitution*) := Env Exp.

Inductive Match : Sub -> Pattern -> Exp -> Prop :=
 | m_var  e : Match [e] p_var e
 | m_wild e : Match []  p_wild e
 | m_unit   : Match []  p_unit unitt
 | m_pair s1 s2 p1 p2 e1 e2
   : Match s1 p1 e1
  -> Match s2 p2 e2
  -> Match (s1++s2) (p_pair p1 p2) (pair e1 e2)
 | m_inl s p e
   : Match s p e
  -> Match s (p_inl p) (inl e)
 | m_inr s p e
   : Match s p e
  -> Match s (p_inr p) (inr e).

Inductive NoMatch : Pattern -> Exp -> Prop :=
 | nm_pair1 p1 p2 e1 e2
   : NoMatch p1 e1
  -> NoMatch (p_pair p1 p2) (pair e1 e2)
 | nm_pair2 p1 p2 e1 e2
   : NoMatch p2 e2
  -> NoMatch (p_pair p1 p2) (pair e1 e2)
 | nm_lr p e
   : NoMatch (p_inl p) (inr e)
 | nm_rl p e
   : NoMatch (p_inr p) (inl e)
 | nm_ll p e
   : NoMatch p e
  -> NoMatch (p_inl p) (inl e)
 | nm_rr p e
   : NoMatch p e
  -> NoMatch (p_inr p) (inr e).


Lemma Match_sub_length s p e:
      Match s p e ->
      length s = pattern_vars p.
Proof.
 intros Hm.
 induction Hm; try rewrite app_length; simpl; auto.
Qed.

Lemma Match_NoMatch_ex s p e:
      Match s p e -> ~ NoMatch p e.
Proof.
 intros Hm Hnot.
 induction Hm; inversion Hnot; auto.
Qed.

Lemma NoMatch_Match_ex s p e:
      NoMatch p e -> ~ Match s p e.
Proof.
 intros Hm Hnot.  revert s Hnot.
 induction Hm; intros; inversion Hnot; auto; subst.
  apply IHHm in H3. destruct H3.
  apply IHHm in H5. destruct H5.
  apply IHHm in H2. destruct H2.
  apply IHHm in H2. destruct H2.
Qed.


Inductive val : Exp -> Prop :=
 | v_l t b : val (lambda t b)
 | v_pair p q: val p -> val q -> val (pair p q)
 | v_inl p : val p -> val (inl p)
 | v_inr p : val p -> val (inr p)
 | v_unitt : val unitt.

Lemma t13_1 e t penv p :
  TYPE [] e t ->
  val e ->
  DBLTACK penv p t ->
  (exists s, Match s p e) \/ NoMatch p e.
Proof.
 intros Ht Hv Hd. revert e Ht Hv.
 induction Hd; intros;
  inversion Hv; subst; inversion Ht; subst;
  try solve [left; eexists; try econstructor; eauto];
  try solve [right; try econstructor; eauto].

 edestruct IHHd1; try eassumption.
 destruct H1.
 edestruct IHHd2; try eassumption.
 destruct H2.

 left; eexists; econstructor; eauto.
 right; apply nm_pair2; assumption.
 right; apply nm_pair1; assumption.

 edestruct IHHd; try eassumption.
 destruct H0.
 left; eexists; econstructor; eauto.
 right; econstructor; assumption.

 edestruct IHHd; try eassumption.
 destruct H0.
 left; eexists; econstructor; eauto.
 right; econstructor; assumption.
Qed.

Definition subst_all subs e := fold_right (fun p q => subst q p 0) e subs.

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

 | e_pa1 e1 e1' e2
            : e_step      e1          e1'
           -> e_step (pair e1 e2) (pair e1' e2)
 | e_pa2 e1 e2 e2'
            : val e1
           -> e_step         e2          e2'
           -> e_step (pair e1 e2) (pair e1 e2')

 | e_inl e e'
            : e_step      e       e'
           -> e_step (inl e) (inl e')
 | e_inr e e'
            : e_step      e       e'
           -> e_step (inr e) (inr e')
 
 | matchh1 e e' rs
            : e_step      e       e'
           -> e_step (matchh e rs) (matchh e' rs)

 | matchh_here_pe s sub p e rest nep nee
            : val s
           -> Match sub p s
           -> e_step (matchh s (lne (lpe_cons p e rest) nep nee))
                     (subst_all sub e)

 | matchh_next_pe s p e rest nep nee
            : val s
           -> NoMatch p s
           -> e_step (matchh s (lne (lpe_cons p e rest) nep nee))
                     (matchh s (lne rest nep nee))

 | matchh_here_ne s sub nep nee
            : val s
           -> Match sub nep s
           -> e_step (matchh s (lne (lpe_nil) nep nee))
                     (subst_all sub nee).


Theorem preservation env e e' t:
        TYPE env e t ->
        e_step e e'  ->
        TYPE env e' t.
Proof.
 intros Ht He.
 revert env t Ht.
 induction He; intros;
   try solve [inversion Ht; subst; try econstructor; try eapply IHHe; eassumption].

  inversion Ht; subst;
  inversion H2; subst.
  eapply substitution; eassumption.


  destruct rs.
  induction l.
  inversion Ht; subst.
   eapply ty_matchh_nil; try eassumption.
   apply IHHe. assumption.
  
  inversion Ht; subst.
   eapply ty_matchh_cons; try eassumption.
   apply IHHe. assumption.
   apply IHl. assumption.

  inversion Ht; subst.
  assert (length sub = pattern_vars p) by (eapply Match_sub_length; eassumption).
  assert (length penv = pattern_vars p) by (eapply DBLTACK_env_len__pattern_vars; eassumption).
  
(*  generalize dependent e.
  generalize dependent env.
  generalize dependent t.
  generalize dependent penv.
  generalize dependent pt.
  generalize dependent p.
  generalize dependent s.*)
  induction sub; intros.
   simpl.
   assert (penv = []). destruct penv; subst; auto. simpl in H2. rewrite <- H2 in H1. simpl in H1. omega.
   subst.
   assumption.

  simpl.
  eapply substitution.
 (*TODO need to track types of substitution *)


(*  eapply IHsub; try eassumption.


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