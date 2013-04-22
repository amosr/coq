(* Goedel's T *)

Require Import Env.
Require Import TransitiveClosure.

Inductive Ty :=
        | t_num   : Ty
        | t_arrow : Ty -> Ty -> Ty.

Inductive Exp :=
        | var    : Var -> Exp
        | z      : Exp
        | s      : Exp -> Exp
        | rec    : Exp -> Exp -> Exp -> Exp
        | lambda : Ty  -> Exp -> Exp
        | app    : Exp -> Exp -> Exp.

Fixpoint numof n := match n with
 | O    => z
 | S n' => s (numof n')
 end.

Definition TEnv := Env Ty.

Inductive TYPE (env : TEnv) : Exp -> Ty -> Prop :=
        | ty_env (v : Var) (t : Ty): (InEnv v t env) -> TYPE env (var v) t
        | ty_z   : TYPE env z t_num
        | ty_s (n : Exp) : TYPE env n t_num -> TYPE env (s n) t_num
        | ty_rec (n ez es : Exp) (t : Ty) :
                TYPE env n  t_num           ->
                TYPE env ez t               ->
                TYPE (t :: t_num :: env) es t ->
                TYPE env (rec n ez es) t

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
 | rec n ez es => rec (raise n a b) (raise ez a b) (raise es a (S (S b)))
 | lambda t x  => lambda t (raise x a (S b))
 | app f x     => app (raise f a b) (raise x a b)
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

 apply ty_rec; auto.
  rewrite <- uninsert.
  rewrite <- uninsert.
  apply IHHte3.

 apply ty_lambda.
  rewrite <- uninsert; auto.

 eapply ty_app; auto.
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
 | rec n ez es  => rec (subst n e' v) (subst ez e' v) (subst es (raise e' 2 0) (S (S v)))
 | lambda t x   => lambda t (subst x (raise e' 1 0) (S v))
 | app    f x   => app (subst f e' v) (subst x e' v)
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
  rewrite raise_S.
  apply weakening_cons.
  apply weakening_cons.
  assumption.

 eapply IHHe'; simpl; try omega; try reflexivity.
  apply weakening_cons.
  assumption.

 eapply ty_app.
  eapply IHHe'1; simpl; try omega; try reflexivity; assumption.
  eapply IHHe'2; simpl; try omega; try reflexivity; assumption.
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
 | e_rec1 e e' ez es
            : e_step e e'
           -> e_step (rec e ez es) (rec e' ez es)
 | e_recz ez es
            : e_step (rec z ez es) ez
 | e_recs e ez es
            : val e
           -> e_step (rec (s e) ez es)
                     (subst (subst es (raise (rec e ez es) 1 0) 0) e 0).


Lemma canon_num env e:
      TYPE env e t_num ->
      val e ->
      exists k, e = numof k.
Proof.
 intros Ht Hv.
 induction Hv.
 exists 0. reflexivity.
 destruct IHHv.
  inversion Ht. assumption.
 exists (S x). simpl. f_equal. assumption.

 inversion Ht.
Qed.


Lemma canon_arrow env e t1 t2:
      TYPE env e (t_arrow t1 t2) ->
      val e ->
      exists e2, e = lambda t1 e2.
Proof.
 intros Ht Hv.
 induction Hv; inversion Ht.
 exists b. reflexivity.
Qed.

Lemma raise_closed' env e t a:
      TYPE env e t ->
      e = raise e a (length env).
Proof.
 intros Ht.
 revert a.
 induction Ht; intros; simpl; subst; try f_equal; try auto.
  unfold raise'.
  apply InEnv__length in H.
  destruct (ge_dec).
   omega.
  reflexivity.
Qed.

Lemma weaken_closed env e t:
      TYPE [] e t ->
      TYPE env e t.
Proof.
 intros Ht. revert e t Ht.
 induction env; intros.
  assumption.
 replace e with (raise e 1 0).
  apply weakening_cons.
  apply IHenv.
  assumption.
 replace 0 with (@length Ty []).
  erewrite <- raise_closed'.
   reflexivity.
   eassumption.
  reflexivity.
Qed.
 
Lemma preservation e e' t:
      TYPE [] e t ->
      e_step e e'  ->
      TYPE [] e' t.
Proof.
 intros Ht He.
 revert t Ht.
 induction He; intros; inversion Ht; subst;
 try econstructor; try eapply IHHe; try eassumption.

 inversion H2; subst.
 eapply substitution; eassumption.

 eapply substitution.
 eapply substitution.
 eassumption.
  simpl.
  inversion H3.
  constructor.
   apply weakening_cons; assumption.
   apply weakening_cons; assumption.

   replace [t; t_num; t_num] with (insert [t;t_num] 2 t_num) by reflexivity.
   apply weakening_insert; assumption.
 inversion H3. assumption.
Qed.


Lemma progress e t:
      TYPE [] e t ->
      val e \/ exists e', e_step e e'.
Proof.
 remember [] as ENV.
 intros Ht.
 assert (@nil Ty = nil) as Hnil by reflexivity.
 induction Ht; subst;
     try (apply IHHt in Hnil);
     try destruct Hnil;
     try solve [left; constructor; auto];
     try solve [right; eexists; econstructor; auto].
  apply not_InEnv_nil in H. destruct H.
 destruct H.
 
 right. eexists. econstructor. eassumption.

 right.
  destruct IHHt1; try reflexivity.
   destruct H.
    eexists; apply e_recz.
    eexists; apply e_recs; assumption.
    inversion Ht1.
  destruct H.
   eexists; apply e_rec1; eassumption.

 right.
  destruct IHHt1; try reflexivity; destruct IHHt2; try reflexivity.
   inversion H; subst; inversion Ht1; subst.
    eexists; apply e_lam; assumption.
    destruct H0.
    eexists; apply e_ap2; eassumption.
   destruct H; eexists; apply e_ap1; eassumption.
   destruct H; eexists; apply e_ap1; eassumption.
Qed.

Definition tc := transitive_closure Exp e_step.

Lemma tc_s e e':
      tc e e' ->
      tc (s e) (s e').
Proof.
 intros Htc.
 induction Htc.
 constructor.
 eapply tc_step.
  eapply e_s. eassumption.
 assumption.
Qed.

Lemma tc_rec1 e e' ez es:
      tc e e' ->
      tc (rec e ez es) (rec e' ez es).
Proof.
 intros Htc.
 induction Htc.
 constructor.
 eapply tc_step.
  eapply e_rec1. eassumption.
 assumption.
Qed.

Lemma val_or_not e:
  val e \/ ~val e.
Proof.
 induction e;
  try destruct IHe;
  try solve [right; intros Hn; inversion Hn];
  try solve [left; constructor].
  
  left. constructor. assumption.
  right. intros Hn. inversion Hn.
  subst. apply H in H1. assumption.
Qed.


Lemma preservation_open env e e' t:
      TYPE env e t ->
      e_step e e'  ->
      TYPE env e' t.
Proof.
 intros Ht He.
 revert t env Ht.
 induction He; intros; inversion Ht; subst;
 try econstructor; try eapply IHHe; try eassumption.

 inversion H2; subst.
 eapply substitution; eassumption.

 eapply substitution.
 eapply substitution.
 eassumption.
  simpl.
  inversion H3.
  constructor.
   apply weakening_cons; assumption.
   apply weakening_cons; assumption.

   replace (t :: t_num :: t_num :: env) with (insert (t :: t_num :: env) 2 t_num)
      by (destruct env; reflexivity).
   apply weakening_insert; assumption.
 inversion H3. assumption.
Qed.


Lemma tc_preservation env e e' t:
      TYPE env e t ->
      tc e e'  ->
      TYPE env e' t.
Proof.
 intros Ht Htc.
 induction Htc.
  assumption.
  apply IHHtc.
  eapply preservation_open;
  eassumption.
Qed.

(*
Lemma total env e t:
      TYPE env e t ->
      exists e', tc e e' /\ ~exists e'', e_step e' e''.
 intros Ht.
 induction Ht.
  exists (var v). split.
   apply tc_refl.
   intros Hnot.
   destruct Hnot. inversion H0.
  exists z. split.
   apply tc_refl.
   intros Hnot.
   destruct Hnot. inversion H.

  destruct IHHt.
  destruct H.
  exists (s x). split.
   apply tc_s. assumption.
   intros Hnot.
   destruct Hnot.
   inversion H1. subst.
   apply H0.
   exists n'. assumption.

  destruct IHHt1 as [e1 H1]. destruct H1.
  destruct IHHt2 as [e2 H2]. destruct H2.
  destruct IHHt3 as [e3 H3]. destruct H3.

  assert (val e1 \/ ~val e1) as HVorN by apply val_or_not.
  destruct HVorN.

  assert (TYPE env e1 t_num) as He1num by (eapply tc_preservation; eassumption).
  apply (canon_num env e1) in He1num; try assumption.
  destruct He1num.

  eexists. split.
  eapply tc_concat.
  eapply tc_rec1. eassumption.

Lemma total env e t:
      TYPE env e t ->
      exists e', tc e e' /\ (val e' \/ exists v' t', e' = var v' /\ InEnv v' t' env).
Proof.
 intros Ht.
 induction Ht.
  exists (var v). split.
   apply tc_refl.
   right. exists v, t. split; try assumption; reflexivity.

  exists z. split.
   apply tc_refl.
   left. constructor.

  destruct IHHt.
  destruct H.
  destruct H0.
   exists (s x). split.
    eapply tc_s. assumption.
    left. constructor. assumption.

   destruct H0. destruct H0.
   destruct H0. subst.
   

 split.

 remember [] as ENV.
 induction Ht; subst.
      apply not_InEnv_nil in H. destruct H.
     exists z. simpl. split; constructor.
    destruct IHHt. reflexivity. destruct H.
    exists (s x).
    simpl. split. eapply tc_s. assumption. constructor. assumption.
   destruct IHHt1. reflexivity.
   destruct IHHt2. reflexivity.
   
 
 
*)
(*
Lemma total e t:
      TYPE [] e t ->
      exists e', tc e e' /\ val e'.
Proof.
 intros Ht.
 remember [] as ENV.
 induction Ht; subst.
  apply not_InEnv_nil in H. destruct H.
 eexists; repeat constructor.

 destruct IHHt. reflexivity. destruct H.
 eexists. split.
  eapply tc_s. eassumption.
  apply v_s. assumption.

 destruct IHHt1. reflexivity. destruct H as [tcn vn].
 destruct IHHt2. reflexivity. destruct H as [tcez vez].

 eexists. split.
  eapply tc_concat.
   eapply tc_rec1. eassumption.
 
Qed.

*)