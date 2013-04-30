Require Export Omega.
Require Export List.
Export ListNotations.

Require Export Coq.Arith.Bool_nat.

Definition Env A := list A.
Definition Var   := nat.

Definition getEnv {A} (env : Env A) n := nth_error env n.
Definition InEnv {A} v t (env : Env A) := getEnv env v = Some t.

Hint Unfold Env.
Hint Unfold getEnv.
Hint Unfold InEnv.

Fixpoint insert {A} (env : Env A) v tv :=
 match env,v with
 | _, 0          => tv :: env
 | [],      S v' => tv :: env
 | (x::xs), S v' => x  :: insert xs v' tv
 end.

Lemma insert_0 {A} (env : Env A) t :
      insert env 0 t = t :: env.
Proof.
 destruct env; auto.
Qed.


Lemma InEnv_app_end {A}
  (env env' : Env A) t (v : Var) :
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


Lemma InEnv_app_start {A}
  (env env' : Env A) t (v : Var) :
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


Lemma get_insert_lt {A} (env : Env A) i v ti tv :
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

Lemma get_insert_ge {A} (env : Env A) i v ti tv :
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

Lemma uninsert {A} (t1 : A) e v t2:
      insert (t1::e) (S v) t2 =
      t1 :: (insert e v t2).
Proof.
 auto.
Qed.


Lemma InEnv_insert {A} (env : Env A) v t t':
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


Lemma minus_n_1 v:
      S v - 1 = v.
 simpl. rewrite minus_n_O. reflexivity.
Qed.



Lemma insert_minus1 {A} (env : Env A) i v ti tv :
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

Lemma insert_minus {A} (env : Env A) i v ti tv :
      InEnv i ti (insert env v tv) ->
      i > v ->
      InEnv (i-1) ti env.
Proof.
 intros. destruct i. omega.
 rewrite minus_n_1.
 eapply insert_minus1;
 eassumption.
Qed.


Lemma insert_pre {A} (env : Env A) i v ti tv :
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




Lemma InEnv_insert_n {A} (env : Env A) v t:
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


Lemma not_InEnv_nil {A} v (t : A):
      InEnv v t [] -> False.
Proof.
 unfold InEnv.
 intros.
 destruct v; inversion H.
Qed.


Lemma InEnv__length {A} v (t : A) env:
      InEnv v t env ->
      v < length env.
Proof.
 unfold InEnv.
 intros Hie.
 revert v t Hie.
 induction env; intros.
  destruct v; inversion Hie.
 destruct v; simpl in *.
  omega.
 apply IHenv in Hie.
  omega.
Qed. 

Definition raise' (a b v : nat) :=
 if   ge_dec v b
 then a + v
 else v.

Definition subst' {A} (v v' : Var) (f : Var -> A) (r : A) :=
 if   eq_nat_dec v v'
 then r
 else if lt_dec v v'
 then f (v' - 1)
 else f v'.


Lemma subst_cases {E} x v {f : Var -> E} (e : E) P:
      (x = v -> P e)               ->
      (x < v -> v <> 0 -> P (f (v-1))) ->
      (x > v -> P (f v)) ->
      P (subst' x v f e).
Proof.
 intros.
 unfold subst'.
 destruct (eq_nat_dec x v).
  apply X. assumption.
 destruct (lt_dec x v).
  apply X0. assumption.
  omega.
 
 apply X1. omega.
Qed.
  



Lemma raise_cases inc vi v P:
      (v >= vi -> P (inc+v)) ->
      (v <  vi -> P (v))     ->
      P (raise' inc vi v).
Proof.
 intros.
 unfold raise'.
 destruct (ge_dec v vi); auto.
  apply X0. omega.
Qed.

