
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


Lemma tc_concat {E S} e1 e2 e3:
      transitive_closure E S e1 e2 ->
      transitive_closure E S e2 e3 ->
      transitive_closure E S e1 e3.
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

