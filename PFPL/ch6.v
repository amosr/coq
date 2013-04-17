Require Import Env.

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
	| ty_lambda (def body : Exp) (ty tbody : Ty) :
		TYPE (ty :: env) body tbody ->
		TYPE env (lambda ty body) (t_arrow ty tbody)
	| ty_app (f x : Exp) (t1 t2 : Ty) :
		TYPE env f (t_arrow t1 t2) ->
		TYPE env x t1 ->
		TYPE env (app f x) t2.

