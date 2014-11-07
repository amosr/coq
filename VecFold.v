
Inductive vec (a : Type) : nat -> Type :=
 | Nil  :                           vec a 0
 | Cons : forall n, a -> vec a n -> vec a (S n).

Fixpoint fold {a : Type} (b : forall m, vec a m -> Type)
              (z : b 0 (Nil a)) (s : forall m v val, b m v -> a -> b (S m) (Cons a m val v))
              {n : nat} (v : vec a n)
              :=
 match v with
 | Nil => z
 | Cons m l ls => s m ls l (fold b z s ls) l
 end.


Definition map {a b : Type} {n : nat}
               (f : a -> b)
               (v : vec a n) : vec b n
 :=
 fold (fun m v => vec b m)
   (Nil b) (fun m v val rest val' => Cons b m (f val') rest)
   v.

Inductive exT
 {a : Type} (b : a -> Type)
 :=
 exI : forall x : a, b x -> exT b.

Definition filter {a : Type} {n : nat}
                  (p : a -> bool)
                  (v : vec a n)
                  : exT (fun n' => vec a n')
 :=
 fold (fun m v => exT (fun n' => vec a n'))
  (exI _ 0 (Nil _))
  (fun m v val rest val' =>
    if   p val'
    then match rest with
         exI filt_len vo => 
           exI _ (S filt_len) (Cons _ _ val' vo)
         end
    else rest)
  v
.