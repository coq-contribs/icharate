Require Export lambda_coq.
Require Export final_sem.

Set Implicit Arguments.

Section to_coq.
Variable W:Set.
Parameter semW:forall (w:W)(i:nat)(ty:semType),trans_type ty. 

Definition deep_to_shallow(ct:cst W): trans_type (type_cst ct).
intro ct; elim ct.
intro l;elim l.
simpl.
intros P Q;exact (P/\Q).
simpl.
intro f.
exact (exists x:E, (f x)).
simpl;intro f.
exact ((exists x:E, (f x)) /\ (forall (x y:E), f x->f y-> x=y)). 
simpl;intro f.
exact (forall x, f x).
simpl;intros P Q;exact (P \/ Q).
simpl;intros P Q;exact (P -> Q).
simpl.
intros w i ty.
exact (semW w i ty). 
Defined.


End to_coq.

 Definition pretty_printer(W:Set) (l:lambda_terms (cst W))(ty:semType)
(p:isWellTyped (type_cst (W:=W)) nil l ty) (q:no_hyps_inside l) :(trans_type ty):=
(trans_lamb (getSemTypeX:= type_cst (W:=W)) (deep_to_shallow (W:=W)) p q (nil_trans)).
  

(* the pretty printer will be refined in a future release *)