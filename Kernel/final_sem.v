(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2004 -2006                                *)
(*                              LaBRI                                   *)
(************************************************************************)


Require Export derivSem.
Set Implicit Arguments.

Section lambda_morphism.

Variables X Y:Set.
Variable typeX:X->semType.
Variable typeY:Y->semType.
Variable subst_X_by_Y:X->lambda_terms Y.

Fixpoint translate(lTerm1:lambda_terms X):lambda_terms Y:=
match lTerm1 with 
| num n => (num Y n)
| ress r => (subst_X_by_Y r)
| hyps n ty=>hyps Y n ty
| appl l1 l2 => appl (translate l1) (translate l2)
| abs t1 l => abs t1 (translate l) 
| twoL  l1 l2 =>  twoL (translate l1)(translate l2)
| pi1  l => pi1 (translate l)
| pi2 l =>  pi2 (translate l) 
| box  l=> box (translate l)
| debox  l => debox (translate l)
| diam l =>  diam (translate l) 
| dediam  l=>  dediam (translate l) 
end.

Definition same_type :=forall (x:X),
                       isWellTyped typeY nil (subst_X_by_Y x) (typeX x).
                     

Lemma same_type_after_subst:forall (l1:lambda_terms X) env t1,
                            isWellTyped typeX env l1 t1->
                            same_type->
                            isWellTyped typeY env (translate l1) t1.
Proof.
 intro l1; elim l1; intros.
 inversion H.
 simpl in |- *.
 constructor; auto.
 unfold same_type in H0; simpl in |- *.
 inversion H.
 change env with (nil ++ env) in |- *.
 apply wellTypedAppEnv; auto.
 inversion H; simpl in |- *; constructor; auto.
 simpl in |- *; inversion H1; econstructor; eauto.
 simpl in |- *; inversion H0; constructor; auto.
 simpl in |- *; inversion H1; constructor; auto.
 simpl in |- *; inversion H0; econstructor; eauto.
 simpl in |- *; inversion H0; econstructor; eauto.
 simpl in |- *; inversion H0; constructor; auto.
 simpl in |- *; inversion H0; constructor; auto.
 simpl in |- *; inversion H0; constructor; auto.
 simpl in |- *; inversion H0; constructor; auto.
Qed.

End lambda_morphism.




Section semantic.
Variables I J A W:Set.

Variable lexi:W->list ((Form I J A)*(option (lambda_terms logic_cst))).
Variable map:A->semType.

Inductive cst:Set:=
|formal:logic_cst->cst
|normal: W->nat->semType->cst.

Definition trans:lambda_terms logic_cst->lambda_terms cst
:=translate (fun (lc:logic_cst)=>(ress (formal lc))).

Definition word_to_lambda:word_type W->lambda_terms cst.
intro wt; case wt.
intros n w1 f1.
case (nth_error (lexi w1) n).
induction 1.
case b.
intro l;exact (trans l).
exact (ress(normal w1 n f1)).
exact (ress(normal w1 n f1)).
Defined.


(* well typeness of final semantics *)

Definition type_cst(ct:cst):semType:=
match ct with
|formal lcst=>setTypeLog lcst
|normal w n  f=> f
end.

(* to be continued ...*)
End semantic.

(* compute the whole semantics *)
Definition whole_sem(gr: syn_sem_gram)(l:list _)
(f:Form _ _ _)(red:deriveTo gr l f):=
translate (word_to_lambda (gr.(lexic)).(lex)) 
(getSemantic red).


(* the whole semantics is well typed *)
Lemma sem_wt:forall (gr: syn_sem_gram)(l:list _)
(f:Form _ _ _)(red:deriveTo gr l f),
 isWellTyped (type_cst (W:=((gr.(lexic)).(W))))  nil
 (whole_sem red) (mapExt (gr.(lexic)).(map) f). 
unfold whole_sem;intros.
eapply same_type_after_subst.
apply wellTyped_deriv_sem.
unfold same_type.
intro wt;case wt.
simpl.
Admitted.
