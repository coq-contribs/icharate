(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                              LaBRI                                   *)
(************************************************************************)

Require Export semLex.

Set Implicit Arguments.

Section semantic.
Variables I J A W:Set.
Variables (eqDecI :eqdec I)
               (eqDecJ :eqdec J).

Variable ext:extension I J.
Variable map:A -> semType.


Inductive word_type:Set:=
|wt:nat->W->semType->word_type.

Definition getTypeWT (wot:word_type):semType:=
match wot with
|wt _ _ ty=>  ty
end.

(* calculate a lambda term corresponding to each linguistic resource*)
Definition free_lambda(r:resource W)(F:Form I J A):(lambda_terms word_type):=
match r with 
|(word n w)=>(ress (wt n w (mapExt map F)))
|hyp n => (hyps _ n (mapExt map F))
end.

Fixpoint semanticTerm(Gamma:context I J A W)(F:Form I J A)
           (der:(natded eqDecI eqDecJ ext Gamma F)) {struct der}:
(lambda_terms word_type):=
match der with 
| Wd r F => free_lambda r F
| SlashI Gamma F G  i n der1 => lambdaAbs (semanticTerm der1) n
           (mapExt map G)
| BackI Gamma F G i n der1   => lambdaAbs (semanticTerm der1) n
           (mapExt map G)
| DotI Gamma Delta F G i der1 der2 =>
       twoL (semanticTerm der1) (semanticTerm  der2)
| BoxI Gamma F i der1 => box (semanticTerm der1)
| DiamI Gamma F i  der1 => diam (semanticTerm  der1)
| SlashE Gamma Delta F G i  der1 der2 =>
        appl (semanticTerm  der1)(semanticTerm  der2)
| BackE Gamma Delta F G i der1 der2 =>
         appl (semanticTerm der2)(semanticTerm der1)
| DotE Gamma Gamma' Delta F G H i n p  _ der1 der2 =>
     (lambSub (lambSub  (semanticTerm der2) 
             (pi1 (semanticTerm der1)) n (mapExt map F)) 
             (pi2 (semanticTerm der1)) p (mapExt map G))
|BoxE Gamma F i der1 =>debox  (semanticTerm der1)
| DiamE Gamma Gamma' Delta F G  i n _ der1 der2 =>
     lambSub  (semanticTerm der2) (dediam (semanticTerm der1))
                n (mapExt map F)
| StructRule Gamma Gamma' T1 T2 F _ _ _ der1 => (semanticTerm  der1)
end.



(* theorem which states that all lambda terms returned by the function above
  are well formed *)
Theorem semWellDefined: forall (Gamma:context I J A W)(F:Form I J A)
                               (der:(natded eqDecI eqDecJ ext Gamma F)), 
                             isWellFormed (semanticTerm der).
 intros.
 elim der; unfold isWellFormed in |- *; 
 simpl in |- *; intros; auto || (try tauto).
 case r; simpl in |- *; auto.
 apply isWellFormedBindN;auto.
 apply isWellFormedBindN; auto.
 apply isWellFormedSubst; auto.
 apply isWellFormedSubst; auto.
 apply isWellFormedSubst; auto.
Qed.

(* theorem which states that the lambda term associated to a derivation Gamma => F is well
typed, moreover it's type is (mapExt F)  *)
Theorem wellTypedSem :forall (Gamma:context I J A W)(F:Form I J A)
                         (der:(natded eqDecI eqDecJ ext Gamma F)),
                          isWellTyped getTypeWT nil (semanticTerm der)(mapExt map F).
Proof.
 intros Gamma F der; elim der; intros.
 simpl in |- *.
 case r;simpl;intros.
 replace (mapExt map F0) with (getTypeWT (wt n w (mapExt map F0))).
 constructor.
 auto.
 constructor.
 simpl in |- *.
 apply wellTypedAbs.
 auto.
 simpl in |- *.
 apply wellTypedAbs; auto.
 simpl in |- *; constructor; auto.
 simpl in |- *; constructor; auto.
 simpl in |- *; constructor; auto.
 simpl in H; simpl in |- *; econstructor; eauto.
 simpl in |- *.
 simpl in H0; econstructor; eauto.
 simpl in |- *.
 apply wellTypedSubst.
 simpl in H0; econstructor; eauto.
 apply wellTypedSubst.
 simpl in H0; econstructor; eauto.
 auto.
 simpl in |- *.
 apply wellTypedSubst.
 simpl in H; constructor; auto.
 auto.
 simpl in |- *; simpl in H; constructor; auto.
 simpl in |- *; auto.
Defined.

 
End semantic.

Definition getSemantic(gr: syn_sem_gram)(l:list _)
(f:Form _ _ _)(red:deriveTo gr l f):=
match red with
| reduce1 _ natD _ =>
 semanticTerm (gr.(lexic)).(map) natD
end.

Lemma wellTyped_deriv_sem:forall (gr: syn_sem_gram)(l:list _)
(f:Form _ _ _)(red:deriveTo gr l f),
 isWellTyped  (getTypeWT (W:=(gr.(lexic)).(W))) nil (getSemantic red) 
 (mapExt (gr.(lexic)).(map) f).
intros gr l f red;case red.
simpl.
intros;apply wellTypedSem.
Defined.
