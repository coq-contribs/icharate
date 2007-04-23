(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2004                                *)
(*                              LaBRI                                   *)
(************************************************************************)
Set Implicit Arguments.
Require Export struct_ex.
Require Export derivedRulesNatDed.

Section cross_dep.

Variables  I (* composition modes *)
           J (* unary modes *) 
           A (* atomic formulaes*) 
           W (* set of terminals: words *)
           : Set.


 Variables (eqdecI :eqdec I)
           (eqdecJ :eqdec J)
           (eqdecA :eqdec A)
           (eqdecW :eqdec W).
 Variable R : extension I J.

Fixpoint distDiam (i0:I)(j0:J)(ct:context I J A W){struct ct}:context I J A W :=
match ct with
|Comma i t1 t2=> match (eqdecI i i0) with 
                 |left _=> Comma i (distDiam i0 j0 t1) (distDiam i0 j0 t2)
                 |right _ => (TDiamond j0 ct)
               end
|others =>  (TDiamond j0 ct)
end.

Fixpoint transformCont (ct:context I J A W)(i0 i1:I)(j0 j1:J){struct ct}:context I J A W:=
match ct with
 |Comma i t1 t2 =>match (eqdecI i i1) with 
                 |left _=> (Comma i t1 (transformCont t2 i0 i1 j0 j1))
                 |right _ =>match (eqdecI i i0)with
                            |left _ => (Comma i (distDiam i0 j0 t1) (distDiam i0 j0 t2))
                            |right _ => (TDiamond j1 ct)
                  
                             end
                end
| res _ _=> (TDiamond j0 ct)
|others => (TDiamond j1 ct)
end.




Definition repDistribute:forall(i0:I)(j0 :J)(Gamma:context I J A W) ,
               in_extension (KDiam i0 j0) R ->
               replaceNTimesExt eqdecI eqdecJ R (TDiamond j0 Gamma) (distDiam i0 j0 Gamma).
 intros.
 elim Gamma; intros.
 constructor 1.
 simpl in |- *.
 case (eqdecI i i0).
 intro; subst.
 eapply replNPermut.
 eexact H.
 eapply replExtMono;eauto.
 econstructor.
 constructor 1.
 apply KDiam_rw.
 constructor.
 intro.
 constructor 1.       
 simpl in |- *.
 constructor.
Defined.

Definition repTransform:forall(i0 i1:I)(j0 j1:J)(Gamma:context I J A W) ,
              in_extension (K2Diam i1 j1) R ->
              in_extension (incDiam I j1 j0) R ->
              in_extension (KDiam i0 j0) R ->
              replaceNTimesExt eqdecI eqdecJ R (TDiamond j1 Gamma) (transformCont Gamma i0 i1 j0 j1).

 intros.
 elim Gamma; intros.
 econstructor 2.
 eexact H0.
 constructor 1.
 econstructor 2.
 constructor 1.       
 apply incDiam_rw.
 constructor.
 simpl in |- *.
 case (eqdecI i i1).
 intros.
 subst.
 eapply replNPermut.
 eexact H.
 eapply replaceExtMonoLeft.
 eauto.
 econstructor.
 constructor.
 apply K2Diam_rw.
 constructor.
 intro.
 case (eqdecI i i0).
 intro.
 subst.
 assert (distDiam i0 j0 (Comma i0 c c0)=Comma i0 (distDiam i0 j0 c) (distDiam i0 j0 c0)).
 simpl.
 case (eqdecI i0 i0).
 auto.
 intro H4; elim H4.
 auto.
 rewrite <- H4.
 eapply replNPermut.
 eexact H0. 
 eapply repDistribute.
 auto.
 econstructor.
 constructor.
 apply incDiam_rw.
 constructor.
 intro.
 constructor 1.
 simpl.
 constructor 1.
Defined.


Definition cross_depend:forall (i0 i1:I)(j0 j1:J)(B:Form I J A)(Gamma:context I J A W),
                          in_extension (K2Diam i1 j1) R ->
                          in_extension (incDiam I j1 j0) R ->
                          in_extension (KDiam i0 j0) R ->
                          natded eqdecI eqdecJ R (transformCont Gamma i0 i1 j0 j1) B ->
                          natded eqdecI eqdecJ R (TDiamond j1 Gamma) B.
intros.
eapply repExtnatDed.
apply repTransform;eauto.
auto.
Defined.
                          

End cross_dep.