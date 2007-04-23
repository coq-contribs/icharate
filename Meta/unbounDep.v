(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2004                                *)
(*                              LaBRI                                   *)
(************************************************************************)


Set Implicit Arguments.

Require Export derivedRulesNatDed.

Section unboundDepend.
Variables I J A W:Set.
Variable eqdecI:(eqdec I).
Variable eqdecJ :(eqdec J).
Variable ext:(extension I J).

Fixpoint addToEnd (T1 T2:context I J A W)(i:I){struct T1}:context I J A W:=
match T1 with 
|(Comma j Tr1 Tr2)=>match (eqdecI i j) with 
                    |left _=> (Comma i Tr1 (addToEnd Tr2 T2 i))
                    |right _=>(Comma i T1 T2)
                    end
|others => (Comma i T1 T2)
end.

Definition MA2DiamRep:forall(T1 T2:context I J A W)(i:I)(j:J),
                         replaceNTimes eqdecI eqdecJ (MA2Diam i j)
                                       (Comma i T1 (TDiamond j T2)) 
                                       (addToEnd T1 (TDiamond j T2) i).

 intro T1; elim T1; intros.
 simpl in |- *; constructor.
 simpl in |- *; elim (eqdecI i0 i).
 intro;subst.
 econstructor.
 econstructor.   
 eapply MA2Diam_rw.
 apply MonoLeftNRu.
 auto.
 intro; constructor.
 simpl in |- *; constructor.
Defined.


Definition unboundDepend:forall(i:I)(j:J) (T1 T2:context I J A W)
                              (C:Form I J A),
                             in_extension (MA2Diam i j) ext->
                             natded eqdecI eqdecJ ext (addToEnd T1 (TDiamond j T2) i) C ->
                             natded eqdecI eqdecJ ext (Comma i T1 (TDiamond j T2)) C.
 intros.
 eapply natdedNRep.
 eauto.
 apply MA2DiamRep.
 auto.
Defined.

Definition unboundDep:forall(i:I)(j:J) (T1:context I J A W)
                              (B C:Form I J A)(r:resource W)n1,
                             in_extension (MA2Diam i j) ext->
                             natded eqdecI eqdecJ ext 
                                  (addToEnd T1 (TDiamond j (res (hyp n1) B)) i) C ->
                             natded eqdecI eqdecJ ext (Comma i T1 (res r (Diamond j B))) C.
intros.
eapply DiamE .
econstructor 3.
constructor 1.
constructor 1.
apply unboundDepend;eauto.
Defined.

End unboundDepend.

Ltac struct_dep n:=apply unboundDep with n;[inExt|simpl].