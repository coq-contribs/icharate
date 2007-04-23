(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2004                                *)
(*                              LaBRI                                   *)
(************************************************************************)


Require Export sequent.
Require Export derivedRulesNatDed.

Set Implicit Arguments.
Section natDedSeq.
Variables I J A W :Set.
Variable eqDecI: (eqdec I).
Variable eqDecJ :(eqdec J).



Definition replaceNatDed :
  forall (Gamma Gamma' Delta Delta':context I J A W)(ext :extension I J),
    replace Delta Delta' Gamma Gamma' ->
    natded eqDecI eqDecJ  ext Delta' (contextToForm  Delta) ->
    natded eqDecI eqDecJ  ext Gamma' (contextToForm  Gamma). 
 intros Gamma Gamma' Delta Delta' ext H; elim H.
 intros.
 assumption.
 intros.
 simpl.
 apply DotI.
 auto.
 apply axiomGen.
 intros.
 simpl.
 apply DotI.
 apply axiomGen.
 auto.
 intros.
 simpl.
 apply DiamI; auto.
Defined.                                                                                             


(* definition which does the transformation from sequent calculus 
to natural deduction*)
Definition seqToNatded :
  forall (T1:context I J A W) (C:Form I J A)(ext:extension I J),
    weak_sahlqvist_ext ext->
    gentzen eqDecI eqDecJ ext T1 C ->
    natded eqDecI eqDecJ  ext T1 C.
 intros T1 C ext H0 H; elim H.
 constructor 1.
 intros; econstructor 2; eauto.
 intros; econstructor 3; eauto.
 intros; econstructor 4; eauto.
 intros; econstructor 5; eauto.
 intros; econstructor 6; eauto.
 intros;eapply cut_rule1.
 auto. 
 2:eauto.
 eapply SlashE; [ constructor 1 | auto ].
 auto.
 intros; eapply cut_rule1.
 auto. 
 2:eauto.
 eapply BackE; [ eauto | constructor 1 ].    
 auto.
 intros;eapply DotE.
 eauto. 
 constructor 1. 
 auto.
 intros;eapply DiamE.
 eauto. 
 constructor 1.
 auto.
 intros;eapply cut_rule1.
 auto.
 2:eauto.
 apply BoxE; constructor 1.
 auto.
 intros.
 eapply cut_rule1.
 auto.
 2:eauto.
 auto.
 auto.
 intros.
 eapply StructRule; eauto.
Defined.


(* from natural deduction to sequent calculus *)
Definition natDedToSeq:
  forall (Omega:context I J A W) (C:Form I J A)(ext :extension I J),
    natded eqDecI eqDecJ  ext Omega C ->
    gentzen eqDecI eqDecJ ext  Omega C.
 intros Omega C ext H; elim H.
 constructor 1.
 intros.
 eapply RSlash;eauto.
 intros.
 eapply RBack;eauto.
 intros.
 eapply RDot; eauto.
 intros.
 eapply RDiam; eauto.
 intros;eapply RBox; eauto.
 intros.
 eapply CutRule with (B:= (Dot i (Slash i F G) G)) (n:=0).
 constructor 1.  
 eapply RDot; auto. 
 eapply LDot with (n1 := 1) (n2 := 3).
 constructor 1.  
 eapply LSlash with (n := 2); constructor 1.
 intros.
 eapply CutRule with (n := 0) (B := (Dot i G (Backslash i G F))).
 constructor 1.
 eapply RDot; auto. 
 eapply LDot with (n1 := 1) (n2 := 2).
 constructor 1.  
 eapply LBack with (n := 3); constructor 1.
 intros.
 elim (replaceProp (res (hyp 0) (Dot i F G)) r).
 intros Gamma1 H3.
 elim H3; clear H3; intros H3 H4.
 eapply CutRule with (n := 0).
 eauto. 
 auto. 
 eapply LDot; eauto.
 intros.
 elim (replaceProp (res (hyp  0) (Diamond j F)) r).
 intros Gamma1 H2; elim H2; clear H2; intros H2 H3.
 eapply CutRule with (n := 0).
 eauto. 
 eauto. 
 eapply LDiam; eauto.
 intros.
 eapply CutRule with (n := 0) (B := (Box j F)).
 constructor 4.
 constructor 1.
 auto.   
 eapply LBox with (n := 1);constructor 1.
 intros;eapply StructR; eauto.
Defined.

End natDedSeq.