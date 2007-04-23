(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2004                                *)
(*                              LaBRI                                   *)
(************************************************************************)

(* derived rule for medial extraction in natural deduction system *)
Set Implicit Arguments.
Require Export tacticsDed.
Require Export struct_ex.

Section medialMeta.
Variables I
          J
          A
          W:Set.
Variable eqdecI:eqdec I.
Variable eqdecJ :eqdec J.
Variable ext:extension I J.
Variable i:I.
Variable j:J.
Hypothesis MA_ij: in_extension (MA2Diam i j) ext.
Hypothesis MP_ij: in_extension (MP1Diam i j) ext.

(*  D ,i ((D \i B) /i C ,i ((D \i B) \i (D \i B))) |- B /i <>j[]j C *)
Definition medialExtraction: forall 
                           (D B C:Form I J A)(r1 r2 r3:resource W), 
                            (natded eqdecI eqdecJ ext (Comma i (res r1 D)
                                                              (Comma i (res r2 (Slash i (Backslash i D B) C))
                                                                       (res r3 (Backslash i (Backslash i D B)
                                                                                            (Backslash i D B))))) 
                                                      (Slash i B (Diamond j (Box j C)))).             

 intros.
 slashI  0.
 elimDiam 1.
 eapply StructRule with (Ru:=(MA2Diam i j)).
 auto.
 here.
 autorewrite with ctl_db;auto. 
 eapply StructRule.
 eexact MP_ij.  
 constructor 3.
 constructor 1; autorewrite with ctl_db;auto. 
 eapply BackE; [ constructor 1 | idtac ].    
 eapply BackE; [ idtac | constructor 1 ].    
 eapply SlashE.
 constructor 1.   
 eapply BoxE; constructor 1.
Defined.


End  medialMeta.
Ltac extract_med:=apply medialExtraction;inExt.
