(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2004                                *)
(*                              LaBRI                                   *)
(************************************************************************)


Set Implicit Arguments.
Require Export basics.

Section defs.

Variables 
           I (* composition modes *)
           J (* unary modes *) 
           A
           W
           : Set.


Variables  (decI : eqdec I)
           (decJ : eqdec J).
           

Variable R:(extension I J).

Inductive gentzen : (context I J A W) -> (Form I J A) -> Set :=
   | Ax : forall r F, gentzen (res r F) F
   | RSlash :
      forall (Gamma:context I J A W) (F G:Form I J A) (i:I) (n:nat),
        gentzen (Comma i Gamma (res (hyp  n) G)) F ->
        gentzen Gamma (Slash i F G)
   | RBack :
      forall (Gamma:context I J A W) (F G:Form I J A) (i:I) n,
        gentzen (Comma i (res (hyp n) G) Gamma) F ->
        gentzen Gamma (Backslash i G F)
   | RDot :
       forall (Gamma Delta:context I J A W) (F G:Form I J A) (i:I),
        gentzen Gamma F ->
        gentzen Delta G ->
        gentzen (Comma i Gamma Delta) (Dot i F G)
       
   | RDiam:
        forall (Gamma:context I J A W) (F:Form I J A) (j:J),
        gentzen Gamma F ->
        gentzen (TDiamond j Gamma) (Diamond j F)
   | RBox :
       forall (Gamma:context I J A W) (F:Form I J A) (i:J),
        gentzen (TDiamond i Gamma) F ->
        gentzen Gamma (Box i F)
   | LSlash :
       forall (Delta Gamma Gamma': context I J A W) (F B C:Form I J A) (i:I) (n:nat) r1,
           replace  (res (hyp  n) F) (Comma i (res r1 (Slash i F B)) Delta) Gamma Gamma' ->
         gentzen Delta B ->
         gentzen Gamma C -> gentzen Gamma' C
   | LBack :
       forall (Delta Gamma Gamma': context I J A W) (F B C:Form I J A) (i:I) (n:nat) r1,
         replace (res (hyp  n) F) (Comma i Delta (res r1 (Backslash i B F)))  Gamma Gamma' ->
         gentzen Delta B ->
         gentzen Gamma C -> gentzen Gamma' C
   | LDot :
       forall (Gamma Gamma':context I J A W) (F B C:Form I J A) (i:I)(n1 n2:nat) r1,
         replace 
           (Comma i (res (hyp n1) F) (res (hyp n2) B))
           (res r1 (Dot i F B)) Gamma Gamma' ->
         gentzen Gamma C -> gentzen Gamma' C
   | LDiam :
       forall (Gamma Gamma':context I J A W) (F B:Form I J A) (j:J)(n:nat)r1,
         replace (TDiamond j (res (hyp  n) F)) (res r1  (Diamond j F)) Gamma Gamma' ->
         gentzen Gamma B -> gentzen Gamma' B
   | LBox :
       forall (Gamma Gamma':context I J A W) (F B:Form I J A) (j:J)(n:nat)r1,
         replace  (res (hyp n) F)(TDiamond j (res r1 (Box j F))) Gamma Gamma'->
         gentzen Gamma B -> gentzen Gamma' B
   | CutRule :
       forall (Delta Gamma Gamma':context I J A W) (B C:Form I J A)(n:nat),
         replace (res (hyp  n) B) Delta Gamma Gamma'->
         gentzen Delta B ->
         gentzen Gamma C -> gentzen Gamma' C
   | StructR :
       forall (Gamma Gamma' T1 T2:context I J A W) (F:Form I J A) Ru,
        in_extension Ru R ->
        struct_replace decI decJ Ru T1 T2 Gamma Gamma'  ->
        gentzen Gamma' F -> gentzen Gamma F. 

End defs.