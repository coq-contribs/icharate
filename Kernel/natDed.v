(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2004                                *)
(*                              LaBRI                                   *)
(************************************************************************)



Set Implicit Arguments.
Require Export basics.

Section Main.
 Variables 
           I (* composition modes *)
           J (* unary modes *) 
           A (* atomic formulaes*) 
           W (* set of terminals: words *)
           : Set.


 Variables (eqdecI :eqdec I)
           (eqdecJ :eqdec J).
         
 Variable R : extension I J.


(* natural deduction *)
Inductive natded : context I J A W -> Form I J A -> Set :=
  | Wd  : forall r  F, natded  (res r F) F
  | SlashI : 
      forall (Gamma:context I J  A W) (F G:Form I J A) (i:I) n,
        natded (Comma i Gamma (res (hyp n) G)) F ->
        natded Gamma (Slash i F G)
  | BackI :
      forall (Gamma:context I J A W) (F G:Form I J A) (i:I) n,
        natded (Comma i (res (hyp n) G) Gamma) F ->
        natded Gamma (Backslash i G F)
  | DotI :
      forall (Gamma Delta:context I J A W) (F G:Form I J A) (i:I),
        natded Gamma F ->
        natded Delta G ->
        natded (Comma i Gamma Delta) (Dot i F G)
  | DiamI :
      forall (Gamma:context I J A W) (F:Form I J A) (j:J),
        natded Gamma F ->
        natded (TDiamond j Gamma) (Diamond j F)
  | BoxI :
      forall (Gamma:context I J A W) (F:Form I J A) (i:J),
        natded (TDiamond i Gamma) F ->
        natded Gamma (Box i F)
  | SlashE :
      forall (Gamma Delta:context I J A W) (F G:Form I J A) (i:I),
        natded Gamma (Slash i F G) ->
        natded Delta G ->
         natded (Comma i Gamma Delta) F
  | BackE :
      forall (Gamma Delta:context I J A W) (F G:Form I J A) (i:I),
        natded Gamma G ->
        natded Delta (Backslash i G F) ->
        natded (Comma i Gamma Delta) F
  | DotE :
      forall (Gamma Gamma': context I J A W)(Delta:context I J A W) 
             (F G H:Form I J A) (i:I) n p,
          replace 
          (Comma i (res (hyp  n) F) (res (hyp  p) G)) Delta Gamma Gamma' ->
        natded Delta (Dot i F G) ->
        natded Gamma H -> natded Gamma' H
  | DiamE :
      forall (Gamma Gamma' Delta:context I J A W) (F G:Form I J A) (j:J) n,
        replace  (TDiamond j (res (hyp  n) F)) Delta Gamma Gamma' ->
        natded Delta (Diamond j F) ->
        natded Gamma G -> natded Gamma' G
  | BoxE :
      forall (Gamma:context I J A W) (F:Form I J A) (j:J),
        natded Gamma (Box j F) ->
        natded (TDiamond j Gamma) F
  | StructRule :
      forall (Gamma Gamma' T1 T2:context I J A W) (F:Form I J A) Ru,
        in_extension Ru R ->
        struct_replace  eqdecI eqdecJ Ru T1 T2 Gamma Gamma'  ->
        natded Gamma' F -> natded Gamma F. 


(* A hideous patch ! *)
Definition XStructRule : forall (Gamma Gamma' T1 T2:context I J A W) (F:Form I J A) Ru,
        struct_replace eqdecI eqdecJ  Ru  T1 T2 Gamma Gamma'  ->
        in_extension Ru R ->
        natded Gamma' F ->
        natded Gamma F. 
 intros; eapply StructRule;eauto.
Defined.

(* derived rules using contexts with one hole *)
Definition Structrule' : 
  forall (ZGamma : zcontext I J A W)(T1 T2:context I J A W) (F:Form I J A) Ru,
        in_extension Ru R -> 
        apply_rule Ru eqdecI eqdecJ  T2 = Some T1 ->
        natded  (zfill ZGamma T1) F ->
        natded  (zfill ZGamma T2) F. 
 intros.
 eapply StructRule.
 eexact H.
 eapply struct_replace_as_zfill.
 eexact H0.
 trivial.
Defined.

Definition XStructrule' : 
  forall (ZGamma : zcontext I J A W)(T1 T2:context I J A W) (F:Form I J A) Ru,
        apply_rule Ru eqdecI eqdecJ T2 = Some T1 ->
        in_extension Ru R -> 
        natded (zfill ZGamma T1) F ->
        natded (zfill ZGamma T2) F. 
intros;eapply Structrule';eauto.
Defined.


Definition DotE' :  forall (ZGamma : zcontext I J A W)(Delta:context I J A W) 
             (F G H:Form I J A) (i:I) n p,
        natded Delta (Dot i F G) ->
        natded (zfill ZGamma  (Comma i (res (hyp n) F) (res (hyp  p) G))) H ->
        natded (zfill ZGamma Delta) H.
 intros.
 eapply DotE;eauto with ctl_db.
Defined.

Definition DiamondE' :
      forall (ZGamma : zcontext I J A W)(Delta:context I J A W) (F G:Form I J A) (j:J) n,
        natded Delta (Diamond j F) ->
        natded (zfill ZGamma (TDiamond j (res (hyp  n) F))) G -> 
        natded (zfill ZGamma Delta) G.
 intros; eapply DiamE;eauto with ctl_db.
 Defined.


End Main.


Definition natded0 (I J A:Set) decI decJ  e (bGamma:bcontext I J A )(F:Form I J A) :=
   forall W  Gamma, matches (W:=W) bGamma Gamma -> natded decI decJ  e Gamma F.


Hint Resolve in_extension_rule in_extension_right.
Hint Resolve form_matches comma_matches diam_matches.

Notation "Gamma '{' eqdecI eqdecJ ext '}' '|--' F" :=(natded eqdecI eqdecJ ext Gamma F) (at level 30):mmg_scope. 