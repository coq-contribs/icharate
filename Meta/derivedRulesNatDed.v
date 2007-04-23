(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2006                                *)
(*                              LaBRI                                   *)
(************************************************************************)



Set Implicit Arguments.
Require Export tacticsDed.
Require Export struct_ex.

Section props.
Variables I J A W:Set.
Variable eqdecI:(eqdec I).
Variable eqdecJ :(eqdec J).
Variable ext:(extension I J).

(* generalization of the axiom rule :
    Gamma |-- delta(Gamma) *)
Definition axiomGen :
  forall Gamma:context I J A W,
    natded eqdecI eqdecJ ext Gamma (contextToForm Gamma).
 induction Gamma.
 simpl; constructor 1.
 simpl.
 apply DotI; assumption.
 simpl.
 apply DiamI.
 assumption.
Defined.


(* binary relation between contexts 
   (replaceNTimes ru G1 G2) iff G2 is a result of 
   rewriting G1 a number of times using the structural rule ru *)
Inductive replaceNTimes(Ru:structrule I J):
context I J A W ->context I J A W->Set:=
|noRep:forall(T1:context I J A W), 
          replaceNTimes Ru T1 T1
|repRu: forall(T1 T2 T3 T4 T5:context I J A W),
     struct_replace eqdecI eqdecJ Ru T4 T5 T1 T2->
     replaceNTimes Ru T2 T3->
     replaceNTimes Ru T1 T3.


(* binary relation between contexts 
   (replaceNTimes ext G1 G2) iff G2 results from rewriting 
   G1 a number of times using a rule among the set of rules ext *)
Inductive replaceNTimesExt:
context I J A W ->context I J A W->Set:=
|rep1:forall(T1:context I J A W), replaceNTimesExt T1 T1
|rep2:forall (T1 T2 T3:context I J A W)(ru:structrule I J),
                   in_extension ru ext->
                   replaceNTimesExt  T1 T2->
                   replaceNTimes ru T2 T3->
                   replaceNTimesExt  T1 T3.

(* some properties of the above relations *)

Definition MonoLeftNRu:forall (Ru:structrule I J)(T1 T2 T3:context I J A W)i,
                       replaceNTimes Ru  T1 T2->
                       replaceNTimes Ru (Comma i T3 T1) (Comma i T3 T2).
 induction 1.
 constructor.
 eapply repRu with (T2 := (Comma i T3 T2)).
 constructor 3.
 eauto.
 auto.
Defined.

Definition replNPermut:forall (T1 T2 T3:context I J A W)(ru:structrule I J),
                   in_extension ru ext->
                   replaceNTimesExt  T2 T3->
                   replaceNTimes  ru T1 T2->
                   replaceNTimesExt  T1 T3.
 induction 2; intros.
 econstructor 2.
 eauto.
 constructor 1.    
 auto.
 econstructor.
 eauto.
 eauto. 
 auto.
Defined.

Definition replaceExtMonoLeft:forall (T1 T2 T3:context I J A W)i,
                   replaceNTimesExt T1 T2->
                   replaceNTimesExt  (Comma i T3 T1) (Comma i T3 T2).

  induction 1; intros.
  constructor.
  econstructor 2.
  eauto.
  eauto.
  eapply MonoLeftNRu; auto.
Defined.


Definition MonoRightNRu:forall (T1 T2 T3:context I J A W)i ru,
                    replaceNTimes ru T1 T2->
                    replaceNTimes ru (Comma i T1 T3) (Comma i T2 T3).
 induction 1.
 constructor 1.
 econstructor 2.
 econstructor 2.
 eauto.
 auto.
Defined.

Definition replaceExtMonoRight:forall (T1 T2 T3:context I J A W)i,
                    replaceNTimesExt T1 T2->
                    replaceNTimesExt  (Comma i T1 T3) (Comma i T2 T3).

  induction 1; intros.
  constructor.
  econstructor 2.
  eauto.
  eauto.
  eapply MonoRightNRu; auto.
Defined.

Definition replExtTrans:forall (T1 T2 T3:context I J A W) ,
                               replaceNTimesExt T1 T2->
                               replaceNTimesExt T2 T3->
                               replaceNTimesExt T1 T3.
 induction 1.
 auto.
 intro.
 apply IHreplaceNTimesExt.
 eapply replNPermut;eauto.
Defined.

 
Definition replExtMono:forall (T1 T2 T3 T4:context I J A W) (i:I),
                               replaceNTimesExt T1 T2->
                               replaceNTimesExt T3 T4 ->
                               replaceNTimesExt (Comma i T1 T3) (Comma i T2 T4).
  intros.
  eapply replExtTrans.
  eapply replaceExtMonoRight.
  eauto.
  eapply replaceExtMonoLeft;eauto.
Defined.


(* if (Ru C ext) and (T2 --->(Ru) T1) and T1 |--{ext} C then
   T2 |--{ext} C *) 
Definition natdedNRep:forall (Ru:(structrule I J))(T1 T2:context I J A W)(C:Form I J A),
                              in_extension Ru ext ->
                              replaceNTimes Ru T2 T1->
                              natded eqdecI eqdecJ ext T1 C ->
                              natded eqdecI eqdecJ ext T2 C.
 induction 2.
 intro.
 auto.
 intro.
 eapply StructRule;eauto.
Defined.

(* proof that if T1 --->(ext) T2 and T2 |--{ext}C then 
  T1|--{ext}C *)
Definition repExtnatDed:forall (T1 T2:context I J A W)(B:Form I J A),
                         replaceNTimesExt T1 T2->
                         natded eqdecI eqdecJ ext T2 B->
                         natded eqdecI eqdecJ ext T1 B.
 induction 1.
 auto.
 intro.
 apply IHreplaceNTimesExt.
 eapply natdedNRep;eauto.
Defined.


(* derivation of cut rule *)

Definition cut_rule :forall
   (Gamma Delta: context I J A W)
   (F G: Form I J A),
   weak_sahlqvist_ext  ext ->
   natded eqdecI eqdecJ ext Delta F ->
   natded  eqdecI eqdecJ ext Gamma G ->   
   forall Gamma' r, 
      par_replace (res (hyp  r) F) Delta Gamma Gamma' ->
      natded  eqdecI eqdecJ ext Gamma' G.

 
 intros Gamma Delta F G cond ;induction 2.
 intros.
 inversion H0.
 constructor.
 subst.
 auto.
 intros.
 apply SlashI with n.
 apply IHnatded with r.
 constructor.
 auto.
 constructor.
 intros.
 apply BackI with n.
 apply IHnatded with r.
 constructor.
 constructor.
 auto.
 intros.
 elim (replaceParCom H0).
 intros Gamma1 H1.
 elim H1; clear H1; intros Delta2' H1.
 elim H1; clear H1; intros H1 H2; elim H2; clear H2; intros H2 H3.
 rewrite H3.
 apply DotI.
 eapply IHnatded1.
 eauto.
 eapply IHnatded2; eauto.
 intros.
 elim (replaceParDiam H1).
 intros Gamma1 H2; elim H2; clear H2; intros H2 H3.
 rewrite H3.
 apply DiamI.
 eapply IHnatded; eauto.
 intros.
 apply BoxI.
 eapply IHnatded.
 constructor.
 eauto.
 intros.
 elim (replaceParCom H0).
 intros Gamma1 H1; elim H1; clear H1; intros Delta2' H1.
 elim H1; clear H1; intros H1 H2.
 elim H2; clear H2; intros H2 H3.
 rewrite H3.
 apply SlashE with G.
 eapply IHnatded1; eauto.
 eapply IHnatded2; eauto.
 intros.
 elim (replaceParCom H0).
 intros Gamma1 H1; elim H1; clear H1; intros Delta2' H1.
 elim H1; clear H1; intros H1 H2; elim H2; clear H2; intros H2 H3.
 rewrite H3.
 apply BackE with G.
 eapply IHnatded1; eauto.
 eapply IHnatded2; eauto.
 intros.
 elim (doubleReplacePar r H1).
 intros Gamma1 H2; elim H2; clear H2; intros Gamma2 H2.
 elim H2; clear H2; intros H2 H3.
 elim H3; clear H3; intros H3 H4.
 eapply DotE.
 eauto. 
 eapply IHnatded1; eauto. 
 eapply IHnatded2; eauto.
 intros.
 elim (doubleReplacePar r H0).
 intros Gamma1 H1; elim H1; clear H1; intros Gamma2 H1; elim H1; clear H1;
 intros H1 H2.
 elim H2; clear H2; intros H2 H3.
 eapply DiamE.
 eauto.
 eapply IHnatded1;eauto. 
 eapply IHnatded2; eauto.
 intros.
 elim (replaceParDiam H1).
 intros Gamma1 H2; elim H2; clear H2; intros H2 H3.
 rewrite H3.
 apply BoxE.
 eapply IHnatded; eauto.
 intros.
 cut (weak_sahlqvist_rule  Ru).
 intro cond'.
 elim (structrule_subst_commute cond' s H1).
 intros Gamma1 H2; elim H2; clear H2; intros T2' H2; elim H2; clear H2;
 intros Gamma2 H2; elim H2; clear H2; intros H2 H3; 
 elim H2; clear H2; intros; elim H3; clear H3; intros.
 eapply StructRule;eauto.
 auto.
Defined.


Definition cut_rule1:forall 
   (Gamma Gamma': context I J A W)
   (Delta: context I J A W)
   (F G: Form I J A)r,
   weak_sahlqvist_ext  ext ->
   natded eqdecI eqdecJ ext Delta F ->
   replace (res (hyp r) F) Delta Gamma Gamma' ->
   natded  eqdecI eqdecJ ext Gamma G ->   
   natded  eqdecI eqdecJ ext Gamma'  G.
 intros.
 eapply cut_rule.
 auto.
 eexact H.
 eauto.
 eapply repToParRep;eauto.
Defined. 

Definition cut_rule' : 
  forall 
   (HGamma : hcontext I J A W)
   (Delta: context I J A W)
   (F G: Form I J A),
   weak_sahlqvist_ext ext ->
   natded eqdecI eqdecJ ext Delta F ->
   forall r,
   natded  eqdecI eqdecJ ext (fill HGamma (res (hyp  r) F)) G ->   
   natded  eqdecI eqdecJ ext (fill HGamma Delta) G.
   intros.
   eapply cut_rule.
   apply X.
   eexact H.
   eauto.
   eapply fill_to_par_replace.
Defined.

Definition simple_cut_rule :forall
   (ZGamma : zcontext I J A W)
   (Delta: context I J A W)
   (F G: Form I J A),
   weak_sahlqvist_ext  ext ->
   natded eqdecI eqdecJ ext Delta F ->
   forall r,
   natded  eqdecI eqdecJ ext (zfill ZGamma (res (hyp  r) F)) G ->   
   natded  eqdecI eqdecJ ext (zfill ZGamma Delta) G.
intros.
rewrite zfill_fill.
rewrite zfill_fill in H0.
eapply cut_rule'.
auto.
eauto.
eauto.
Defined.


(* particular case of cut rule *)
Definition natded_trans :
  forall r (Gamma:context I J A W) (F G:Form I J A),
   weak_sahlqvist_ext  ext ->
    natded  eqdecI eqdecJ ext Gamma F ->
    natded   eqdecI eqdecJ ext (res (W:=W) (hyp r) F) G ->
    natded  eqdecI eqdecJ ext Gamma G.
 intros.
 eapply cut_rule with (r:=r).
 auto.
 eexact H. 
 eexact H0.
 econstructor.
Defined.

(* derived rules taken from chapter 2 
  of the Handbook 
 contribution of M.Moortgat *) 
(* derived rules in NL *)

(*  F/iG oi G |-F *)
Definition application_l:forall (r:resource W)(F G :Form I J A)i,
    natded eqdecI eqdecJ ext (res r (Dot i (Slash i F G) G)) F.


 intros.
 eapply DotE with (n:= 1)(p:=2).
 constructor 1.
 constructor 1.
 eapply SlashE; constructor 1.
Defined.

(*  G oi G \i F |-F *)
Definition application_r : forall (r:resource W) (F G: Form I J A)i,
   natded eqdecI eqdecJ ext (res r (Dot i G (Backslash i G F))) F.
 intros.
 eapply DotE with (n:= 1)(p:=2).
 constructor 1.
 constructor 1.
 eapply BackE ;constructor 1.
Defined.

(* F |- (F oi G) /i G *)
Definition co_application_l : forall (r:resource W)(F G : Form I J A)i,
   natded   eqdecI eqdecJ ext (res r F) (Slash i (Dot i F G) G).
 intros; eapply  SlashI with (n:=1). 
 eapply DotI ;constructor 1.
Defined.

(* F|- G \i (G oi F) *)
Definition co_application_r : forall (r:resource W) (F G: Form I J A)i,
   natded   eqdecI eqdecJ ext (res r F) (Backslash i G (Dot i G F)).
  intros; eapply BackI with (n:= 1).
  apply DotI ;constructor 1.
Defined.

(* if F |- G and H|-K then F oiH |- G oi K *)
Lemma Dot_monotonicity : forall (F G H K : Form I J A)i ,
  (natded0 eqdecI eqdecJ ext (form F) G) ->
  (natded0  eqdecI eqdecJ ext (form H ) K) ->
  natded0  eqdecI eqdecJ ext (form (Dot i F H)) (Dot i G K).
 unfold  natded0 at 3;intros.
 eapply DotE with (n:=9)(p:=10).
 constructor 1.
 axiom.
 eapply DotI.
 apply X ; auto.
 apply X0; auto.
Defined.


Lemma Dot_monotonicity0 : forall (F G H K : Form I J A)i ,
   natded0  eqdecI eqdecJ ext (form F) G ->
   natded0   eqdecI eqdecJ ext (form H) K ->
  forall r3, natded  eqdecI eqdecJ ext (res (W:=W) r3 (Dot i F H)) (Dot i G  K).
 intros.
 z_root.
 dotE 9 10. 
 axiom.
 unfocus; eapply DotI.
 apply X ; auto.
 apply X0; auto.
Defined.

(* F|- G /i (F \i G) *)
Definition Slash_lifting :  forall (r:resource W) (F G: Form I J A)i,
                       natded eqdecI eqdecJ ext (res r F) (Slash i G (Backslash i F  G)).
 intros.
 eapply SlashI with 6.
 eapply BackE; axiom.
Defined.

(* F |- (G/iF)\iG *)
Definition Back_lifting : forall (r:resource W)(F G: Form I J A) i ,
                       natded  eqdecI eqdecJ ext (res r F) (Backslash i (Slash i G F) G).
 intros.
 eapply BackI with 6.
 eapply SlashE; axiom.
Defined.

(* a revoir apres la demonstration de la transitivite de |- 
Lemma Slash_isotonicity : (weak_sahlqvist_ext  e)->
                          forall (F G   : Form I J A)  ,
                          (natded0  decI decJ e (form F) G)->
   forall H , natded0 decI decJ e (form (F /i H)) (G /i H).

 unfold natded0 at 2;  intros.
 eapply SlashI with 5.
 xtrans 6 F.
 auto.
 eapply SlashE; axiom. 
 apply X0; auto.
Defined.

Lemma Back_isotonicity : (weak_sahlqvist_ext  e)->
                          forall (F G   : Form I J A)  ,
                          (natded0   decI decJ e (form F) G) ->
   forall H, natded0  decI decJ e (form (H \i F)) (H \i G).
  unfold natded0 at 2; intros.
 eapply BackI with 5.
 z_root.
 xcut 6 F; auto.
 eapply BackE; axiom. 
 unfocus;apply X0;auto.
Qed.


*)

(* if F |- G then H/i G |- H/i F *)
Definition Slash_antitonicity :
  forall (r:resource W) (F G : Form I J A)i ,
    (natded0   eqdecI eqdecJ ext (form F) G) ->
   forall H , natded   eqdecI eqdecJ ext (res r (Slash i H  G)) (Slash i H  F).

 intros.
 eapply SlashI with 5.
 eapply SlashE. 
 axiom.
 apply X;auto.
Defined.

(* if F |- G then  G \i H |- F\i H *)
Lemma Back_antitonicity : 
   forall (r:resource W)(F G: Form I J A) i,
      (natded0 eqdecI eqdecJ ext (form F) G) ->
   forall H, natded  eqdecI eqdecJ ext (res r (Backslash i G H)) (Backslash i F H).
 intros.
 eapply BackI with 5.
 eapply BackE. 
 eapply X;auto.
 axiom.
Qed.

(* F /i ((G/i H) \i G) |- F /i H *)
Definition argument_lowering :
 forall (r:resource W) (F G H: Form  I J A) i, 
  natded eqdecI eqdecJ ext  (res r (Slash i F  (Backslash i (Slash i G  H) G))) (Slash i F  H).
 intros.
 apply Slash_antitonicity.
 unfold natded0 in |- *.
 intros.
 elim (matches_inv_form H0).
 intros.
 subst.
 backI 1.
 eslashE;axiom.
Defined.

(*for unaries*)

(* < []j B >j |-B *)
Definition diam_Box:forall (r:resource W)(B :Form I J A)(j:J),
                  natded eqdecI eqdecJ ext (TDiamond j (res r (Box j B))) B.
 intros.
 boxE.
 axiom.
Defined.

(* <>j[]j B |- B *)
Definition diamBox:forall (r:resource W)(B :Form I J A)(j:J),
                  natded eqdecI eqdecJ ext (res r (Diamond j (Box j B))) B.
 intros.
 elimDiam 1.
 apply diam_Box.
Defined.

(* B |- []j <>j B *)
Definition boxDiam:forall (r:resource W)(B :Form I J A)(j:J),
                   natded eqdecI eqdecJ ext (res r B) (Box j (Diamond j B)).
 intros.
 boxI.
 diamI;axiom.
Defined.
 
(* if <>j A |- B then A |-[]j B*)
Definition box2diam : forall (r:resource W)(F G  : Form I J A)j ,
  weak_sahlqvist_ext  ext ->
  (natded0 eqdecI eqdecJ ext (form (Diamond j F)) G) ->
  natded  eqdecI eqdecJ ext (res r  F) (Box j G).

 intros; unfold natded0;intros.
 boxI.
 eapply natded_trans with (r:=3). 
 auto.
 eapply DiamI .
 axiom.
 auto.
Defined.


Section L.

(* derived rules in L *)
  Variable a:I.
  Hypothesis L1_a : (in_extension (L1 a) ext).
  Hypothesis L2_a : (in_extension (L2 a) ext).


(* D ,a ((D \a C)/a B ,a (((C /a B)\a C) /a E ,a E)) |-C *)
Definition objectLift:forall (D B C E:Form I J A)(r1 r2 r3 r4:resource W),
             natded eqdecI eqdecJ ext 
            (Comma a (res r1 D)
                     (Comma a (res r2 (Slash a (Backslash a D C) B))
                             (Comma a (res r3 (Slash a (Backslash a (Slash a C B) C) E))
                                      (res r4 E)))) 
             C.

 intros.
 eapply StructRule.
 eexact L1_a.
 here.
 autorewrite with ctl_db; auto.
 eapply BackE;[idtac|eapply SlashE; constructor 1].
 eapply SlashI with 0.
 eapply StructRule.
 eexact L2_a.
 here.
 autorewrite with ctl_db; auto.
 eapply BackE.
 constructor 1.
 eapply SlashE;constructor.
Defined.
 
(* F/a G |- (F/a H)/a (G/a H) *)
  Definition Geach_main_Slash : forall (r:resource W)(F G H : Form I J A) ,
                           natded   eqdecI eqdecJ ext (res r (Slash a F G))
                                              (Slash a (Slash a F  H) (Slash a G H)).
  intros r F G H.
  eapply SlashI with 3.
  eapply SlashI with 2.
  eapply StructRule.
  eexact L2_a.
  here. 
  autorewrite with ctl_db; auto.
  eslashE; try axiom.
  eslashE; axiom.
 Defined.

(* G \a F |- (H\a G) \a (H \a F) *)
Definition Geach_main_Back : forall(r:resource W) (F G H : Form I J A),
                           natded  eqdecI eqdecJ ext (res r (Backslash a G F))
                                              (Backslash a (Backslash a H  G)
                                                           (Backslash a H  F)).
  intros r F G H.
  eapply BackI with 3.
  eapply BackI with 2.
  eapply StructRule.
  eexact L1_a.
  here. 
  autorewrite with ctl_db; auto.
  ebackE; try axiom.
  ebackE; axiom.
 Defined.

(* H\a G |- (H\a F) /a (G \a F) *)
 Definition Geach_secondary_Slash : forall (r:resource W)(F G H: Form I J A),
                           natded eqdecI eqdecJ ext (res r (Backslash a H  G))
                                              (Slash a (Backslash a H  F)  (Backslash a G F)).
 intros r F G H.
 eapply SlashI with 3.
 eapply BackI with 2.
 eapply StructRule.
 eexact L1_a.
 here.
 autorewrite with ctl_db; auto. 
 ebackE;try axiom.
 ebackE; axiom.
 Defined.

(* G /a H |- (F /a G) \a (F /a H) *)
 Definition Geach_secondary_Back : forall(r:resource W) (F G H : Form I J A),
                           natded  eqdecI eqdecJ ext (res r (Slash a G  H))
                                              (Backslash a (Slash a F  G)  (Slash a F  H)).
  intros r F G H.
  eapply BackI with 3.
  eapply SlashI with 2.
  eapply StructRule.
  eexact L2_a.
  here.
  autorewrite with ctl_db; auto. 
  eslashE; try axiom.
  eslashE; axiom.
 Defined.

(* (F /a G) oa (G/a H) |- F /a H *)
Definition composition_Slash : forall (r:resource W) (F G H : Form I J A),
                                natded  eqdecI eqdecJ ext
                                (res r (Dot a (Slash a F  G)  (Slash a G  H)))
                                (Slash a F  H).
 intros r F G H.
 eapply DotE with (n:=1)(p:=2).
 here.
 axiom.
 eapply SlashI with 3.
 eapply StructRule.
 eexact L2_a.
 here.
 autorewrite with ctl_db; auto. 
 eslashE; try axiom.
 eslashE; axiom.
Defined.

(* H\a G oa G\a F |-H \a F *)
Definition composition_Back : forall (r:resource W) (F G H : Form I J A),
                                natded  eqdecI eqdecJ ext
                                (res r  (Dot a (Backslash a H  G)  (Backslash a G  F)))
                                (Backslash a H  F).
 intros.
 eapply DotE with (n:=1)(p:=2).
 here.
 axiom.
 eapply BackI with 3.
 eapply StructRule.
 eexact L1_a.
 here.
 autorewrite with ctl_db; auto. 
 ebackE; try axiom.
 ebackE; axiom. 
Defined.

(* (F \a G)/a H |- F \a (G /a H) *)
 Definition restructuring_l :   forall (r:resource W)(F G H : Form I J A),
                                natded  eqdecI eqdecJ ext
                                (res r  (Slash a (Backslash a F  G) H))
                                (Backslash a F  (Slash a G  H)).
 intros.
 eapply BackI with 1.
 eapply SlashI with 2.
 eapply StructRule.
 eexact L2_a.
 here.
 autorewrite with ctl_db; auto. 
 eapply BackE.
 axiom.  
 eapply SlashE; axiom.
Defined.

(* F \a (G /a H) |- (F \a G)/a H *)
Definition restructuring_r : forall (r:resource W) (F G H : Form I J A),
                                natded  eqdecI eqdecJ ext
                                (res r (Backslash a F (Slash a G  H)))
                                 (Slash a (Backslash a F G) H) .
 intros.
 eapply SlashI with 2.
 eapply BackI with 1.
 eapply StructRule.
 eexact L1_a.
 here.
 autorewrite with ctl_db; auto. 
 eslashE.
 ebackE;axiom.
 axiom.
 Defined.

(* F /a (G oa H) |- (F /a H)/a G *) 
Definition currying_Slash :   forall(r:resource W) (F G H : Form I J A),
                                natded  eqdecI eqdecJ ext
                                (res r  (Slash a F (Dot a G  H)))
                                 (Slash a (Slash a F  H)  G) .
 intros.
 eapply SlashI with 1.
 eapply SlashI with 2.
 eapply StructRule.
 eexact L2_a.
 here.
 autorewrite with ctl_db; auto. 
 eapply SlashE with (Dot a G H).
 axiom.
 eapply DotI. 
 axiom.
 axiom. 
Defined.

(* (F /a H) /a G) |- (F /a (G oa H)) *)
Definition De_currying_Slash :  forall (r:resource W)(F G H: Form I J A),
                                natded  eqdecI eqdecJ ext
                                (res r (Slash a (Slash a F  H)  G))
                                 (Slash a F (Dot a G  H))  .

 intros.
 eapply SlashI with 1.
 eapply DotE with (n:=2)(p:=3).
 down_r.
 here.
 axiom.
 eapply StructRule.
 eexact L1_a.
 here.
 autorewrite with ctl_db; auto.  
 eslashE; try axiom.
 eslashE; axiom.
Defined.

(* (F oa G)\a H |- G \a (F \a H) *)
Definition currying_Back :  forall (r:resource W)(F G H : Form I J A),
                                natded eqdecI eqdecJ ext
                                (res r (Backslash a (Dot a F  G) H))
                                 (Backslash a G (Backslash a F  H)) .
 intros.
 eapply BackI with 1.
 eapply BackI with 2.
 eapply StructRule.
 eexact L1_a.
 here.
 autorewrite with ctl_db; auto.  
 dotE 33 34.
 down_l; here. 
 eapply DotI;axiom.
 ebackE; try axiom.
 eapply DotI;axiom.
Defined.

(* G \a (F \a H) |- (F oa G) \a H *)
Definition De_currying_Back :  forall (r:resource W)(F G H : Form I J A),
                                natded  eqdecI eqdecJ ext
                                (res r   (Backslash a G  (Backslash a F  H)))
                                 (Backslash a (Dot a F G) H)  .
 intros.
 eapply BackI with 1.
 dotE 2 3.
 down_l; here.  
 axiom.
 eapply StructRule.
 eexact L2_a.
 here.
 autorewrite with ctl_db; auto.
 ebackE; try axiom.
 ebackE; axiom. 
Defined.

End L.

Section P.
  Variable c:I.
  Hypothesis p_c : in_extension (P c) ext.

 (*  if F |- G \c H then G|- F \c H *)
  Definition Permutation : forall (F G H : Form I J A),
                           (natded0  eqdecI eqdecJ ext
                                       (form F) (Backslash c G H))->
                           natded0  eqdecI eqdecJ ext
                                       (form G) (Backslash c F  H).
                           
  intros;unfold natded0;intros.
  eapply BackI with 1.
  eapply StructRule.
  eauto.
  here.
  autorewrite with ctl_db; auto. 
  ebackE.
  axiom.
  apply X; auto.
Defined.

(* if F |- H/c G then G |-H /c F *)
  Definition Permutation2 : forall (F G H : Form I J A),
                           (natded0  eqdecI eqdecJ ext
                                       (form F) (Slash c H  G))->
                           natded0  eqdecI eqdecJ ext
                                       (form G) (Slash c H  F).
                           
  intros; unfold natded0; intros.
  eapply SlashI with 1.
  eapply StructRule.
  eauto.
  here.
  autorewrite with ctl_db; auto.
  eslashE.
  apply X; auto.
 axiom.
Defined.

(* F/c G |-G \c F *)
Definition exchange_l : forall (r:resource W) (F G : Form I J A),
                       natded  eqdecI eqdecJ ext (res r (Slash c F  G)) (Backslash c G F).
 intros.
 eapply BackI with 1.
 eapply StructRule.
 eauto.
 here.
 autorewrite with ctl_db; auto.
 eslashE; axiom.
Defined.

(* G \c F |- F /c G *)
Definition exchange_r : forall (r:resource W) (F G : Form I J A),
                       natded  eqdecI eqdecJ ext (res r (Backslash c G  F)) (Slash c F  G).
 intros.
 eapply SlashI with 1.
 eapply StructRule.
 eauto.
 here.
 autorewrite with ctl_db; auto.
 ebackE; axiom.
Defined.

(* F |- G /c (G /c F) *)
Definition preposing : forall (r:resource W) (F G : Form I J A),
                       natded  eqdecI eqdecJ ext (res r F) (Slash c G  (Slash c G  F)).
 intros.
 eapply SlashI with 1.
 eapply StructRule.
 eauto.
 here.
 autorewrite with ctl_db; auto.
 eslashE; axiom.
Defined.

(* F |- (F \c G) \c G*)
Definition postponing : forall(r:resource W) (F G : Form I J A),
                       natded  eqdecI eqdecJ ext (res r F) (Backslash c (Backslash c F  G) G).
 intros.
 eapply BackI with 1.
 eapply StructRule.
 eauto.
 here.
 autorewrite with ctl_db; auto.
 ebackE; axiom.
Defined.

End P.

(* for LP logic*) 

  Section LP.
 Variable c:I.
  Hypothesis L1_c : in_extension (L1 c) ext.
  Hypothesis L2_c : in_extension (L2 c) ext.
  Hypothesis P_c: in_extension (P c) ext.

(* (F /c G) oc (H \c G) |- (H \c F)*)
Definition mixed_composition_Back : forall (r:resource W) (F G H :Form I J A),
                                          natded  eqdecI eqdecJ ext 
                                          (res r (Dot c (Slash c F  G) (Backslash c H  G)))
                                          (Backslash c H  F).
 intros.
 eapply DotE with (n:=2)(p:=3).
 here.
 axiom.
 eapply StructRule.
 eexact P_c.
 here.
 autorewrite with ctl_db; auto.
 eapply BackI with 1.
 eapply StructRule.
 eexact L1_c.
 here.
 autorewrite with ctl_db; auto.
 ebackE.
 ebackE; axiom.   
 apply exchange_l; auto.
Defined.

(* (G /c H) oc (G\c F) |-F /c H *) 
Definition mixed_composition_Slash : forall (r:resource W)(F G H : Form I J A),
                                          natded  eqdecI eqdecJ ext 
                                          (res r (Dot c (Slash c G  H) (Backslash c G  F)))
                                          (Slash c F  H).
 intros.
 dotE 2 3.  
 here.
 axiom.
 eapply StructRule.
 eexact P_c.
 here.
 autorewrite with ctl_db; auto.
 eapply SlashI with 1.
 eapply StructRule.
 eexact L2_c.
 here.
 autorewrite with ctl_db; auto.
 eslashE.
 apply exchange_r; auto.  
 eslashE; axiom.
Defined.
  
End LP.

Section MP.

 Variables h r : I.
 Variable MP_hr : in_extension (MP h r) ext.

(* F /h G  |- (H \r F) /h (H \r G) *)
Definition mixed_composition_Geach : forall (re:resource W)(F G H : Form I J A),
                                          natded  eqdecI eqdecJ ext 
                                          (res re  (Slash h F  G))
                                          (Slash h (Backslash r H  F) (Backslash r H  G)).
intros.
slashI 1.
backI 2.
eapply StructRule.
eauto.
here.
autorewrite with ctl_db; auto.
eslashE .
axiom.
ebackE; axiom.
Defined.

End MP.

Section MC.
Variables i j :I.
Hypothesis MC_ij : in_extension (MC i j) ext.

 (* Moortgat, page 133 *)

  (* F /j H ,i (F \i G) /j H |- G /j H *)
 Definition S_combinator : forall (r1 r2:resource W)(F G H : Form I J A) ,
                            natded eqdecI eqdecJ ext 
                                    (Comma i (res r1  (Slash j F H))
                                             (res r2  (Slash j (Backslash i F  G) H)))
                                          (Slash j G  H).
 intros.
 slashI 1.
 eapply StructRule.
 eauto.
 here.
 autorewrite with ctl_db;auto.
 backE F.
 slashE H; axiom.
 slashE H; axiom.
Defined.

End MC.



End  props.

