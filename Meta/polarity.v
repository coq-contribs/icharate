(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2006                                *)
(*                              LaBRI                                   *)
(************************************************************************)

Set Implicit Arguments.
Require Export sequent.
Require Export natDed.
Require Import ZArith.
Require Import ZArithRing.
Require Export struct_props.

Section pol.

Variables I J A W:Set.
Variable eqdecA :eqdec A.
Variable eqdecI:eqdec I.
Variable eqdecJ:eqdec J.

(* definition of the polarity of an atom p in the formula F' *)
Fixpoint polF (p:A) (F:(Form I J A)) {struct F} : Z :=
  match F with
  | At a =>
      match eqdecA p a with
      | left _ => 1%Z
      | right _ => 0%Z
      end
  | Slash i F1 F2 => (polF p F1 - polF p F2)%Z
  | Backslash i F1 F2 => (polF p F2 - polF p F1)%Z
  | Dot i F1 F2 => (polF p F2 + polF p F1)%Z
  | Diamond i F1 => polF p F1
  | Box i F1 => polF p F1
  end.

(* extension to contexts of formulas *)
Fixpoint polT (p:A) (T':context I J A W) {struct T'} : Z :=
  match T' with
  | res r F => polF p F
  | Comma i T1 T2 => (polT p T1 + polT p T2)%Z
  | TDiamond j T1 => polT p T1
  end.


Definition structPol (Ru:structrule I J) :=
  forall (T1 T2:context I J A W) (p:A),
    apply_rule Ru eqdecI eqdecJ T2=Some T1 -> polT p T2 = polT p T1.


Theorem replacePolarity :
 forall (Gamma Gamma' Delta Delta':context I J A W) (p:A),
   replace  Delta Delta' Gamma Gamma' ->
   polT p Delta = polT p Delta' ->
   polT p Gamma' = polT p Gamma.

 Proof.
  intros Gamma Gamma' Delta Delta' p H; elim H; intros; simpl; auto with zarith.
 Qed.

Theorem replaceStruct:forall (Ru:structrule I J)
     (T1 T2 T3 T4:context I J A W)(p:A),
  structPol Ru ->
 struct_replace eqdecI eqdecJ Ru T1 T2 T3 T4 ->
 polT p T3=polT p T4.

Proof.
 unfold structPol; induction 2; intros; simpl; auto with zarith.
Qed.


(* proof of polarity theorem within sequent calculus *)

(* proof of the theorem of polarity which states that in 
the gentzen calculus if the sequent G =>A is provable then
 for all atom p, the polarity of p in the context G equals the 
polarity of p in the formula A *)

Theorem polaritySeq :
 forall (Gamma:context I J A W) (F':Form I J A) (p:A)(ext:(extension I J)),
   (forall Ru, in_extension Ru ext -> structPol Ru)->
   gentzen eqdecI eqdecJ ext Gamma F' ->
   polT p Gamma = polF p F'.
 Proof.
 intros Gamma F' p ext H H0.
 elim H0.
 simpl.
 auto.
 intros Gamma0 F B i n H1.
 simpl.
 intro H2.
 rewrite <- H2.
 ring.
 intros Gamma0 F B i n H1.
 simpl.
 intro H2.
 rewrite <- H2.
 ring.
 intros Gamma0 Delta F B i H1 H2 H3 H4.
 simpl.
 rewrite <- H2.
 rewrite <- H4.
 ring.
 intros Gamma0 F i H1 H2.
 simpl; auto.
 intros Gamma0 F i H1.
 simpl.
 intro H2; auto.
 intros Delta Gamma0 Gamma' F B C i n r1 H1 H2 H3 H4 H5.
 rewrite <- H5.
 eapply replacePolarity.
 eauto.
 simpl.
 rewrite <- H3.
 ring.
 intros Delta Gamma0 Gamma' F B C i n r1 H1 H2 H3 H4 H5.
 rewrite <- H5.
 eapply replacePolarity.
 eauto.
 simpl.
 rewrite <- H3.
 ring.
 intros Gamma0 Gamma' F B C i n1 n2 r1 H1 H2 H3.
 rewrite <- H3.
 eapply replacePolarity.
 eauto.
 simpl.
 auto.
 ring.
 intros Gamma0 Gamma' F B i n r1 H1 H2 H3.
 rewrite <- H3.
 eapply replacePolarity.
 eauto.
 simpl.
 auto.
 intros Gamma0 Gamma' F B i n r1 H1 H2 H3.
 rewrite <- H3.
 eapply replacePolarity.
 eauto.
 simpl.
 auto.
 intros Delta Gamma0 Gamma' F C n H1 H2 H3 H4 H5.
 rewrite <- H5.
 eapply replacePolarity.
 eauto.
 simpl.
 auto.
 intros Gamma0 Gamma' T1 T2 C Ru H1 H2 H3 H4.
 rewrite <- H4.
 eapply replaceStruct;eauto.
Qed.

(* derived theorem which can be used to prove that a sequent
is not provable in the gentzen calculus using a simpl calculus
of polarity*)

Theorem polarityRef :
 forall (Gamma:context I J A W) (F':Form I J A) (p:A)(ext :extension I J),
  (forall Ru, in_extension Ru ext -> structPol Ru )->
   gentzen eqdecI eqdecJ ext Gamma F' ->
   polT p Gamma <> polF p F' -> False.
 Proof.
 intros.
 elim H1.
 eapply polaritySeq; eauto.
Qed.

(* proof of polarity theorem within natural deduction formalism *)
Theorem polarityDed :
 forall (Gamma:context I J A W) (F':Form I J A) (p:A)(ext:(extension I J)),
   (forall Ru, in_extension Ru ext -> structPol Ru)->
   natded eqdecI eqdecJ ext Gamma F' ->
   polT p Gamma = polF p F'.
Admitted.

Theorem polarityRefDed :
 forall (Gamma:context I J A W) (F':Form I J A) (p:A)(ext :extension I J),
  (forall Ru, in_extension Ru ext -> structPol Ru )->
   natded eqdecI eqdecJ ext Gamma F' ->
   polT p Gamma <> polF p F' -> False.

intros.
elim H1;eapply polarityDed;eauto.
Qed.



Lemma sub_cont_pol:forall (rp:rule_pattern I J)(Gamma:context I J A
   W) l p , 
   hasSubContexts rp Gamma l->
   sum_all (map (polT p) l) = polT p Gamma.
Proof.
 induction 1.
 simpl in |- *.
 ring.
 rewrite map_app.
 unfold sum_all in |- *.
 rewrite op_all_app.
 simpl in |- *.
 auto with zarith.
 intro; ring.
 intros; ring.
 simpl in |- *.
 auto.
Qed.


Lemma permut_same_pol:forall (rp1 rp2:rule_pattern I J) (T1 T2:context
             I J A W) p,
            permut (flatten_pattern rp1)(flatten_pattern rp2)->
            allDistinctLeaves rp1->
            allDistinctLeaves rp2->
            apply_rule (rp1,rp2) eqdecI eqdecJ T1=Some T2->
            polT p T1=polT p T2.
Proof.
 intros.
 elim (subCont_same_shape (apply_rule_same_shape _ _ _ _ _ H2)).
 intros l H3.
 elim (subCont_same_shape (apply_rule_same_shape2 _ _ _ _ _ H2)).
 intros l' H4.
 rewrite <- (sub_cont_pol p H3).
 rewrite <- (sub_cont_pol p H4).
 unfold sum_all in |- *.
 apply op_all_permut.
 intros; auto with zarith.
 intros; auto with zarith.
 intros; auto with zarith.
 apply map_permut.
 apply permut_sub_cont with eqdecI eqdecJ rp1 rp2 T1 T2; auto.
Qed.


(* linear rules verify the structPol condition 
 i.e. are suitable for the application of the polarity
  theorem *)

Lemma linearPolarity:forall (ru:structrule I J),
                             linear ru ->
                             structPol ru.
Proof.
 intro ru;case ru; unfold structPol in |- *.
 intros.
 eapply permut_same_pol.
 apply linear_permut;eauto.
 unfold linear, leftLinear in H;tauto.
 unfold linear, rightLinear in H; tauto.
 eauto.
 Qed.
End pol.


