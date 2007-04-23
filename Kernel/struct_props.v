(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                              LaBRI                                   *)
(************************************************************************)


Require Export apply_rule_props.


Set Implicit Arguments.

Section classes.
 Variables I J: Set.

Fixpoint countDiam(j:J)(decJ:eqdec J)(rp1:rule_pattern I J){struct rp1}:nat:=
match rp1 with
|pvar k =>0
|pcomma _ r1 r2=> countDiam j decJ r1 +countDiam j decJ r2
|pdiam j1 r1 =>match (decJ j j1) with 
      |left _=>countDiam j decJ r1 +1
      |right _ => countDiam j decJ r1
    end
end.

(* definition of some classes of structural rules: left linear, linear
etc...*)

Definition leftLinear(ru:structrule I J):Prop:=
match ru with 
|(r1 ,r2)=>allDistinctLeaves r1 /\isIncluded r2 r1
end.

Definition rightLinear(ru:structrule I J):Prop:=
match ru with 
|(r1 ,r2)=>allDistinctLeaves r2 /\isIncluded r1 r2
end.


Definition linear(ru:structrule I J):Prop:=
leftLinear ru /\ rightLinear ru.

Definition notLeaf (ru:rule_pattern I J):Prop:=
match ru with 
|pvar _ => False
|other=> True
end.

Definition weakSahlqvist(ru:structrule I J):Prop:=
match ru with 
|(r1, r2)=>leftLinear (r1,r2)/\isIncluded r1 r2/\notLeaf r1
end.

Lemma linear_permut:forall (r1 r2:rule_pattern I J),
                      linear (r1, r2)->
                      permut (flatten_pattern r1)(flatten_pattern r2).
Proof.
intros.
unfold linear in H.
unfold leftLinear, rightLinear in H.
decompose [and] H; clear H.
apply incl_distinct_permut; auto.
exact eq_nat_dec.
Qed.


Definition linearDiam(decJ:eqdec J)(ru:structrule I J): Prop:=
 match ru with
|(rp1,rp2)=>  linear ru /\forall j, countDiam j decJ rp1=countDiam j
 decJ rp2
end.


Lemma leftLinear_Com1:forall (rp1 rp2 rp3:rule_pattern I J) (i:I),
                    leftLinear (rp1, (pcomma i rp2 rp3))->
                    leftLinear (rp1, rp2).
simpl in |- *.
tauto.
Qed.

Lemma leftLinear_Com2:forall (rp1 rp2 rp3:rule_pattern I J) (i:I),
                    leftLinear (rp1, (pcomma i rp2 rp3))->
                    leftLinear (rp1, rp3).
simpl in |- *.
tauto.
Qed.

Lemma leftLinear_Diam:forall (rp1 rp2:rule_pattern I J) (i:J),
                    leftLinear (rp1 , (pdiam i rp2)) ->
                    leftLinear (rp1 ,rp2).
simpl in |- *.
tauto.
Qed.


Definition same_shape_left_linear:forall A W decI decJ (rp1 rp2:rule_pattern I J)(Gamma:context I J A W),
                              leftLinear (rp1 , rp2) ->
                              same_shape rp1 Gamma->
                             {Gamma':context I J A W |apply_rule (rp1, rp2) decI decJ Gamma=Some Gamma'}.

 intros  A W decI decJ rp1 rp2; elim rp2; intros.
 simpl in H.
 elim H; clear H; intros.
 simpl in |- *.
 elim (acces_same_shape decI decJ _ H H1 H0).
 intros Gamma1 H2.
 exists Gamma1.
 rewrite H2.
 auto.
 elim (H0 _ (leftLinear_Com2 H1) H2).
 intros.
 elim (H _ (leftLinear_Com1 H1) H2).
 intros.
 simpl in p; simpl in p0.
 simpl in |- *.
 rewrite p; rewrite p0.
 econstructor; eauto.
 simpl in |- *.
 elim (H _ (leftLinear_Diam H0) H1); intros.
 econstructor.
 simpl in p; rewrite p; eauto.
Defined.

(*left linear rules are weak sahlqvist ones *)
Definition leftLinear_par_replace:forall A W decI decJ (ru:structrule I J)(Gamma1 Gamma2
Delta Gamma1':context I J A W) (r:resource W)(A1:Form I J A),
             leftLinear ru ->
             apply_rule ru decI decJ Gamma1 =Some Gamma2 ->
             par_replace (res r A1) Delta Gamma1 Gamma1' ->
             {Gamma2':context I J A W |apply_rule ru decI decJ
	     Gamma1'=Some Gamma2'}.

 intros A W decI decJ ru; case ru; intros.
 cut (same_shape r Gamma1').
 intro.
 apply same_shape_left_linear; auto.
 eapply same_shape_par_replace.
 eauto. 
 eapply apply_rule_same_shape.
 eauto.
Defined.

Definition leftLinearSahlqvist:forall (ru:structrule I J), 
               leftLinear ru->
               weak_sahlqvist_rule ru.

 unfold weak_sahlqvist_rule in |- *.
 intros.
 elim (leftLinear_par_replace _ _ _ H H0 H1).
 intros Gamma2 H2.
 exists Gamma2.
 exists (apply_rule_par_replace _ _ _ H1 H0 H2).
 auto.
Defined.


                            


End classes.