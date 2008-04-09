Set Implicit Arguments.

Require Export polarity.
Require Export Omega.

Fixpoint linear_ext(I J:Set)(R:extension I J){struct R}:Prop:=
match R with
|NL=>True
|add_rule r1 R'=> linear r1 /\ linear_ext R'
end.


Lemma linear_pol:forall (A I J W:Set)(decA:eqdec A)(decJ:eqdec J)(decI:eqdec I)(R:extension I J),
                       linear_ext R->
                       forall ru, in_extension ru R->structPol W decA decI decJ ru.
intros A I J W decA decJ decI R; elim R.
intros.
inversion H0.
intros.
simpl in H0.
decompose [and] H0;clear H0.
inversion H1;subst.
apply linearPolarity;auto.
exact (H H3 _ H4).
Qed.

Ltac and_split:=
match goal with 
| |- and ?P ?Q=>
 split;and_split
|_=>(try omega) || (try tauto)
end.


Ltac polH H decA q:=
match goal with
| |- False=>
match type of H with
|natded _ _ _ _ _ =>
simple eapply polarityRefDed with (p:=q)(2:=H)(eqdecA:=decA);
 [simple apply linear_pol;simpl;unfold linear, leftLinear,rightLinear,allDistinctLeaves,isIncluded;simpl;and_split|simpl;omega] 
|_=>idtac
end
|_=> idtac
end.

Ltac pol decA p:=
match goal with
|H:natded _ _ _ _ _ |- False=>
polH H decA p
|_=>idtac
end.
