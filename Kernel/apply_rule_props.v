(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2006                                *)
(*                              LaBRI                                   *)
(************************************************************************)

Require Export basics.
Set Implicit Arguments.

Section props.
 Variables A W I J: Set.
 

(* some inversion lemmas *)

Lemma access_res:forall  decI decJ n (r:resource W) (rp
:rule_pattern I J) (Gamma':context I J A W)(A1: Form I J A), 
access decI decJ rp n (res r A1) =(Some Gamma',true) ->
 {i:nat |rp=(pvar i)}.

 intros  decI decJ n r rp; case rp.
 simpl in |- *.
 intro n0.
 intros.
 exists n0.
 auto.
 simpl in |- *.
 intros.
 discriminate H.
 simpl in |- *.
 intros.
 discriminate H.    
Defined.
   
Lemma access_com_none:forall (rp1 rp2:rule_pattern I J) decI decJ n i 
                      (Gamma:context I J A W),
                   access decI decJ (pcomma i rp1 rp2) n Gamma=(None, true) ->
                      {Gamma1:context I J A W&{Gamma2:context  I J A W|
                       Gamma=(Comma i Gamma1 Gamma2)/\
                     (access decI decJ rp2 n Gamma2=(None,true))/\
                      (access  decI decJ rp1 n Gamma1=(None, true))}}.

 simpl in |- *.
 intros  rp1 rp2 decI decJ n i Gamma; case Gamma.
 intros.
 discriminate H.
 intro i0; case (decI i0 i).
 intro R; subst; intros c c0.
 intros.
 exists c; exists c0; generalize H; clear H.
 case (access decI decJ rp1 n c).
 intros o b0; case o.
 intro c1; case (access decI decJ rp2 n c0).
 intro o0; case o0.
 intros.
 discriminate H.
 intro b1; case b1.
 intro H; discriminate H.
 intro H; discriminate H.
 case b0.
 tauto.
 intro H; discriminate H.
 intros.
 discriminate H.
 intros; discriminate H.
Qed.

Lemma access_com_some:forall (rp1 rp2:rule_pattern I J) decI decJ n b
 i (Gamma Gamma':context I J A W),
          access decI decJ (pcomma i rp1 rp2) n Gamma=((Some Gamma'), b) ->
         {Gamma1:context I J A W&{Gamma2:context I J A W|
           Gamma=(Comma i Gamma1 Gamma2)/\
         (((access decI decJ rp1 n Gamma1=((Some Gamma'),b))/\
                      (access  decI decJ rp2 n Gamma2=(None, true))) \/
                     ((access decI decJ rp2 n Gamma2=((Some Gamma'),b))/\
                      (access  decI decJ rp1 n Gamma1=(None, true))))}}.
 simpl in |- *.
 intros rp1 rp2 decI decJ n b i Gamma Gamma'; case Gamma.
 intros.
 discriminate H.
 intro i0; case (decI i0 i).
 intro R; subst; intros c c0.
 intros.
 exists c; exists c0; generalize H; clear H.
 case (access decI decJ rp1 n c).
 intros o b0; case o.
 intro c1; case (access decI decJ rp2 n c0).
 intro o0; case o0.
 intros.
 discriminate H.
 intro b1; case b1.
 intros; tauto.
 intro H; discriminate H.
 case b0.
 tauto.
 intro H; discriminate H.
 intros.
 discriminate H.
 intros.
 discriminate H.
Qed.

Lemma access_Com_some:forall (rp:rule_pattern I J) decI decJ n 
 i (Gamma1 Gamma2 Gamma':context I J A W),
                   access decI decJ rp n (Comma i Gamma1 Gamma2)=
                     ((Some Gamma'), true) ->
                      {rp1:rule_pattern I J &{rp2:rule_pattern I J&
                     {H: {(access decI decJ rp1 n Gamma1=((Some Gamma'),true))/\
                      (access  decI decJ rp2 n Gamma2=(None, true))} +
                     {(access decI decJ rp2 n Gamma2=((Some Gamma'),true))/\
                      (access  decI decJ rp1 n Gamma1=(None,true))} |
                       rp=pcomma i rp1 rp2}}}
                  +{i:nat|rp=pvar i}.
 intros.
 generalize H; clear H.
 case rp.
 intros; right.
 exists n0; auto.
 intros i0 r r0.
 intro H0.
 cut
 ({access decI decJ r n Gamma1 = (Some Gamma', true) /\
   access decI decJ r0 n Gamma2 = (None, true)} +
  {access decI decJ r0 n Gamma2 = (Some Gamma', true) /\
  access decI decJ r n Gamma1 = (None, true)}).
 intro H.
 left.
 exists r; exists r0; exists H.
 generalize H0.
 simpl in |- *.
 case (decI i i0).
 intros; subst; auto.
 intros.
 discriminate H1.
 generalize H0.
 simpl in |- *.
 case (decI i i0).
 case (access decI decJ r n Gamma1).
 intro o; case o.
 case (access decI decJ r0 n Gamma2).
 intro o0; case o0.
 intros.
 discriminate H1.
 intro b; case b.
 intros.
 injection H1; intros; subst.
 left.
 tauto.
 intros.
 discriminate H1.
 intro b; case b.
 intros.
 right.
 tauto.
 intros.
 discriminate H1.
 intros.
 discriminate H1.
 simpl in |- *.
 intros.
 discriminate H.
Qed.


Lemma access_diam_some:forall (rp:rule_pattern I J) decI decJ n b j 
                   (Gamma Gamma':context I J A W),
                    access decI decJ (pdiam j rp) n Gamma=((Some Gamma'), b) ->
                   {Gamma1:context I J A W|Gamma=(TDiamond j Gamma1) /\
                    access decI decJ rp n Gamma1=((Some Gamma'), b)}.
 simpl in |- *.
 intros rp decI decJ n b j Gamma Gamma'; case Gamma.
 intros; discriminate H.
 intros; discriminate H.
 intro j0; case (decJ j j0).
 intros.
 exists c.
 subst; tauto.
 intros.
 discriminate H.
Qed.

Lemma access_diam_TDiam:forall (rp:rule_pattern I J) decI decJ n b j 
                   (Gamma Gamma':context I J A W),
                    access decI decJ  rp n (TDiamond j Gamma)=((Some Gamma'), b) ->
                   {rp1:rule_pattern I J|rp=(pdiam j rp1) /\
                    access decI decJ rp1 n Gamma=((Some Gamma'), b)}+
                   {j:nat|rp=pvar j}.
 intros  rp; case rp.
 intros; right; econstructor; eauto.
 simpl in |- *.
 intros.
 discriminate H.
 intros; left.
 generalize H; simpl in |- *.
 case (decJ j j0).
 intros.
 subst.
 exists r.
 tauto.
 intros.
 discriminate H0.
Qed.

Lemma access_diam_none:forall  (rp:rule_pattern I J) decI decJ n  j 
                      (Gamma :context I J A W),
                    access decI decJ (pdiam j rp) n Gamma=(None, true) ->
                   {Gamma1:context I J A W|Gamma=(TDiamond j Gamma1) /\
                    access decI decJ rp n Gamma1=(None,true)}.
 simpl.
 intros rp decI decJ n j Gamma; case Gamma.
 intros; discriminate H.
 intros; discriminate H.
 intro j0; case (decJ j j0).
 intros.
 exists c.
 subst; tauto.
 intros.
 discriminate H.
Qed.

Lemma access_some_true: forall (rp1:rule_pattern I J) decI decJ n b
                   (Gamma Gamma':context I J A W),
                   access decI decJ rp1 n Gamma=(Some Gamma', b)->
                   b=true.
 intros rp1; elim rp1.
 intros n decI decJ n0 b Gamma Gamma'.
 simpl in |- *.
 case (eq_nat_dec n n0).
 intros.
 injection H; auto.
 intros.
 discriminate H.
 intros.
 elim (access_com_some _ _ _ _ _ _ _ H1).
 intros Gamma1 H2; elim H2; clear H2; intros Gamma2 H2.
 elim H2; clear H2; intros H2 H3.
 elim H3; clear H3; intro H3; elim H3; clear H3; intros H3 H4.
 eauto.
 eauto.
 intros.
 elim (access_diam_some _ _ _ _ _ _ H0).
 intros Gamma1 H1.
 elim H1; clear H1; intros.
 eauto.
Qed.

Lemma access_dec:forall (rp1:rule_pattern I J) decI decJ n 
                   (Gamma :context I J A W),
                 (exists Gamma', access decI decJ rp1 n Gamma=(Some Gamma', true)) \/
                 (exists b:bool,  access decI decJ rp1 n Gamma=(None ,
                   b)).
Proof.
 intros.
 cut
 ((exists Gamma' : context I J A W,
     (exists b : bool, access decI decJ rp1 n Gamma = (Some Gamma', b))) \/
  (exists b : bool, access decI decJ rp1 n Gamma = (None, b))).
 intro H0; elim H0; intros.
 elim H; clear H; intros Gamma' H; elim H; clear H; intros.
 rewrite (access_some_true _ _ _ _ _ H) in H.
 left; econstructor; eauto.
 tauto.
 case (access decI decJ rp1 n Gamma).
 intros o b; case o.
 intro; left; econstructor; econstructor; eauto.
 right; econstructor; eauto.
Qed.

Lemma access_leaf:forall decI decJ (rp1:rule_pattern I J) (Gamma
                   Gamma':context I J A W) n,
                   access decI decJ rp1 n Gamma=(Some Gamma', true)->
                   isLeaf n rp1.
Proof.
 intros decI decJ rp1; elim rp1; intros.
 simpl in |- *.
 generalize H; simpl in |- *.
 case (eq_nat_dec n n0).
 auto.
 intros.
 discriminate H0.
 simpl in |- *.
 elim (access_com_some _ _ _ _ _ _ _ H1).
 intros Gamma1 H2.
 elim H2; clear H2; intros Gamma2 H2.
 elim H2; clear H2; intros H2 H3.
 elim H3; clear H3; intros.
 elim H3; clear H3; intros.
 left; eauto.
 right; elim H3; eauto.
 simpl in |- *.
 elim (access_diam_some _ _ _ _ _ _ H0).
 intros Gamma0 H1.
 elim H1; eauto.
Qed.

Lemma access_is_sub_cont:forall decI decJ (rp:rule_pattern I J)
                        (Gamma Gamma':context I J A W) n,
                        access decI decJ rp n Gamma=(Some Gamma',true)->
                        is_sub_cont Gamma' Gamma.
intros decI decJ rp; elim rp; intros.
generalize H;clear H;simpl.
case (eq_nat_dec n n0).
 intros.
injection H.
intro;subst;constructor.
discriminate 2.
elim (access_com_some _ _ _ _ _ _ _ H1).
intros Gamma1 H2.
 elim H2; clear H2; intros Gamma2 H2.
 elim H2; clear H2; intros H2 H3.
 elim H3; clear H3; intros;elim H3; clear H3; intros;subst.
constructor.
eauto.
subst;constructor 3.
eauto.
elim (access_diam_some _ _ _ _ _ _ H0).
 intros T H1;decompose [and] H1.
subst;constructor;eauto.
Qed.

Lemma access_leaf_false:forall decI decJ (rp:rule_pattern I J)
                        (Gamma:context I J A W) n,
                        isLeaf n rp -> 
                        access decI decJ rp n Gamma=(None,true)->
                        False.
 intros decI decJ rp; elim rp; intros.
 generalize H0; clear H0; simpl in |- *.
 case (eq_nat_dec n n0).
 intros.
 discriminate H0.
 simpl in H.
 intros.
 elim n1; auto.
 simpl in H1.
 elim (access_com_none _ _ _ _ _ _ _ H2).
 intros Gamma1 H3; elim H3; clear H3; intros Gamma2 H3.
 elim H3; clear H3; intros.
 elim H1; elim H4; intros; eauto.
 simpl in H0.
 elim (access_diam_none _ _ _ _ _ _ H1).
 intros Gamma0 H2; elim H2; clear H2; intros.
 eauto.
Qed.

Lemma access_pathL:forall  decI decJ n (rp1 rp2:rule_pattern I J)
 (i:I)(Gamma0 Gamma1 Gamma2 Gamma' Gamma:context I J A W), 
 access decI decJ rp1 n Gamma=(Some Gamma',true)->
 access decI decJ (pcomma i rp1 rp2) n (Comma i Gamma1 Gamma2)=(Some
 Gamma0 , true)->
 access decI decJ rp1 n Gamma1=(Some Gamma0 , true).

 intros.
 elim (access_com_some _ _ _ _ _ _ _ H0).
 intros Gamma3 H1; elim H1; clear H1; intros Gamma4 H1.
 elim H1; clear H1; intros H1 H2; elim H2; clear H2; intros.
 injection H1; intros; subst.
 tauto.
 injection H1; intros; subst.
 elim H2; clear H2; intros.
 cut (isLeaf n rp1).
 intro.
 elim (access_leaf_false _ _ _ _ _ H4 H3).
 eapply access_leaf; eauto.
Qed.

Lemma access_pathR:forall decI decJ n (rp1 rp2:rule_pattern I J)
 (i:I)(Gamma0 Gamma1 Gamma2 Gamma' Gamma:context I J A W), 
 access decI decJ rp2 n Gamma=(Some Gamma',true)->
 access decI decJ (pcomma i rp1 rp2) n (Comma i Gamma1 Gamma2)=
           (Some Gamma0 , true)->
 access decI decJ rp2 n Gamma2=(Some Gamma0 , true).

 intros.
 elim (access_com_some _ _ _ _ _ _ _ H0).
 intros Gamma3 H1; elim H1; clear H1; intros Gamma4 H1.
 elim H1; clear H1; intros H1 H2; elim H2; clear H2; intros.
 cut (isLeaf n rp2).
 intro.
 elim H2; clear H2; intros.
 elim (access_leaf_false _ _ _ _ _ H3 H4).
 eapply access_leaf; eauto.
 injection H1; intros; subst; tauto.
Qed.
              
Lemma apply_rule_pvar:forall (rp1:rule_pattern I J) decI decJ n (t
                           t':context I J A W),
                           apply_rule (rp1, (pvar n))  decI decJ t=Some t' ->
                          {b:bool |access decI decJ rp1 n t=((Some t'), b)}.
 simpl in |- *.
 intros rp1 decI decJ n t t'.
 case (access decI decJ rp1 n t).
 intros o b; case o.
 intros.
 injection H; intros; subst; econstructor; eauto.
 intro H; discriminate H.
Qed.

Lemma apply_rule_com:forall (rp1 rp2 rp3: rule_pattern I J) decI decJ i
                           (t t':context I J A W),
               apply_rule (rp1, (pcomma i rp2 rp3)) decI decJ t=Some t' ->
               {t1:context I J A W&{t2:context I J A W | t'=(Comma i t1 t2) /\
                             apply_rule (rp1, rp2) decI decJ t =Some t1 /\
                             apply_rule (rp1, rp3) decI decJ t=Some t2}}.
 simpl.
 intros.
 generalize H; clear H.
 case (compile decI decJ rp1 rp3 t).
 case (compile decI decJ rp1 rp2 t).
 intros.
 injection H; econstructor;econstructor.
 split.
 eauto.
 auto.
 intros.
 discriminate H.
 case (compile decI decJ rp1 rp2 t);intros.
 discriminate H.
 discriminate H.
Qed.

Lemma apply_rule_diam: forall (rp1 rp2: rule_pattern I J)decI decJ i
                       (t t':context I J A W),
                      apply_rule (rp1,(pdiam i rp2)) decI decJ t =Some t' ->
                      {t1:context I J A W |t'=TDiamond i t1 /\ apply_rule (rp1, rp2) decI decJ t=Some t1}.
 intros.
 generalize H; clear H; simpl.
 case (compile  decI decJ rp1 rp2 t).
 intros.
 injection H; econstructor.
 split;eauto.
 intro H; discriminate H.
Qed.

Lemma access_same_shape_true:forall decI decJ rp1 opt
                        (n:nat)(Gamma:context I J A W),
                        access decI decJ rp1  n Gamma =(opt, true)->
                        same_shape rp1 Gamma.
 intros decI decJ rp1; elim rp1.
 intros; constructor.
 intros.
 generalize H1; case opt.
 intros.
 elim (access_com_some _ _ _ _ _ _ _ H2).
 clear H2.
 intros Gamma1 H2; elim H2; clear H2; intros Gamma2 H2.
 elim H2; clear H2; intros H2 H3.
 elim H3; clear H3; intro H3; elim H3; clear H3; intros H3 H4.
 rewrite H2.
 constructor; eauto.
 rewrite H2; constructor; eauto.
 intro.
 elim (access_com_none _ _ _ _ _ _ _ H2); clear H2.
 intros Gamma1 H2; elim H2; clear H2; intros Gamma2 H2.
 elim H2; clear H2; intros H2 H3.
 rewrite H2.
 elim H3; intros; constructor; eauto.
 intros.
 generalize H0; clear H0; case opt; intros.
 elim (access_diam_some _ _ _ _ _ _ H0).
 intros Gamma1 H1.
 elim H1; clear H1; intros.
 subst.
 constructor; eauto.
 elim (access_diam_none _ _ _ _ _ _ H0).
 intros Gamma1 H1; elim H1; intros.
 subst; constructor; eapply H; eauto.
Qed.

 
Lemma access_same_shape:forall decI decJ b (n:nat)(Gamma
                          Gamma':context I J A W)rp1,
                          access decI decJ rp1 n Gamma=((Some Gamma'), b) ->
                          same_shape rp1 Gamma.
Proof.
intros.
rewrite (access_some_true _ _ _ _ _ H) in H.
eapply access_same_shape_true; eauto.
Qed.

Lemma apply_rule_same_shape:forall decI decJ  (r1 r2: rule_pattern I J )
                           (t t':context I J A W),
                             (apply_rule (r1 , r2) decI decJ  t)=Some t'->
                             same_shape r1 t.

 intros.
 generalize t' H; clear t' H.
 elim r2.
 intros.
 elim apply_rule_pvar with (1 := H).
 intros.
 eapply access_same_shape; eauto.
 intros.
 elim apply_rule_com with (1:= H1).
 intros.
 elim p; clear p; intros.
 elim p; clear p; intros.
 elim H3; clear H3; intros.
 eauto.
 intros.
 elim apply_rule_diam with (1 := H0).
 intros.
 elim p; intros.
 eauto.
Qed.

Lemma apply_rule_same_shape2:forall decI decJ  (r1 r2: rule_pattern I J )
                           (t t':context I J A W),
                             (apply_rule (r1 , r2) decI decJ  t)=Some t'->
                             same_shape r2 t'.
Proof.
 intros decI decJ r1 r2; elim r2; intros.
 constructor.
 elim (apply_rule_com _ _ _ _ _ _ _ H1).
 intro t1.
 intro H2; elim H2; clear H2; intros t2 H2.
 elim H2; clear H2; intros.
 subst.
 elim H3; intros; constructor; eauto.
 elim (apply_rule_diam _ _ _ _ _ _ H0).
 intros t1 H1; elim H1; clear H1; intros.
 subst.
 constructor; eauto.
Qed.

(* access, apply_rule and par_replace *)
Definition access_par_replace:forall (r:resource W)(Gamma1 Gamma1'
Delta:context I J A W)decI decJ A1 n,
 par_replace (res r A1) Delta Gamma1 Gamma1'->
forall (rp:rule_pattern I J)(Gamma2 Gamma2':context I J A W),
 access decI decJ rp n Gamma1=(Some Gamma2, true)->
 access decI decJ rp n Gamma1'=(Some Gamma2', true)->
 par_replace (res r A1) Delta Gamma2 Gamma2'.

 induction 1.
 intros.
 rewrite H in H0.
 injection H0.
 intro; subst; constructor.
 intros.
 elim (access_res _ _ _ _ _ _ H).
 intros i H1.
 subst.
 generalize H H0; clear H H0; simpl in |- *.
 case (eq_nat_dec i n).
 intros.
 injection H; injection H0.
 intros; subst.
 constructor.
 intros.
 discriminate H.
 intros.
 elim (access_Com_some _ _ _ _ _ _ _ H1).
 intro H3.
 elim H3; clear H3; intros rp1 H3.
 elim H3; clear H3; intros rp2 H3.
 elim H3; clear H3; intros H3 H4.
 elim (access_Com_some _ _ _ _ _ _ _ H2).
 intro H5.
 elim H5; clear H5; intros r1 H5; elim H5; clear H5; intros r2 H5.
 elim H5; clear H5; intros H5 H6.
 rewrite H6 in H4; injection H4; intros; subst.
 elim H3.
 intro H6.
 elim H6; clear H6; intros.
 eapply IHpar_replace1.
 eauto.    
 eapply access_pathL; eauto.
 intro H6; elim H6; clear H6; intros.
 eapply IHpar_replace2.
 eauto.    
 eapply access_pathR; eauto.
 intro H5; elim H5; clear H5; intros; subst.
 discriminate p.
 intro H3; elim H3; clear H3; intros j H3.
 generalize H1 H2; clear H1 H2; subst.
 simpl in |- *.
 case (eq_nat_dec j n).
 intros.
 injection H1; injection H2; intros; subst.
 constructor.
 auto.
 auto.
 intros.
 discriminate H1.
 intros.
 elim (access_diam_TDiam _ _ _ _ _ _ H0).
 intro H2.
 elim H2; clear H2; intros rp1 H2.
 elim H2; clear H2; intros.
 elim (access_diam_TDiam _ _ _ _ _ _ H1).
 intro H4; elim H4; clear H4; intros rp2 H4; elim H4; clear H4; intros.
 rewrite H2 in H4; injection H4; intros; subst.
 eauto.
 intro H5; elim H5; intros k H6; rewrite H6 in H2; discriminate H2.
 intro H2; elim H2; clear H2; intros k H2; subst.
 generalize H0 H1; simpl in |- *.
 case (eq_nat_dec k n).
 intros.
 injection H2; injection H3; intros; subst.
 constructor; auto.
 intros.
 discriminate H2.
Defined.

Definition apply_rule_par_replace:forall ru (r:resource W)(Gamma1 Gamma1'
Gamma2 Gamma2' Delta:context I J A W)decI decJ A1 ,
 par_replace (res r A1) Delta Gamma1 Gamma1'->
 apply_rule ru decI decJ  Gamma1=Some Gamma2->
 apply_rule ru decI decJ Gamma1'=Some Gamma2'->
 par_replace (res r A1) Delta Gamma2 Gamma2'.       

 intro ru; case ru; intros r1 r2; elim r2; intros.
 elim (apply_rule_pvar _ _ _ _ _ H0).
 intros b H2.
 clear H0.
 elim (apply_rule_pvar _ _ _ _ _ H1); clear H1.
 intros b1 H1.
 rewrite (access_some_true _ _ _ _ _ H2) in H2.
 rewrite (access_some_true _ _ _ _ _ H1) in H1.
 eapply access_par_replace; eauto.
 elim (apply_rule_com _ _ _ _ _ _ _ H2).
 clear H2; intros Gamma11 H2.
 elim H2; clear H2; intros Gamma12 H2.
 elim H2; clear H2; intros H2 H4.
 elim H4; clear H4; intros.
 subst.
 elim (apply_rule_com _ _ _ _ _ _ _ H3).
 clear H3; intros Gamma21 H3.
 elim H3; clear H3; intros Gamma22 H3.
 elim H3; clear H3; intros H3 H6.
 elim H6; clear H6; intros.
 subst.
 constructor.
 eapply H;eauto.
 eapply H0 ;eauto.
 elim (apply_rule_diam _ _ _ _ _ _ H1); clear H1.
 intros Gamma11 H3.
 elim H3; clear H3; intros.
 subst.
 subst.
 elim (apply_rule_diam _ _ _ _ _ _ H2); clear H2.
 intros Gamma11' H4; elim H4; clear H4; intros.
 subst; constructor; eauto.
Defined.


Lemma acces_leaf_shape: forall decI decJ (n:nat)(rp:rule_pattern I J)
                     (Gamma:context I J A W),
                      ~isLeaf n rp ->
                      same_shape rp Gamma->
                      access decI decJ rp n Gamma =(None, true).
 induction 2.
 simpl in H.
 simpl in |- *.
 elim (eq_nat_dec n0 n).
 intro.
 absurd (n = n0); auto.
 auto.
 simpl in H.
 elim (isLeaf_dec n r1); elim (isLeaf_dec n r2); intros.
 elim H; tauto.
 elim H; tauto.
 elim H; tauto.
 simpl in |- *.
 case (decI i i).
 generalize IHsame_shape1; generalize IHsame_shape2.
 case (access decI decJ r1 n Gamma1).
 intros o b1; case o.
 case (access decI decJ r2 n Gamma2).
 intros.
 cut ((Some c, b1) = (None, true)).
 intro D; discriminate D.
 auto.
 case b1.
 intros.
 auto.
 intros.
 tauto.
 tauto.
 simpl in H.
 simpl in |- *.
 case (decJ j j);tauto.
Qed.

Lemma acces_isLeaf: forall decI decJ (n:nat)(rp:rule_pattern I J)
                     (Gamma:context I J A W), ~isLeaf n rp ->
                     {b:bool|access decI decJ rp n Gamma=(None, b)}.
 intros  decI decJ n rp.
 elim rp; intros.
 simpl in |- *.
 elim (eq_nat_dec n0 n).
 simpl in H.
 intro.
 absurd (n = n0); auto.
 auto.
 intro; econstructor; eauto.
 simpl in H1.
 simpl in |- *.
 case Gamma.
 intros; econstructor; eauto.
 elim (isLeaf_dec n r).
 intros.
 elim H1; tauto.
 intros; elim (isLeaf_dec n r0).
 intro; elim H1; tauto.
 intros.
 simpl in |- *.
 case (decI i0 i).
 intros.
 elim (H c b).
 intros.
 rewrite p.
 elim x.
 eauto.
 econstructor; eauto.
 intro; econstructor; eauto.
 intros; econstructor; eauto.
 simpl in H0.
 case Gamma; simpl in |- *.
 intros; econstructor; eauto.
 intros; econstructor; eauto.
 intros.
 elim (decJ j j0).
 intro; auto.
 intro; econstructor; eauto.
Qed.



Lemma acces_same_shape:forall decI decJ (rp1:rule_pattern I J)
                      (Gamma:context I J A W) n,
                       allDistinctLeaves rp1 -> isLeaf n rp1 -> 
                       same_shape rp1 Gamma ->
                       {Gamma' : context I J A W | access decI decJ rp1 n Gamma = ((Some Gamma'),true)}.

 intros decI decJ rp1; elim rp1; intros.
 simpl in H0.
 subst.
 econstructor.
 simpl in |- *.
 case (eq_nat_dec n n).
 eauto. 
 tauto.
 elim (sameShapeCom H3).
 intros.
 elim p; intros.
 elim p0; clear p0; intros.
 subst.
 clear p.
 simpl in H1.
 simpl in |- *.
 elim H1; clear H1; intros.
 elim H4; clear H4; intros.
 elim (isLeaf_dec_com H6 H2).
 intros.
 elim a; clear a; intros.
 elim H5; clear H5; intros.
 elim (H _ _ H1 H7 H5).
 intros.
 rewrite p.
 elim (decI i i).
 intro.
 exists x1.
 rewrite (acces_leaf_shape decI decJ _ H8 H9).
 auto.
 tauto.
 intros.
 elim b; clear b; intros.
 elim H5; clear H5; intros.
 elim (H0 _ _ H4 H7 H9).
 intros.
 rewrite p.
 exists x1.
 case (decI i i).
 rewrite (acces_leaf_shape decI decJ _ H8 H5).
 auto.
 tauto.
 simpl in H1.
 simpl in H0.
 elim (sameShapeDiam H2).
 intros.
 elim p; clear p; intros; subst.
 simpl in |- *.
 elim (H _ _ H0 H1 H4).
 intros.
 exists x0.
 case (decJ j j);tauto.
Qed.


Lemma access_sub_cont:forall (decI:eqdec I)(decJ :eqdec
J)(rp:rule_pattern I J)(Gamma:context I J A W) l ,
               allDistinctLeaves rp->
               hasSubContexts rp Gamma l->
               forall n (Delta :context I J A W)i,
               (nth_error (flatten_pattern rp) i)=Some n ->
                access decI decJ rp n Gamma=(Some Delta,true)->
                nth_error l i=Some Delta.
       
Proof.
 induction 2.
 simpl in |- *.
 intro n ; case (eq_nat_dec i n).
 intros H0 Delta0 i0;case i0.
 simpl in |- *.
 injection 2; intros; subst; auto.
 intro n0; case n0; discriminate 1.
 discriminate 3.
 intros.
 simpl in H0.
 elim (nth_error_app _ _ _ H0); intro.
 apply nth_error_fst_app.
 simpl in H; decompose [and] H; clear H.
 elim
 (acces_same_shape decI decJ n H3 (nth_flatten_leaf _ _ H2)
        (same_shape_SubCont H0_)).
 intros.
 eapply IHhasSubContexts1; eauto.   
 eapply access_pathL; eauto.
 decompose [and] H2; clear H2.
 replace i0 with (i0 - length l1 + length l1).
 apply nth_error_scd_app.
 simpl in H; decompose [and] H; clear H.
 elim
  (acces_same_shape decI decJ n H6 (nth_flatten_leaf _ _ H4)
         (same_shape_SubCont H0_0)).
 intros.
 eapply IHhasSubContexts2; eauto.
 rewrite (subCont_length H0_); eauto.    
 eapply access_pathR; eauto.
 rewrite (subCont_length H0_).
 omega.
 intros.
 simpl in H1.
 elim (access_diam_some _ _ _ _ _ _ H2).
 intros Gamma H3; decompose [and] H3; clear H3.
 injection H4; intros; subst; eauto.
Qed.

Lemma access_subCont:forall (decI:eqdec I)(decJ :eqdec
J)(rp:rule_pattern I J)(Gamma:context I J A W) l i,
               allDistinctLeaves rp->
               hasSubContexts rp Gamma l->
               i<length l->
               (exists n:nat,(exists Delta:context I J A W,
               (nth_error (flatten_pattern rp) i)=Some n /\
                access decI decJ rp n Gamma=(Some Delta,true)/\
                nth_error l i=Some Delta)).
       
Proof.
 intros.
 rewrite (subCont_length H0) in H1.
 elim (nth_error_length _ H1).
 intros n H2.
 exists n.
 elim
 (acces_same_shape decI decJ _ H (nth_flatten_leaf _ _ H2)
    (same_shape_SubCont H0)).
 intros Delta H3.
 exists Delta.
 split.
 auto.
 split.
 auto.
 eapply access_sub_cont; eauto.
Qed.
               
Lemma access_eq_apply:forall decI decJ (rp1 rp2:rule_pattern I J)(T1
                      T2 T:context I J A W) (i:nat),
                      apply_rule (rp1 , rp2) decI decJ T1 =Some T2->
                      access decI decJ rp2 i T2=(Some T,true)->
                      access decI decJ rp1 i T1=(Some T,true).
Proof.
 intros decI decJ rp1 rp2; elim rp2.
 simpl in |- *.
 intros n T1 T2 T i.
 case (eq_nat_dec n i).
 intro; subst.
 elim (access_dec rp1 decI decJ i T1).
 intro H; elim H.
 clear H; intros T' H.
 rewrite H.
 injection 1; intros; subst; auto.
 intro H; elim H; clear H; intros b H; rewrite H.
 discriminate 1.
 discriminate 3.
 intros.
 elim (apply_rule_com _ _ _ _ _ _ _ H1).
 intros T' H3.
 elim H3; clear H3; intros T1' H3.
 elim H3; clear H3; intros H3 H4; elim H4; clear H4; intros H4 H5.
 subst.
 elim (access_com_some _ _ _ _ _ _ _ H2).
 intros Gamma1 H3.
 elim H3; clear H3; intros Gamma2 H3.
 elim H3; clear H3; intro H3.
 intro H6; elim H6; clear H6; intro H6; elim H6; clear H6; intros H6 H7.
 injection H3; intros; subst.
 eauto.
 injection H3; intros; subst; eauto.
 intros.
 elim (apply_rule_diam _ _ _ _ _ _ H0).
 intros T' H2; elim H2; clear H2; intros.
 subst.
 elim (access_diam_some _ _ _ _ _ _ H1).
 intros Gamma H2; elim H2; clear H2; intros.
 injection H2; intros; subst; eauto.
Qed.


Lemma permut_sub_cont:forall decI decJ (rp1 rp2:rule_pattern I J)(T1
                      T2 :context I J A W)l1 l2,
                         allDistinctLeaves rp1->
                         allDistinctLeaves rp2->
                        permut (flatten_pattern rp1) (flatten_pattern rp2)->
                        apply_rule  (rp1 , rp2) decI decJ T1 =Some T2->
                        hasSubContexts rp1 T1 l1->
                        hasSubContexts rp2 T2 l2->
                        permut l1 l2.  
Proof.
 
 intros.
 pose (f := fun n : nat => let (p1, _) := access decI decJ rp1 n T1 in p1).
 cut (permut (map f (flatten_pattern rp1)) (map f (flatten_pattern rp2))).
 intro.
 eapply permut_extract.
 eexact H5. 
 apply extract_forall.
 rewrite (subCont_length H3).
 rewrite map_length; auto.
 intros.
 assert (i < length l1).
 eapply nth_error_some_length.
 eauto.
 elim (access_subCont decI decJ H H3 H7).
 intros n H8; decompose [ex] H8.
 clear H8.
 decompose [and] H9; clear H9.
 rewrite (nth_map f _ _ H8).
 unfold f in |- *; simpl in |- *.
 rewrite H11.
 rewrite H12 in H6; injection H6.
 intro; subst; auto. 
 apply extract_forall.
 rewrite (subCont_length H4).
 rewrite map_length; auto.
 intros.
 assert (i < length l2).
 eapply nth_error_some_length; eauto.
 elim (access_subCont decI decJ H0 H4 H7); intros.
 decompose [ex and] H8; clear H8.
 rewrite (nth_map f _ _ H10).
 unfold f in |- *; simpl in |- *.
 rewrite (access_eq_apply _ _ _ _ _ _ H2 H9).
 rewrite H12 in H6; injection H6; intro; subst; auto.
 apply map_permut; auto.
Qed.



End props.
