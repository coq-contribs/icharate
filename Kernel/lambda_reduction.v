(********************************************)
(*                          Icharate Toolkit                       *)
(*                            Houda ANOUN                       *)
(*                            2004 -2005                            *)
(*                              LaBRI                                   *)
(********************************************)



Set Implicit Arguments.
Require Export lambda_bruijn.
Section beta.
Variable X:Set.

(* BETA REDUCTION *)

(* some useful functions *)

Fixpoint substVar (i:nat)(t1 t2:lambda_terms X){struct t1}:lambda_terms X:=
match t1 with 
| num  n => match (lt_eq_lt_dec n i) with 
                 | inleft (left _) => num X  n   (* n<i*)
                 | inleft (right _) => lift_lambda t2 i     (* n=i *)              
                 | inright _ => (num  X (pred n)) (* n > i*)
               end
| ress  w => ress  w
|hyps k s=>hyps X k s
| appl  l1 l2 => appl  (substVar i l1 t2) (substVar i l2 t2)
| abs ty l => abs ty (substVar (S i) l t2)
| twoL l1 l2 => twoL  (substVar i l1 t2) (substVar i l2 t2)
| pi1  l => pi1  (substVar i l t2)
| pi2 l => pi2  (substVar i l t2)
| box l => box  (substVar i l t2)
| debox  l => debox  (substVar i l t2)
| diam  l =>  diam  (substVar i l t2)
| dediam  l =>  dediam  (substVar i l t2)
end.

Definition substLamb (t1 t2 :lambda_terms X):lambda_terms X :=
(substVar O t1 t2).

(* definition of a confluent beta reduction *)
Inductive beta_one_step:lambda_terms X ->lambda_terms X -> Prop:=
| absRed : forall (ty1 :semType)(l1 l2:lambda_terms X), 
                                   beta_one_step (appl (abs ty1 l1) l2) (substLamb l1 l2)
| pi1Red: forall (l1 l2:lambda_terms X), beta_one_step (pi1  (twoL  l1 l2)) l1
| pi2Red: forall (l1 l2:lambda_terms X), beta_one_step (pi2 (twoL  l1 l2)) l2
|diamDediamRed: forall (l:lambda_terms X), beta_one_step (dediam (diam  l)) l 
|boxDeboxRed:forall (l:lambda_terms X), beta_one_step (debox  (box l)) l
| applRed1:forall (l1 l2 l3:lambda_terms X), beta_one_step l1 l2 -> 
                                     beta_one_step (appl  l1 l3) (appl  l2 l3)
| applRed2:forall (l1 l2 l3:lambda_terms X), beta_one_step l1 l2 -> 
                                     beta_one_step (appl l3 l1) (appl l3 l2)
| absRed2:forall (ty :semType)(l1 l2:lambda_terms X), beta_one_step l1 l2 ->
                                               beta_one_step (abs ty l1) (abs ty l2)
| twoLRed1:forall (l1 l2 l3:lambda_terms X), beta_one_step l1 l2 -> 
                                     beta_one_step (twoL  l1 l3) (twoL  l2 l3)
| twoLRed2:forall (l1 l2 l3:lambda_terms X), beta_one_step l1 l2 -> 
                                     beta_one_step (twoL  l3 l1) (twoL  l3 l2)
| piRed1:forall (l1 l2:lambda_terms X), beta_one_step l1 l2 -> 
                                beta_one_step (pi1 l1) (pi1  l2)
| piRed2:forall (l1 l2:lambda_terms X), beta_one_step l1 l2 -> 
                                beta_one_step (pi2  l1) (pi2  l2)
| boxRed:forall (l1 l2:lambda_terms X), beta_one_step l1 l2 -> 
                                 beta_one_step (box  l1) (box  l2)
| deboxRed:forall (l1 l2:lambda_terms X), beta_one_step l1 l2 -> 
                                  beta_one_step (debox  l1) (debox  l2)
| diamRed:forall (l1 l2:lambda_terms X), beta_one_step l1 l2 ->
                                  beta_one_step (diam  l1) (diam  l2)
| dediamRed:forall (l1 l2:lambda_terms X), beta_one_step l1 l2 ->
                                    beta_one_step (dediam l1) (dediam l2).


(* functions that reduces redexes within a term *)
Fixpoint  reduceAll(l:lambda_terms X) :lambda_terms X :=
match l with 
|hyps k s=> hyps X k s
|num n => num  X n
|ress  r => ress  r
| appl l1 l2 =>match l1 with 
                  |abs ty1 t1 => substVar 0 t1 l2
                  | others => appl (reduceAll l1) (reduceAll l2)
                 end
| abs ty l1 =>abs ty (reduceAll l1)
| twoL  l1 l2 =>twoL (reduceAll l1)(reduceAll l2)
| pi1  l1 => match l1 with 
              | twoL  t1 t2 => (reduceAll t1)
              | others =>pi1  (reduceAll l1)
             end
|pi2 l1 => match l1 with 
              | twoL t1 t2 => (reduceAll t2)
              | others =>pi2  (reduceAll l1)
             end
|box  l1 => box (reduceAll l1)
|debox  l1=> match l1 with 
              |box  t1 =>(reduceAll t1)
              |others => debox  (reduceAll l1)
             end
|diam  l1=>diam (reduceAll l1)
|dediam  l1=> match l1 with 
              |diam  t1 =>(reduceAll t1)
              |others => dediam  (reduceAll l1)
             end
end.


(* reflexive transitive closure of beta-reduction *)
Inductive beta_reduction:lambda_terms X ->lambda_terms X -> Prop:=
|betaRefl:forall (l:lambda_terms X), beta_reduction l l
|betaTrans:forall (l1 l2 l3:lambda_terms X), 
                                      beta_one_step l1 l2 ->
                                      beta_reduction  l2 l3 ->
                                      beta_reduction  l1 l3.


(* some well known properties *)

Lemma simplBetaToRefTrans:forall(l1 l2:lambda_terms X),
                                                beta_one_step l1 l2->
                                                beta_reduction l1 l2.
Proof.
 intros.
 eapply betaTrans;[eauto|constructor 1].
Qed.

Lemma betaTransitive:forall(l1 l2 l3:lambda_terms X), 
                      beta_reduction l1 l2 ->
                      beta_reduction l2 l3 ->
                      beta_reduction l1 l3.
 induction 1.
 auto.
 intro.
 apply betaTrans with l2;auto.
Qed.

(* monotony lemmas*)
Lemma beta_app_mono1:forall (l0 l1 l2:lambda_terms X),
                  beta_reduction l0 l1 ->
                  beta_reduction (appl l0 l2) (appl l1 l2).
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  econstructor.
  eauto.
  auto.
Qed.
Lemma beta_app_mono2:forall (l0 l1 l2:lambda_terms X),
                  beta_reduction l0 l1 ->
                  beta_reduction (appl l2 l0) (appl  l2 l1).
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  eapply applRed2; eauto.
  auto.
Qed.

Lemma beta_app_mono:forall (l1 l2 l3 l4:lambda_terms X),
                                        beta_reduction l1 l2-> 
                                        beta_reduction l3 l4->
                                        beta_reduction (appl l1 l3)(appl l2 l4).
Proof.
intros.
eapply betaTransitive.
eapply beta_app_mono1.
eauto.
eapply beta_app_mono2.
auto.
Qed.

Lemma beta_abs_mono:forall (ty:semType)(l l':lambda_terms X),
                                            beta_reduction l l'-> 
                                            beta_reduction (abs ty l) (abs ty l').
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  econstructor.
  eauto.
  auto.
Qed.

Lemma beta_box_mono:forall (l l':lambda_terms X),
                                        beta_reduction l l'-> 
                                        beta_reduction (box  l) (box  l').
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  econstructor.
  eauto.
  auto.
Qed.

Lemma beta_pi1_mono:forall (l l':lambda_terms X),
                                        beta_reduction l l'-> 
                                        beta_reduction (pi1  l) (pi1 l').
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  econstructor.
  eauto.
  auto.
Qed.

Lemma beta_pi2_mono:forall (l l':lambda_terms X),
                                         beta_reduction l l'-> 
                                         beta_reduction (pi2  l) (pi2  l').
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  econstructor.
  eauto.
  auto.
Qed.

Lemma beta_debox_mono:forall (l l':lambda_terms X),
                                           beta_reduction l l'-> 
                                          beta_reduction (debox  l) (debox  l').
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  econstructor.
  eauto.
  auto.
Qed.

Lemma beta_diam_mono:forall (l l':lambda_terms X),
                                          beta_reduction l l'-> 
                                          beta_reduction (diam  l) (diam  l').
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  econstructor.
  eauto.
  auto.
Qed.

Lemma beta_dediam_mono:forall (l l':lambda_terms X),
                                           beta_reduction l l'-> 
                                           beta_reduction (dediam l) (dediam l').
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  econstructor.
  eauto.
  auto.
Qed.

Lemma beta_twoL_mono1:forall (l0 l1 l2:lambda_terms X),
                  beta_reduction l0 l1 ->
                  beta_reduction (twoL  l0 l2) (twoL  l1 l2).
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  econstructor.
  eauto.
  auto.
Qed.

Lemma beta_twoL_mono2:forall (l0 l1 l2:lambda_terms X),
                  beta_reduction l0 l1 ->
                  beta_reduction (twoL  l2 l0) (twoL  l2 l1).
Proof.
  induction 1.
  constructor 1.
  econstructor 2.
  eapply twoLRed2.
  eauto.
  auto.
Qed.

Lemma beta_twoL_mono:forall(l1 l2 l3 l4:lambda_terms X),
                                        beta_reduction l1 l2->
                                        beta_reduction l3 l4->
                                        beta_reduction (twoL l1 l3)(twoL l2 l4).
Proof.
intros.
eapply betaTransitive.
apply beta_twoL_mono1.
eauto.
apply beta_twoL_mono2.
eauto.
Qed.

(* proof that \-/ term, term --->* (reduceAll term) *)
(* using well founded induction *)

(* definition of sub-term predicate *)
Inductive isSubTerm (l:lambda_terms X): lambda_terms X -> Prop:=
| sameT: isSubTerm l l
| subAppl1: forall (l1 l2:lambda_terms X), isSubTerm l l1 ->
                                    isSubTerm l (appl  l1 l2)
| subAppl2 : forall (l1 l2:lambda_terms X), isSubTerm l l2 ->
                                     isSubTerm l (appl l1 l2)
| subAbs:  forall (l1 :lambda_terms X)(ty:semType), isSubTerm l l1 ->
                                             isSubTerm l (abs ty l1)
| subTwoL1:  forall (l1 l2:lambda_terms X), isSubTerm l l1 ->
                                     isSubTerm l (twoL l1 l2)
|subTwoL2:  forall (l1 l2:lambda_terms X), isSubTerm l l2 ->
                                    isSubTerm l (twoL  l1 l2)
|subPi1: forall (l1 :lambda_terms X), isSubTerm l l1 ->
                               isSubTerm l (pi1 l1)
| subPi2: forall (l1 :lambda_terms X), isSubTerm l l1 ->
                               isSubTerm l (pi2  l1)
| subBox : forall (l1 :lambda_terms X), isSubTerm l l1 ->
                                 isSubTerm l (box  l1)
| subDebox:  forall (l1 :lambda_terms X), isSubTerm l l1 ->
                                   isSubTerm l (debox  l1)
|subDiam :  forall (l1 :lambda_terms X), isSubTerm l l1 ->
                                  isSubTerm l (diam  l1)
| subDediam:  forall (l1 :lambda_terms X), isSubTerm l l1 ->
                                    isSubTerm l (dediam l1).

(* strict sub-term predicate *)

(* definition of sub-term predicate *)
Inductive isStrictSubTerm (l:lambda_terms X): lambda_terms X -> Prop:=
| ssubAppl1: forall (l1 l2:lambda_terms X), isSubTerm l l1 ->
                                    isStrictSubTerm l (appl  l1 l2)
| ssubAppl2 : forall (l1 l2:lambda_terms X), isSubTerm l l2 ->
                                     isStrictSubTerm l (appl l1 l2)
| ssubAbs:  forall (l1 :lambda_terms X)(ty:semType), 
                                    isSubTerm l l1 ->
                                    isStrictSubTerm l (abs ty l1)
| ssubTwoL1:  forall (l1 l2:lambda_terms X), isSubTerm l l1 ->
                                    isStrictSubTerm l (twoL l1 l2)
|ssubTwoL2:  forall (l1 l2:lambda_terms X), isSubTerm l l2 ->
                                   isStrictSubTerm l (twoL  l1 l2)
|ssubPi1: forall (l1 :lambda_terms X), isSubTerm l l1 ->
                               isStrictSubTerm l (pi1 l1)
| ssubPi2: forall (l1 :lambda_terms X), isSubTerm l l1 ->
                               isStrictSubTerm l (pi2  l1)
| ssubBox : forall (l1 :lambda_terms X), isSubTerm l l1 ->
                                 isStrictSubTerm l (box  l1)
| ssubDebox:  forall (l1 :lambda_terms X), isSubTerm l l1 ->
                                 isStrictSubTerm l (debox  l1)
|ssubDiam :  forall (l1 :lambda_terms X), isSubTerm l l1 ->
                                isStrictSubTerm l (diam  l1)
| ssubDediam:  forall (l1 :lambda_terms X), isSubTerm l l1 ->
                                    isStrictSubTerm l (dediam l1).

Lemma sub_eq_strict:forall (l1 l2:lambda_terms X),
                                        isSubTerm l1 l2 ->
                                        l1 = l2 \/ isStrictSubTerm l1 l2.
Proof. 
 induction 1.                  
 auto.
 Admitted.

(* isStrictSubTerm is a well founded relation *)
Lemma isWFStrictSub:well_founded  isStrictSubTerm.
 Proof.
 unfold well_founded in |- *.
 intro l; elim l.
 intro; constructor.
 inversion 1.
intro;constructor;inversion 1.
intro;constructor;inversion 1. 
intros.
constructor.
inversion 1.
elim (sub_eq_strict H3).
intro;subst;auto.
intros;apply Acc_inv with l0;auto.
elim (sub_eq_strict H3).
intro;subst;auto.
intro;apply Acc_inv with l1;auto.
intros;constructor;inversion 1;intros.
elim (sub_eq_strict H2);[intro;subst;auto|intro;apply Acc_inv with l0;auto].
intros;constructor;inversion 1.

Admitted.

(* some tactics *)
Ltac pi1_tac H:=eapply betaTransitive; [eapply beta_pi1_mono;
apply H;repeat constructor|constructor 1].

Ltac pi2_tac H:=eapply betaTransitive; [eapply beta_pi2_mono;
apply H;repeat constructor|constructor 1].

Ltac debox_tac H:=eapply betaTransitive; [eapply beta_debox_mono;
apply H;repeat constructor|constructor 1].

Ltac dediam_tac H :=eapply betaTransitive; [eapply beta_dediam_mono;
apply H;repeat constructor|constructor 1].

Lemma reduceAllWellFound: forall (l2 :lambda_terms X), 
                          (forall l1 ,(isStrictSubTerm l1 l2) ->
                                      beta_reduction l1 (reduceAll l1))->
                           beta_reduction l2 (reduceAll l2).

Proof.
 intro l2; elim l2; intros. 
 simpl; constructor.
 simpl; constructor.
 simpl;constructor.
 generalize H H1; elim l; intros.
simpl;apply beta_app_mono2.
apply H3;constructor 2;constructor.
simpl;apply beta_app_mono2.
apply H3;constructor 2;constructor.
simpl;apply beta_app_mono2.
apply H3;constructor 2;constructor.
apply betaTransitive with (appl (reduceAll (appl l1 l3)) (reduceAll l0)).
eapply beta_app_mono;apply H5.
repeat constructor.
constructor 2;constructor.
constructor 1.
simpl.
econstructor.
constructor 1.
constructor 1.
simpl. 
apply beta_app_mono.
apply beta_twoL_mono.
apply H5;repeat constructor.
apply H5;constructor;constructor 6;constructor.
apply H5;constructor 2;constructor.
eapply betaTransitive.
apply beta_app_mono1.
apply H4;repeat constructor.
eapply betaTransitive.
apply beta_app_mono2.
apply H4;constructor 2;constructor.
constructor 1.
eapply betaTransitive.
apply beta_app_mono1.
apply H4;repeat constructor.
eapply betaTransitive.
apply beta_app_mono2.
apply H4;constructor 2;constructor.
constructor 1.
simpl.
apply beta_app_mono.
apply beta_box_mono.
apply H4;repeat constructor.
apply H4;constructor 2;constructor.
eapply betaTransitive.
apply beta_app_mono.
apply H4;repeat constructor.
apply H4;constructor 2;constructor.
constructor 1.
simpl.
apply beta_app_mono.
apply beta_diam_mono.
apply H4;repeat constructor.
apply H4;constructor 2;constructor.
eapply betaTransitive.
apply beta_app_mono.
apply H4;repeat constructor.
apply H4;constructor 2;constructor.
constructor 1.
simpl.
apply beta_abs_mono.
apply H0;repeat constructor.
simpl;apply beta_twoL_mono.
apply H1;repeat constructor.
apply H1;constructor 5;constructor.
generalize H0;clear H0;elim l;intros.
pi1_tac H0.
pi1_tac H0.
pi1_tac H0.
pi1_tac H2.
pi1_tac H1.
simpl.
econstructor.
constructor.
apply H2;repeat constructor.
pi1_tac H1.
pi1_tac H1.
pi1_tac H1.
pi1_tac H1.
pi1_tac H1.
pi1_tac H1.
generalize H0;clear H0;elim l;intros.
pi2_tac H0.
pi2_tac H0.
pi2_tac H0.
pi2_tac H2.
pi2_tac H1.
simpl;
econstructor.
constructor.
apply H2;constructor; constructor 6;constructor.
pi2_tac H1.
pi2_tac H1.
pi2_tac H1.
pi2_tac H1.
pi2_tac H1.
pi2_tac H1.
simpl;apply beta_box_mono.
apply H0;repeat constructor.
generalize H0;clear H0;elim l;intros;
solve[debox_tac H0|debox_tac H1|debox_tac H2|
(simpl;econstructor;[constructor|apply H1;repeat constructor])].
simpl;apply beta_diam_mono;apply H0;repeat constructor.
generalize H0;clear H0;elim l;intros;
solve[dediam_tac H0|dediam_tac H1|dediam_tac H2|
(simpl;econstructor;[constructor|apply H1;repeat constructor])].
Qed.

Lemma reduceAllBeta:forall (l:lambda_terms X), 
      beta_reduction l (reduceAll l).

Proof.
 exact
 (well_founded_ind isWFStrictSub (fun l => beta_reduction l (reduceAll l))
    reduceAllWellFound).
Qed.


(* definition of normal form *)
Definition normalForm (l:lambda_terms X):Prop:=
forall (l1:lambda_terms X), beta_one_step l l1 ->False. 


Fixpoint containsNoRedex (l:lambda_terms X) :Prop:=
match l with 
| num  _ => True
| ress  _ => True
|hyps _ _=> True
| appl  l1 l2 =>match l1 with 
                      | abs _ _ => False
                      | others => containsNoRedex l1 /\ containsNoRedex l2
                  end
| abs _ l1 => containsNoRedex l1
| twoL l1 l2=>containsNoRedex l1 /\ containsNoRedex l2
| pi1 l1 => match l1 with 
            | twoL  _ _ =>  False
            | others => containsNoRedex l1
            end
| pi2 l1 => match l1 with 
           | twoL  _ _ =>  False
           | others => containsNoRedex l1
            end
| box  l1 => containsNoRedex l1
| debox  l1 => match l1 with 
                | box _ => False
                | others => containsNoRedex l1
            end
| diam  l1 => containsNoRedex l1
| dediam  l1 => match l1 with 
                | diam  _ => False
                |others =>containsNoRedex l1
              end
end.

Lemma redexAppl:forall (l1 l2:lambda_terms X), 
                  containsNoRedex (appl l1 l2) -> 
                  containsNoRedex l1 /\ containsNoRedex l2.
Proof.
 intro l1; elim l1; simpl in |- *; auto.
 tauto.
Qed.


Lemma redexPi1:forall (l1:lambda_terms X) , 
                  containsNoRedex (pi1  l1) -> 
                  containsNoRedex l1.
Proof.
 intro l1; elim l1; simpl in |- *; auto.
 tauto.
Qed.

Lemma redexPi2:forall (l1:lambda_terms X) , 
                  containsNoRedex (pi2 l1) -> 
                  containsNoRedex l1.
Proof.
 intro l1; elim l1; simpl in |- *; auto.
 tauto.
Qed.

Lemma redexDebox:forall (l1:lambda_terms X) , 
                  containsNoRedex (debox l1) -> 
                  containsNoRedex l1.
Proof.
 intro l1; elim l1; simpl in |- *; auto.
 tauto.
Qed.

Lemma redexDediam:forall (l1:lambda_terms X) , 
                  containsNoRedex (dediam  l1) -> 
                  containsNoRedex l1.
Proof.
 intro l1; elim l1; simpl in |- *; auto.
 tauto.
Qed.


Lemma redexNF:forall (l:lambda_terms X), 
                     containsNoRedex l -> 
                     normalForm l.
Proof.
 intro l; elim l; intros; unfold normalForm in |- *.
 intros l1 H1; inversion H1.
 intros l1 H1; inversion H1.
 intros l1 H1;inversion H1.
 intros.
 inversion H2.
 rewrite <- H4 in H1; simpl in H1; auto.
 elim (redexAppl  _ _ H1).
 intros.
 absurd (normalForm l0).
 red in |- *; unfold normalForm in |- *; intros.
 exact (H9 l4 H6).
 auto.
 elim (redexAppl  _ _ H1); intros.
 absurd (normalForm l1).
 red in |- *; unfold normalForm in |- *; intros.
 exact (H9 _ H6).
 auto.
 intros.
 inversion H1.
 simpl in H0.
 absurd (normalForm l0).
 red in |- *; unfold normalForm in |- *; intros.
 exact (H6 l3 H5).
 auto.
 intros.
 simpl in H1.
 inversion H2.
 absurd (normalForm l0).
 red in |- *; unfold normalForm in |- *; intros.
 exact (H7 l4 H6).
 elim H1; intros; auto.
 absurd (normalForm l1).
 red in |- *; unfold normalForm in |- *; intros.
 exact (H7 l4 H6).
 elim H1; auto.
 intros.
 inversion H1.
 rewrite <- H3 in H0; simpl in H0; auto.
 absurd (normalForm l0).
 red in |- *; unfold normalForm in |- *; intros.
 exact (H5 l3 H3).
 apply H.
 apply redexPi1; auto.
 intros.
 inversion H1.
 rewrite <- H3 in H0; simpl in H0; auto.
 absurd (normalForm l0).
 red in |- *; unfold normalForm in |- *; intros.
 exact (H5 l3 H3).
 apply H; apply redexPi2 ; auto.
 intros.
 inversion H1.
 absurd (normalForm l0).
 red in |- *; unfold normalForm in |- *; intros.
 exact (H5 l3 H3).
 simpl in H0; auto.
 intros.
 inversion H1.
 rewrite <- H3 in H0; simpl in H0; auto.
 absurd (normalForm l0).
 red in |- *; unfold normalForm in |- *; intros.
 exact (H5 l3 H3).
 apply H; apply redexDebox ; auto.
 intros.
 inversion H1.
 simpl in H0.
 unfold normalForm in H.
 exact (H H0 l3 H3).
 intros.
 inversion H1.
 rewrite <- H3 in H0.
 simpl in H0; auto.
 absurd (normalForm l0).
 red in |- *; unfold normalForm in |- *; intros.
 exact (H5 l3 H3).
 apply H.
 apply redexDediam ; auto.
Qed.


Lemma beta_normal :forall (l l1:lambda_terms X), 
                                 beta_reduction l l1 -> 
                                 normalForm l->
                                  l=l1.
Proof.
 induction 1;intros.
 auto.
 unfold normalForm in H1.
 elim (H1 l2 H).
Qed. 

Inductive hasNormalForm (l:lambda_terms X):Set:=
hasNF1: forall(l':lambda_terms X),
                           beta_reduction l l' -> 
                           normalForm l' ->
                           hasNormalForm l.

Definition extractNF (l:lambda_terms X)
(p:hasNormalForm l) :lambda_terms X:=
match p with 
|hasNF1 l' red nf => l'
end.



Lemma normalFormExtr:forall (l:lambda_terms X)
                        (p:hasNormalForm l), 
                         normalForm (extractNF p).
Proof.
 intros l p; elim p.
 intros.
 simpl in |- *; auto.
Qed.

Lemma betaExtract:forall (l:lambda_terms X) (p:hasNormalForm l),
                       beta_reduction l (extractNF p).
Proof.
 intros l p; elim p.
 intros.
 simpl in |- *; auto.
Qed.
End beta.
(*some useful tactics *)
(* used when ?l' is  a meta-variable representing the normal form
 of ?l *)
Ltac compute_nf := match goal with 
|  |-(beta_reduction ?l ?l') =>
         first [apply betaTransitive with (reduceAll l);
             [constructor 1|constructor 1] |
                apply betaTransitive with (reduceAll l); 
             [apply reduceAllBeta | compute_nf]]
| |- _ => idtac
end.

(* to prove that a term is a normal form *)
Ltac nfTac:=match goal with 
|- (normalForm ?l) => apply redexNF;simpl;tauto
end.

(* to solve goals of the form (hasNormalForm l) *)
Ltac solve_nf:=econstructor; [compute_nf | nfTac].
