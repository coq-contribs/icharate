(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                              LaBRI                                   *)
(************************************************************************)

Require Export lambda_bruijn.
Set Implicit Arguments.
Parameter E:Set.
Parameter intent:Type ->Type.
Notation "'s->' ty":=(intent ty)(at level 40).

(* it can be seen as the application from all possible worlds to the 
 data structure *)
Parameters box_coq diam_coq:forall (A:Type), A->intent A.
Parameters debox_coq dediam_coq:forall (A:Type), intent A->A.

(* interpretation of semType *)

Fixpoint trans_type (st:semType):Type:=
match st with 
|e=>E
|t=> Prop
|funAppli t1 t2=> (trans_type t1)->(trans_type t2)
|cartProd t1 t2=>prodT (trans_type t1)(trans_type t2)
|intention t1=>intent (trans_type t1)
end.


Inductive type_obj:Type:=
|obj1:forall (A:Type),A-> type_obj.

(* generalization of list for sort type *)
Inductive listT (A:Type):Type:=
|nilT:listT A
|consT:A->listT A->listT A.

Implicit Arguments nilT [A].

Inductive trans_env:list semType->listT (type_obj)->
                          Type:=
|nil_trans:trans_env nil nilT 
|cons_trans:forall l1 l2 a1 (x1:trans_type a1),
                             trans_env  l1 l2->
                             trans_env  (a1::l1)(consT (obj1 x1)l2).

Inductive optionT (A : Type) : Type:=
  SomeT : A -> optionT A | NoneT : optionT A.

Implicit Arguments NoneT [A].

Fixpoint nth_error_T (A:Type)(l:listT A)(n:nat){struct l}:optionT A:=
match l, n with
|nilT, _ => NoneT
|consT a1 l1, 0=>SomeT a1
|consT a1 l1, (S m)=>nth_error_T l1 m
end.

Definition trans_env_nth:forall (e:list semType)(lit:listT type_obj),
                       trans_env e lit->
                       forall n t,  nth_error e n=Some t->
                        (sigT (fun x1:trans_type t=> nth_error_T lit n=SomeT
                         (obj1 x1))). 
 induction 1.
 intro n; case n; simpl in |- *.
 discriminate 1.
 discriminate 2.
 intro n; case n; simpl in |- *.
 injection 1; intros; subst; econstructor; eauto.
 auto.
Defined.

Section coq_terms.
Variable  X:Set.
Variable getSemTypeX : X->semType.
Variable consts:forall (x:X), trans_type (getSemTypeX x).


Definition trans_lamb:forall l env t, 
   isWellTyped getSemTypeX env l t-> 
   no_hyps_inside l-> 
  forall (vars:listT type_obj), 
       trans_env env vars->
       (trans_type t).
 induction 1; intros.
 elim (trans_env_nth X0 _ e).
 intros x H2; exact x.
 exact (consts x).
 simpl in H.
 elim H.
 simpl in H1.
 decompose [and] H1.
 simpl in IHisWellTyped1.
 exact (IHisWellTyped1 H2 _ X0 (IHisWellTyped2 H3 _ X0)).
 simpl in |- *.
 simpl in H0; generalize H H0 IHisWellTyped;clear H H0 IHisWellTyped.
 case t2.
 intros H H0 H1 x.
 apply (H1 H0 (consT (obj1 x) vars)).
 apply cons_trans;auto.
 intros H H0 H1 P.
 apply (H1 H0 (consT (obj1 P) vars)).
 apply cons_trans;auto.
 intros s s0 H0 H1 H2 Q.
apply (H2 H1 (consT (obj1 Q) vars)).
 constructor;auto.
 intros s s0 H0 H1 H2 C.
apply (H2 H1 (consT (obj1 C) vars)).
 constructor;auto.
 intros s H0 H1 H2 T.
apply (H2 H1 (consT (obj1 T) vars)).
 constructor;auto.
 simpl in |- *.
 simpl in H1.
 decompose [and] H1.
 constructor.
 exact (IHisWellTyped1 H2 _ X0).
 exact (IHisWellTyped2 H3 _ X0).
 simpl in H0.
 simpl in IHisWellTyped.
 exact (fstT (IHisWellTyped H0 _ X0)).
 simpl in H0; simpl in IHisWellTyped.
 exact (sndT (IHisWellTyped H0 _ X0)).
 simpl in |- *.
 simpl in H0.
 exact (box_coq (IHisWellTyped H0 _ X0)).
 simpl in H0.
 simpl in IHisWellTyped.
 exact (debox_coq (IHisWellTyped H0 _ X0)).
 simpl in |- *; simpl in H0.
 exact (diam_coq (IHisWellTyped H0 _ X0)).
 simpl in H0.
 simpl in IHisWellTyped.
 exact (dediam_coq (IHisWellTyped H0 _ X0)).
Defined.

	    
Definition trans_lamb0:forall l env t, 
   type_check getSemTypeX env l=Some t-> 
   no_hyps_inside l-> 
  forall (vars:listT type_obj), 
       trans_env env vars->
       (trans_type t).

 intro l; elim l; intros.
 simpl in H; elim (trans_env_nth X0 _ H).
 intros x H2; exact x.
 simpl in H.
 injection H; intro; subst.
 exact (consts x).
 simpl in H0; tauto.
 elim (getTypeAppl _ _ _ _ H).
 intros x H1; decompose [and] H1; clear H1.
 generalize (X0 env _ H2); clear X0; simpl in |- *; intro X0.
 simpl in H0; decompose [and] H0; clear H0.
 exact (X0 H1 _ X2 (X1 _ _ H3 H4 _ X2)).
 simpl in H0.
 elim (getTypeAbs _ _ _ _ H).
 intros x H3; decompose [and] H3; clear H3; subst.
 simpl in |- *; intro.
 apply (X0 _ _ H2 H0 (consT (obj1 X2) vars)).
 constructor; auto.
 simpl in H0; decompose [and] H0; clear H0.
 elim (getTypeTwoL _ _ _ _ H).
 intros x H3; decompose [and sig] H3; clear H3.
 subst.
 simpl in |- *.
 split.
 exact (X0 env x H5 H1 _ X2).
 exact (X1 env _ H6 H2 _ X2).
 elim (getTypePi1 _ _ _ H).
 intros x H3.
 simpl in H0.
 exact (fstT (X0 _ _ H3 H0 _ X1)).
 simpl in H0; elim (getTypePi2 _ _ _ H); intros x H3.
 exact (sndT (X0 _ _ H3 H0 _ X1)).
 elim (getTypeBox _ _ _ H).
 intros x H3; decompose [and] H3; clear H3; subst.
 simpl in H0.
 exact (box_coq (X0 _ _ H2 H0 _ X1)).
 simpl in H0.
 exact (debox_coq (X0 _ _ (getTypeDebox _ _ _ H) H0 _ X1)).
 simpl in H0.
 elim (getTypeDiam _ _ _ H).
 intros x H3; decompose [and] H3; clear H3.
 subst.
 simpl in |- *.
 exact (diam_coq (X0 _ _ H2 H0 _ X1)).
 simpl in H0.
 exact (dediam_coq (X0 _ _ (getTypeDediam _ _ _ H) H0 _ X1)).
Defined.

Definition pretty_printer0 (l:lambda_terms X)(ty:semType)
(p:type_check getSemTypeX nil l =Some ty) (q:no_hyps_inside l) :(trans_type ty):=
(trans_lamb0 _ p q (nil_trans)).


(*
(* tests *)
Definition wty:type_check getSemTypeX nil (abs e (abs e (box(pi1 (twoL
(num _ 0) (num _
1))))))=Some (funAppli e (funAppli e (intention e))).
simpl;auto.
Qed.


Definition wty1:isWellTyped getSemTypeX nil (abs e (abs e (box(pi1 (twoL
(num _ 0) (num _
1)))))) (funAppli e (funAppli e (intention e))).
constructor.
constructor.
econstructor.
econstructor.
constructor.
constructor.
auto.
econstructor;simpl;eauto.
Defined.

Definition noHyps0:no_hyps_inside (abs e (abs e (box(pi1 (twoL (num X 0) (num
_ 1)))))).
simpl;auto.
Defined.

Eval compute in (pretty_printer0 _  wty noHyps0).

Eval compute in (trans_lamb1 wty1 noHyps0 (nil_trans)).*)
End coq_terms.

(*
Section deriv_coq.
Variable gr:syn_sem_gram.
Variable l:list (gr.(lexic)).(W).
Variable f:Form (gr.(lexic)).(I) (gr.(lexic)).(J)
(gr.(lexic)).(A).
Variable E:Set. (* interpretation of e *)
Variable intent:Set ->Set.
Variables box_coq diam_coq:forall (A:Set), A->intent A.
Variables debox_coq dediam_coq:forall (A:Set), intent A->A.
Variable consts:forall (x:word_type (gr.(lexic)).(W)),
trans_type E intent (getTypeWT x).

Variable red:deriveTo gr l f.


Hypothesis no_hyps:no_hyps_inside (getSemantic red).

Definition get_deriv_coq:trans_type E intent (mapExt
(gr.(lexic)).(map) f).
eapply trans_lamb with (l := getSemantic red).
 exact box_coq.
 exact diam_coq.
 exact debox_coq.
 exact dediam_coq.
 eexact consts.
 apply wellTyped_type_check.
 case red.
 simpl in |- *.
 intros.
 apply wellTypedSem.
 auto.
 constructor 1.
Defined.


End deriv_coq.
*)