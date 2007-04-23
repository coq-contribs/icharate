(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                              LaBRI                                   *)
(************************************************************************)

Require Export listAux.
Require Export Arith.
Require Export basics.
Set Implicit Arguments.


Section allSem.
Variables I J A:Set.



Inductive semType :Set :=
| e :semType  (* type des individus*)
| t : semType  (* valeurs de verite *)
| funAppli :semType -> semType -> semType (* type fonctionnel *)
| cartProd:semType -> semType -> semType  (* produit cartesien *)
|intention :semType->semType. (* le type s->t cf.Gamut *)



Definition eqDecSem:forall (t1 t2:semType), {t1=t2}+{t1 <>t2}.
decide equality.
Defined.
(* map is a function that maps a semantic type to each atomic one *)
Variable map:A->semType.

(* function that maps a semantic type to each syntactic one *)
Fixpoint mapExt (f:Form I J A){struct f}:semType :=
match f with
| At p => map p
| Slash _ f1 f2 => funAppli (mapExt f2) (mapExt f1)
| Backslash _ f1 f2 =>funAppli (mapExt f1) (mapExt f2)
| Dot _ f1 f2 => cartProd (mapExt f1) (mapExt f2)
| Box _ f1 => (intention (mapExt f1))
| Diamond _ f1 => (intention (mapExt f1))
end.

Section lambdaX.
(* In this section X represents the set of constants of our lambda-calculus*)
Variable X:Set.
Variable getSemTypeX : X->semType.

(* definition of typed lambda terms *)
Inductive lambda_terms:Set:=
| num : nat -> lambda_terms (* numbers for bound variables *)
| ress : X ->lambda_terms (* set of constants used *)
| hyps: nat->semType->lambda_terms (* free variables *)
| appl :lambda_terms -> lambda_terms -> lambda_terms (* application *)
| abs : semType ->lambda_terms  -> lambda_terms (* abstraction, the first type is the type of the bound variable *)
| twoL : lambda_terms -> lambda_terms  -> lambda_terms (* pair of two lambda-terms *)
| pi1 :lambda_terms -> lambda_terms  (* first projection *)
| pi2 : lambda_terms -> lambda_terms (* second projection *)
| box : lambda_terms -> lambda_terms (* intentionality operators *)
| debox : lambda_terms -> lambda_terms
| diam : lambda_terms -> lambda_terms
| dediam :lambda_terms -> lambda_terms.


(* function that tests whether a term is well formed: 
all variables represented by integers are bound and there is no
 leaf of the form (hyps ...), 
thus, the term (abs ty (num 0)) is well formed whereas (num 0) is not *)
Fixpoint isWellFormedN (n:nat) (l:lambda_terms){struct l} :Prop:=
match l with 
| num  k =>match (le_lt_dec n k) with 
                            | right _ => True  (* k<n*)
                            | left _ => False (* n <= k *)
             end
| ress  r => True
|hyps _ _ => True
| appl  l1 l2 => isWellFormedN n l1 /\ isWellFormedN n l2
| abs _ l1 => isWellFormedN (S n) l1
| twoL  l1 l2 => isWellFormedN n l1 /\ isWellFormedN n l2
| pi1  l1 => isWellFormedN n l1
| pi2  l1 => isWellFormedN n l1
| box  l1 => isWellFormedN n l1
| debox  l1 => isWellFormedN n l1
| diam  l1 => isWellFormedN n l1
| dediam  l1 => isWellFormedN n l1
end.

Definition isWellFormed(l:lambda_terms):=(isWellFormedN O l).



Fixpoint no_hyps_inside (l:lambda_terms):Prop:=
match l with
|hyps _ _=> False
| num  k =>True
| ress  r => True
| appl  l1 l2 => no_hyps_inside l1 /\ no_hyps_inside l2
| abs _ l1 => no_hyps_inside l1
| twoL  l1 l2 => no_hyps_inside l1 /\ no_hyps_inside l2
| pi1  l1 => no_hyps_inside l1
| pi2  l1 => no_hyps_inside l1
| box  l1 => no_hyps_inside l1
| debox  l1 => no_hyps_inside l1
| diam  l1 => no_hyps_inside l1
| dediam  l1 => no_hyps_inside l1
end.

(* some useful functions *)
(* binds the hypsothesis (hyps n st) *)
Fixpoint lambdaBind (lTerm:lambda_terms)(i n:nat)(st:semType){struct lTerm}:lambda_terms :=
match lTerm with 
| num l => if (le_lt_dec i l) then (num (S l)) else (num l)
| ress  r =>ress r
| hyps k s=> if (eq_nat_dec k n) 
           then (if (eqDecSem s st) then (num i) else (hyps k s))
           else (hyps k s)
| appl t1 t2 => appl  (lambdaBind t1 i n st) (lambdaBind t2 i n st)
| abs ty t1 => abs ty (lambdaBind t1 (S i) n st)
| twoL t1 t2  =>  twoL  (lambdaBind t1 i n st) (lambdaBind t2 i n st)
| pi1  t1=>pi1  (lambdaBind t1 i n st)
| pi2  t1 => pi2  (lambdaBind t1 i n st)
| box  t1 =>box  (lambdaBind t1 i n st)
| debox  t1 => debox (lambdaBind t1 i n st)
| diam  t1 => diam  (lambdaBind t1 i n st)
| dediam t1 => dediam  (lambdaBind t1 i n st)
end.

(* function that abstract the variable x*)
Definition lambdaAbs(lTerm:lambda_terms)(n :nat)(st:semType):lambda_terms
 :=(abs st (lambdaBind lTerm O n st)).

Fixpoint up_lambda (l:lambda_terms)(n:nat)(i:nat){struct l}:lambda_terms:=
match l with 
|num  m=>match (le_lt_dec i m) with 
            |left _ =>num  (m+n)  (* in this case m>=i*)
            |right _=>num  m
             end
|ress  r => ress  r
|hyps k s=>hyps k s
|appl  l1 l2=> appl  (up_lambda l1 n i) (up_lambda l2 n i)
|abs ty l1 => abs ty (up_lambda l1 n (S i))
| twoL l1 l2 =>twoL  (up_lambda l1 n i) (up_lambda l2 n i)
| pi1  l1 => pi1  (up_lambda l1 n i)
|pi2  l1 => pi2  (up_lambda l1 n i)
| box  l1 => box  (up_lambda l1 n i)
|debox  l1 =>debox (up_lambda l1 n i)
|diam  l1=>diam (up_lambda l1  n i)
|dediam  l1 =>dediam  (up_lambda l1 n i)
end.

Definition lift_lambda(l:lambda_terms)(n:nat):lambda_terms:=
(up_lambda l n 0).

Lemma lift_wf:forall (l:lambda_terms)(k n:nat),
                 isWellFormedN n l->
                 up_lambda l k n=l.
 Proof.
 intros l k; elim l; simpl in |- *; intros; auto.
 generalize H; case (le_lt_dec n0 n).
 induction 2.
 auto.
 decompose [and] H1.
 rewrite (H _ H2); rewrite (H0 _ H3).
 auto.
 rewrite (H _ H0).
 auto.
 decompose [and] H1.
 rewrite (H _ H2); rewrite (H0 _ H3); auto.
 rewrite H; auto.
 rewrite H; auto.
 rewrite H; auto.
 rewrite H; auto.
 rewrite H; auto.
 rewrite H; auto.
Qed.

(* substitution of an hypsothesis of the form (hyps n st) by lTerm2 in
the lambda term lTerm1 *) 
Fixpoint lambdaSubN (lTerm1 lTerm2:lambda_terms)(i n:nat)(st:semType){struct lTerm1}:lambda_terms:=
match lTerm1 with
| num l=> (num l)
| ress  r => ress r
| hyps k s=>if (eq_nat_dec k n)
           then (if (eqDecSem s st) then (lift_lambda lTerm2 i) else
	   (hyps k s))
           else (hyps k s)
| appl t1 t2 => appl (lambdaSubN t1 lTerm2 i n st) (lambdaSubN t2
lTerm2 i n st)
| abs ty t1 => abs ty (lambdaSubN t1 lTerm2 (S i) n st)
| twoL  t1 t2 => twoL  (lambdaSubN t1 lTerm2 i n st) (lambdaSubN t2
lTerm2 i n st)
| pi1  t1 =>pi1  (lambdaSubN t1 lTerm2 i n st)
| pi2  t1 =>pi2  (lambdaSubN t1 lTerm2 i n st)
| box  t1 =>box  (lambdaSubN t1 lTerm2 i n st)
| debox  t1 =>debox  (lambdaSubN t1 lTerm2 i n st)
| diam  t1 =>diam  (lambdaSubN t1 lTerm2 i n st)
|dediam t1 =>dediam  (lambdaSubN t1 lTerm2 i n st)
end.

Definition lambSub (lTerm1 lTerm2:lambda_terms)(n:nat)(st:semType):lambda_terms:=
                         lambdaSubN lTerm1 lTerm2 0 n st.



(* typeness *)
Inductive isWellTyped :(list semType)->lambda_terms->semType ->Set:=
| typeNum: forall (env:list semType) (n:nat)(ty:semType),
                    nth_error env n=Some ty -> 
                    isWellTyped env (num n) ty
| typeVar :forall (x:X)(env:list semType) ,
                  isWellTyped env (ress x) (getSemTypeX x)
|typeHyps:forall (n:nat)(ty:semType)env, isWellTyped env (hyps n ty) ty
| typeAppl : forall (l1 l2: lambda_terms)(t1 t2:semType)(env:(list semType)),
                  isWellTyped env l1 (funAppli t1 t2) -> 
                  isWellTyped env l2 t1 ->
                  isWellTyped env (appl l1 l2) t2
| typeAbs : forall (l1:lambda_terms)( t1 t2:semType)(env:list semType),
                  isWellTyped (t2::env) l1 t1->
                  isWellTyped env (abs t2 l1) (funAppli t2 t1)
| typeTwoL: forall  (l1 l2: lambda_terms)(t1 t2:semType)(env:(list semType)),
                  isWellTyped env l1  t1  -> 
                  isWellTyped env l2 t2 ->
                  isWellTyped env (twoL l1 l2)  (cartProd t1 t2)
| typePi1:forall (l1:lambda_terms)(t1 t2 :semType)(env:list semType),
                 isWellTyped env l1 (cartProd t1 t2)->
                 isWellTyped env (pi1 l1) t1
| typePi2 :forall (l1:lambda_terms)(t1 t2 :semType)(env:list semType),
                 isWellTyped env l1 (cartProd t1 t2)->
                 isWellTyped env (pi2 l1) t2
|typeBox:forall (l1:lambda_terms) (t1:semType)(env:list semType),
                 isWellTyped env l1 t1->
                 isWellTyped env (box l1) (intention t1) 
|typeDebox:forall (l1:lambda_terms)(t1:semType) (env:list semType),
                 isWellTyped env l1 (intention t1)->
                 isWellTyped env (debox l1) t1
|typeDiam:forall (l1:lambda_terms)(t1:semType) (env:list semType),
                 isWellTyped env l1 t1->
                 isWellTyped env (diam l1) (intention t1)
|typeDediam:forall (l1:lambda_terms)(t1:semType) (env:list semType),
                 isWellTyped env l1 (intention t1)->
                 isWellTyped  env (dediam l1) t1.


Fixpoint type_check (env:list semType)(l:lambda_terms){struct l} :
 (option semType):=
match l with 
| num n => nth_error env n 
| ress r => Some (getSemTypeX r)
| hyps k ty=> Some ty
| appl l1 l2 => match (type_check env l1) with 
                | Some (funAppli t1 t2) => match (type_check env l2) with
                                           | Some t'1 => match (eqDecSem t1 t'1) with 
                                                        | left _ => Some t2
                                                        | right _ => None 
                                                       end
                                           | None => None 
                                           end
                |others => None
                 end
| abs t1 l1 => match (type_check (t1::env) l1) with 
              | Some t2 => Some (funAppli t1 t2)
              | None => None
             end 
|twoL l1 l2 => match (type_check env l1) with 
       |Some t1 => match (type_check env l2) with 
           |Some t2 => Some (cartProd t1 t2)
           | None => None
           end
       |None => None
         end
| pi1 l1=> match (type_check env l1) with 
              |Some (cartProd t1 t2) => Some t1
              |others => None
            end
| pi2 l1=> match (type_check env l1) with 
              |Some (cartProd t1 t2) => Some t2
              |others => None
            end  
|box l1=>match (type_check env l1) with
         |Some t1 => Some (intention t1)
         |None => None
       end
|debox l1=>match (type_check env l1) with
           |Some (intention t1) => Some t1
           |others => None
       end
|diam l1=>match (type_check env l1) with
         |Some t1 => Some (intention t1)
         |None => None
       end
|dediam l1=>match (type_check env l1) with
           |Some (intention t1) => Some t1
           |others => None
       end
end.


(* a useful tactic *)
Ltac disc:=
 match goal with 
| H: None = Some _ |- _ => 
 discriminate H
end.

(* some inversion lemmas *)
Lemma getTypeAppl :forall (l1 l2:lambda_terms)(env :list semType)(t1:semType),
                   type_check env (appl l1 l2) =Some t1 ->
                  {t2:semType | (type_check env l1 = (Some (funAppli t2 t1))) /\
                   (type_check env l2 = (Some t2))}.
Proof.
intros.
generalize H;clear H.
simpl;elim (type_check env l1); elim (type_check env l2).
intros a a0; case a0.
intro H2; discriminate H2.
intro H2; discriminate H2.
intros s s0; elim (eqDecSem s a).
intros.
exists s.
rewrite a1; injection H; intro R; rewrite R; tauto.
intros H H1; discriminate H1.
intros s s0 H1; discriminate H1.
intros H H1; discriminate H1.
intro a; elim a; intros; disc.
intros.
 discriminate H.
intro H; discriminate H.
Defined.


Lemma getTypeTwoL:forall (l1 l2:lambda_terms)(env :list semType)(t1:semType),
                             type_check env (twoL l1 l2) =Some t1 ->
                             {t'1: semType & { t'2:semType |t1 =cartProd t'1 t'2 /\
                              type_check env l1 =Some t'1 /\
                              type_check env l2 =Some t'2}}.
Proof.
intros.
generalize H; clear H; simpl;
 elim (type_check env l1); elim (type_check env l2).
intros.
exists a0; exists a.
injection H; intro R; rewrite R;tauto.
intros; disc.
intros; disc.
intros ; disc.
Defined.

Lemma getTypePi1:forall (l1:lambda_terms)(env:list semType)(t1:semType),
                        (type_check env (pi1 l1)) = Some t1 ->
                        {t2:semType|(type_check env l1) = 
                                           Some (cartProd t1 t2)}.
Proof.
intros.
generalize H; clear H;simpl.
elim (type_check env l1).
intro a; elim a; intros; try disc.
exists s0; injection H1; intro R; rewrite R.
auto.
intro; disc.
Defined.

Lemma getTypePi2:forall (l1:lambda_terms)(env:list semType)(t1:semType),
                        (type_check env (pi2 l1)) = Some t1 ->
                        {t2:semType|(type_check env l1) = 
                                   Some (cartProd t2 t1)}.
Proof.
intros.
generalize H; clear H;simpl.
elim (type_check env l1).
intro a; elim a; intros; try disc.
exists s; injection H1; intro R; rewrite R.
auto.
intro; disc.
Defined.

Lemma getTypeAbs: forall (l1 :lambda_terms)(t1 t2:semType)(env:list semType),
                     type_check env (abs t1 l1)=Some t2 ->
                     {t'1:semType| t2=funAppli t1 t'1 /\
                                          type_check (t1::env) l1 =Some t'1}.
Proof.
intros.
generalize H.
clear H; simpl.
case (type_check (t1::env) l1).
intros s H; injection H; intro R; rewrite <- R.
exists s;tauto.
intro; disc.
Defined.
  

Lemma getTypeBox:forall (l1:lambda_terms)(t1:semType)(env:list semType),
                     type_check env (box l1)=Some t1->
                     { t'1:semType| t1=intention t'1/\ type_check env l1 =Some t'1}.
Proof.
 intros.
 generalize H; clear H; simpl in |- *.
 elim (type_check env l1).
 intros.
 injection H.
 intro.
 exists a; split.
 rewrite H0; reflexivity.
 auto.
 intro H1; discriminate H1.
Defined.

Lemma getTypeDiam:forall (l1:lambda_terms)(t1:semType)(env:list semType),
                     type_check env (diam l1)=Some t1->
                     {t'1:semType| t1=intention t'1/\
                      type_check env l1 =Some t'1}.
Proof.
 intros.
 generalize H; clear H; simpl in |- *.
 elim (type_check env l1).
 intros.
 injection H.
 intro.
 exists a; split.
 rewrite H0; reflexivity.
 auto.
 intro H1; discriminate H1.
Defined.

Lemma getTypeDebox:forall (l1:lambda_terms)(t1:semType)(env:list semType),
                    type_check env (debox l1)=Some t1->
                    type_check env l1=Some (intention t1).
Proof.
 intros l1 t1 env.
 simpl in |- *.
 elim (type_check env l1).
 intro a.
 case a; intros; try disc.
 injection H; intro R; rewrite R; auto.
 intro; disc.
Defined.

Lemma getTypeDediam:forall (l1:lambda_terms)(t1:semType)(env:list semType),
                   type_check env (dediam l1)=Some t1->
                   type_check env l1=Some (intention t1).
Proof.
 intros l1 t1 env.
 simpl in |- *.
 elim (type_check env l1).
 intro a.
 case a; intros; try disc.
 injection H; intro R; rewrite R; auto.
 intro; disc.
Defined.

Lemma type_check_wellTyped:forall (l1:lambda_terms)(env:list semType) (t1:semType), 
                        type_check env l1= Some t1-> 
                         isWellTyped env l1 t1.
Proof.
intro l1; elim l1;intros.
simpl in H.
constructor.
auto.
simpl in H.
injection H.
intro R;rewrite <-R;constructor.
simpl in H;injection H;intro R.
rewrite <- R; constructor.
elim (getTypeAppl _ _ _ H1).
intros x H2.
elim H2; intros.
econstructor; eauto.
elim (getTypeAbs _ _ _ H0).
intros x H1.
elim H1; intros R H2; rewrite R.
constructor.
apply H;auto.
elim (getTypeTwoL _ _ _ H1).
intros x H2.
elim H2;  intros x0 H3.
elim H3; intros H4 H5.
rewrite H4; elim H5; intros; constructor;auto.
elim (getTypePi1 _ _  H0).
intros.
econstructor;eauto.
elim (getTypePi2 _ _ H0); intros; econstructor; eauto.
elim (getTypeBox _ _ H0).
intros x H1.
elim H1; clear H1; intros.
subst.
constructor.
eauto.
constructor.
apply H.
apply getTypeDebox; auto.
elim (getTypeDiam _ _ H0).
intros x H1.
elim H1; clear H1; intros.
subst.
constructor.
auto.
constructor.
apply H; apply getTypeDediam.
auto.
Defined.

Lemma wellTyped_type_check:forall (l1:lambda_terms)(env:list semType) (t1:semType), 
                   isWellTyped env l1 t1->     
                   type_check env l1= Some t1.
Proof.
 induction 1.
 simpl in |- *; auto.
 simpl in |- *; auto.
 auto.
 simpl in |- *; rewrite IHisWellTyped1;
 rewrite IHisWellTyped2; auto.
 case (eqDecSem t1 t1).
 auto.
 induction 1; auto.
 simpl in |- *.
 rewrite IHisWellTyped.
 auto.
 simpl in |- *; rewrite IHisWellTyped1;
 rewrite IHisWellTyped2; auto.
 simpl in |- *.
 rewrite IHisWellTyped; auto.
 simpl in |- *; rewrite IHisWellTyped; auto.
 simpl in |- *; rewrite IHisWellTyped; auto.
 simpl in |- *; rewrite IHisWellTyped; auto.
 simpl in |- *; rewrite IHisWellTyped; auto.
 simpl in |- *; rewrite IHisWellTyped; auto.
Defined.

Lemma one_type:forall (l:lambda_terms) (t1 t2:semType)(env:list semType),
                     isWellTyped env l t1  ->
                     isWellTyped env l t2 ->
                      t1 =t2. 
Proof.
 intros; cut (Some t1 = Some t2).
 injection 1; auto.
 rewrite <- (wellTyped_type_check H); rewrite <- (wellTyped_type_check H0).
 auto.
Qed.


Inductive add_ith_list (A:Set)(a:A):list A->list A->nat->Prop:=
|add_0:forall l1, add_ith_list a l1 (a::l1) 0
|add_next:forall l1 l2 i b , add_ith_list a l1 l2 i->add_ith_list a
(b::l1)(b::l2) (S i).

(* some lemmas about this predicate *)
Lemma nth_add1:forall (A:Set)(l1 l2:list A)(i:nat)a b,
                 add_ith_list a l1 l2 i->
              forall (n:nat), n>=i->
              nth_error  l1 n=Some b->
              nth_error l2 (S n) =Some b.
Proof.
 induction 1.
 simpl in |- *; auto.
 simpl in |- *.
 intros.
 generalize H0 H1; clear H0 H1; case n; intros.
 inversion H0.
 simpl in H1.
 eauto with arith.
Qed.

Lemma nth_add2:forall (A:Set)(l1 l2:list A)(i:nat)a b,
                 add_ith_list a l1 l2 i->
              forall (n:nat), n<i->
              nth_error l1 n=Some b->
              nth_error l2 n =Some b.
Proof.
 induction 1.
 inversion 1.
 intro n; case n; simpl in |- *; intros.
 auto.
 eauto with arith.
Qed.

Lemma nth_add3:forall (A:Set)(l1 l2:list A)(i:nat)a ,
                 add_ith_list a l1 l2 i->
                nth_error l2 i=Some a.
induction 1;simpl;auto.
Qed.


(* Some lemmas concerning the predicate isWellFormed *)
Lemma wellFLe1:forall (n m:nat), lt n m ->
                                isWellFormedN m (num  n).
Proof.
 intros.
 simpl in |- *.
 elim (le_lt_dec m n); intro.
 absurd (m <= n); auto with arith.
 auto.
Qed.


Lemma wellFLe2:forall (n m:nat),isWellFormedN m (num  n)->
                                lt n m.
Proof.
 intros n m .
 simpl in |- *.
 elim (le_lt_dec m n).
 tauto.
 auto.
Qed.

Lemma notWellFormedNum:forall (n:nat), isWellFormed (num  n) ->
                                       False.
Proof.
 intros n H.
 unfold isWellFormed in H.
 cut (n < O).
 intro; auto with arith.
 apply wellFLe2  ; auto.
Qed.

Lemma wellFLe: forall (l:lambda_terms)(n m:nat), n <= m ->
                                        (isWellFormedN n l)->
                                        (isWellFormedN m l).
Proof.
 intro l; elim l; intros.
 apply wellFLe1.
 eapply lt_le_trans.
 eapply wellFLe2; eauto.
 auto.
 simpl in |- *; auto.
 simpl in |- *; auto.
 simpl in H2; elim H2; clear H2; intros; simpl in |- *;split; eauto.
 simpl in H1.
 simpl in |- *.
 apply (H (S n) (S m)).
 auto with arith.
 auto.
 simpl in |- *.
 simpl in H2; elim H2; intros;split;eauto.
 simpl in |- *;simpl in H1;eauto.
 simpl in |- *; simpl in H1; eauto.
 simpl in |- *; simpl in H1; eauto.
 simpl in |- *; simpl in H1; eauto.
 simpl in |- *; simpl in H1; eauto.
 simpl in |- *; simpl in H1; eauto.
Qed.

Lemma isWellFormedBindN:forall (l:lambda_terms)(i n:nat)(st:semType),
                            isWellFormedN i l->
                            isWellFormedN (S i) (lambdaBind l i n st).
Proof. 
 intro l; elim l; intros.
 simpl lambdaBind.
 case (le_lt_dec i n).
 intro; apply wellFLe1.
 cut (n < i).
 auto with arith.
 eapply wellFLe2; eauto.
 intro; apply wellFLe1; auto with arith.
 simpl in |- *;auto.
 simpl in |- *.
 case (eq_nat_dec n n0).
 case (eqDecSem s st).
 intros; apply wellFLe1; auto with arith.
 simpl in |- *; auto.
 auto.
 simpl in |- *.
 auto.
 simpl in |- *;simpl in H1; elim H1;intros;  split; eauto.
 simpl; simpl in H0; intros; eauto.
 simpl in |- *;elim H1; intros;split; eauto.
 simpl in |- *; simpl in H0; intros; eauto.
 simpl in |- *; simpl in H0; intros; eauto.
 simpl in |- *; simpl in H0; intros; eauto.
 simpl in |- *; simpl in H0; intros; eauto.
 simpl in |- *; simpl in H0; intros; eauto.
 simpl in |- *; simpl in H0; intros; eauto.
Qed.

Lemma isWellFormedBind: forall (l:lambda_terms)(n:nat)(st:semType),
                       isWellFormed l ->
                       isWellFormed (lambdaAbs l n st).  
Proof.
 unfold isWellFormed in |- *.
 unfold lambdaAbs in |- *.
 simpl in |- *.
 intros.
 apply isWellFormedBindN; auto.                                                                                     
Qed.

Lemma wellFormedUp:forall (l1 :lambda_terms)(i j k:nat), 
                   isWellFormedN i l1->
                   isWellFormedN (i+j) (up_lambda l1 j k).
Proof.
  intro l1;elim l1.
  simpl up_lambda in |- *.
  intros; elim (le_lt_dec k n); intro.
  cut (n < i).
  intro; apply wellFLe1; auto with arith.
  apply wellFLe2; auto.
  apply wellFLe with i.
  auto with arith.
  auto.
  simpl in |- *; auto.
  simpl in |- *; auto.
  simpl in |- *.
  intros; elim H1; split; auto.
  simpl in |- *; intros; auto.
  cut (S (i + j) = S i + j).
  intro H1; rewrite H1.
  auto.
  auto with arith.
  simpl in |- *; intros.
  elim H1; split; auto.
  simpl in |- *; intros; auto.
  simpl in |- *; intros; auto.
  simpl in |- *; intros; auto.
  simpl in |- *; intros; auto.
  simpl in |- *; intros;auto.
  simpl in |- *; intros; auto.
Qed.


Lemma wellFormNSub:forall (l1 l2:lambda_terms)(i j n:nat)(st:semType),
                        isWellFormedN i l2->
                        isWellFormedN j l1->
                        isWellFormedN (i+j) (lambdaSubN l1 l2 j n st).
Proof.
 intro l1; elim l1; intros.
 simpl in |- *.
 apply wellFLe1.
 cut (n < j).
 unfold lt in |- *; intro.
 apply le_trans with j.
 auto.
 auto with arith.
 apply wellFLe2; auto.
 simpl in |- *.
 auto.
 simpl in |- *.
 case (eq_nat_dec n n0).
 case (eqDecSem s st).
 unfold lift_lambda in |- *.
 intros; apply wellFormedUp.
 auto.
 simpl in |- *; auto.
 simpl in |- *; auto.
 simpl in |- *.
 simpl in H2; split.
 elim H2; auto.
 elim H2; auto.
 simpl in |- *.
 simpl in H1.
 cut (S (i + j) = i + S j).
 intro H2; rewrite H2.
 auto.
 auto with arith.
 elim H2; simpl in |- *; split; auto.
 simpl in H1; simpl in |- *; auto.
 simpl in H1; simpl in |- *; auto.
 simpl in H1; simpl in |- *; auto.
 simpl in H1; simpl in |- *; auto.
 simpl in H1; simpl in |- *; auto.
 simpl in H1; simpl in |- *; auto.
Qed.

Lemma isWellFormedSubst:forall (l1 l2:lambda_terms)(n:nat)(st:semType),
                         isWellFormed l2->
                         isWellFormed l1->
                         isWellFormed (lambSub l1 l2 n st).
Proof.
 unfold isWellFormed in |- *; unfold lambSub in |- *.
 intros.
 change (isWellFormedN (0 + 0) (lambdaSubN l1 l2 0 n st)) in |- *.
 apply wellFormNSub;auto.
Qed.

(* welltyped and wellformed *)
Lemma wellTypedFormed:forall (l:lambda_terms)(t1:semType)(env:list semType),
                             isWellTyped env l t1 -> 
                             isWellFormedN (length env) l.
Proof.
intro l ; elim l; intros.
inversion H.
apply wellFLe1.
eapply nth_error_some_length; eauto.
simpl in |- *; auto.
simpl;auto.
inversion H1;simpl;split;eauto.
inversion H0; simpl.
cut ((S (length env))=(length (s::env))).
intro R; rewrite R;eauto.
simpl;auto.
inversion H1;simpl; split;eauto.
inversion H0; simpl;eauto.
inversion H0; simpl; eauto.
inversion H0;simpl;eauto.
inversion H0;simpl;eauto.
inversion H0;simpl;eauto.
inversion H0;simpl;eauto.
Defined.

(* some auxiliary lemmas about well-typeness *)
Lemma wellTypedBind: forall (l:lambda_terms)(t1:semType)
                     (env:(list semType))(n:nat)(st:semType),
                            isWellTyped env l t1 ->
                           (forall (i:nat)(env':list semType),
                              add_ith_list st env env' i->
                              isWellTyped env' (lambdaBind l i n st) t1).
Proof.
 induction 1; intros; simpl in |- *.
 case (le_lt_dec i n0).
 intro; constructor.
 eapply nth_add1; eauto.
 intro; constructor; eapply nth_add2; eauto.
 constructor.
 auto.
 case (eq_nat_dec n0 n).
 case (eqDecSem ty st).
 intros; subst; constructor.
 eapply nth_add3; eauto.
 intros; constructor.
 intro; constructor.
 econstructor; eauto.
 constructor.
 apply IHisWellTyped.
 constructor; auto.
 constructor; auto.
 econstructor; eauto.
 econstructor; eauto.
 constructor; auto.
 constructor; auto.
 constructor; auto.
 constructor; auto.
Defined.

Lemma wellTypedAbs:forall (l:lambda_terms)(t1:semType)
             (env:list semType)(n:nat)(st:semType),
                       isWellTyped env l t1 ->
                       isWellTyped env (lambdaAbs l n st) (funAppli st t1). 
Proof.
intros.
unfold lambdaAbs.
constructor.
eapply wellTypedBind.
eauto.
constructor.
Defined.


Lemma wellTypedAppEnv:forall (l1:lambda_terms)(env1 env2:list semType)(t1:semType),
                       isWellTyped env1 l1 t1 ->
                       isWellTyped (env1++ env2) l1 t1.
Proof.
intro l1; elim l1; intros.
inversion H.
constructor.
apply nth_error_fst_app; auto.
inversion H.
constructor.
auto.
inversion H.
constructor.
inversion H1; econstructor;eauto.
inversion H0; constructor.
change (s::env1++env2) with ((s::env1)++env2).
apply H;auto.
inversion H1; constructor;auto.
inversion H0; econstructor;eauto.
inversion H0; econstructor; eauto.
inversion H0; constructor;auto.
inversion H0; constructor;auto.
inversion H0; constructor;auto.
inversion H0; constructor;auto.
Defined.

Lemma wellTypedSub: forall(l1 l2 :lambda_terms)(env:list semType)
                                (i n:nat)(t1 st:semType), 
                               isWellTyped nil l2 st ->  
                               isWellTyped env l1 t1 ->
                               isWellTyped env (lambdaSubN l1 l2 i n st) t1.
Proof.
intro l1; elim l1; intros;simpl.
auto.
auto.
case (eq_nat_dec n n0).
case (eqDecSem s st).
intros; subst.
inversion H0.
subst.
unfold lift_lambda in |- *; rewrite lift_wf.
change env with (nil ++ env) in |- *.
apply wellTypedAppEnv; auto.
exact (wellTypedFormed H).
auto.
auto.
inversion H2.
econstructor;eauto.
inversion H1.
constructor;eauto.
inversion H2; constructor;auto.
inversion H1;econstructor;eauto.
inversion H1; econstructor;eauto.
inversion H1; constructor;auto.
inversion H1; constructor;auto.
inversion H1; constructor;auto.
inversion H1; constructor;auto.
Defined.

Lemma wellTypedSubst: forall(l1 l2 :lambda_terms)(env:list semType)
                                (n:nat)(t1 st:semType), 
                               isWellTyped nil l2 st ->  
                               isWellTyped env l1 t1 ->
                               isWellTyped env (lambSub l1 l2 n st) t1.
Proof.
unfold lambSub in |- *.
intros; apply wellTypedSub; auto.
Defined.


End lambdaX.
End allSem.