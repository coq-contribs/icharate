(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2006                                *)
(*                              LaBRI                                   *)
(************************************************************************)
Set Implicit Arguments.
Require Export permutation.
Require Export ZArith.

(* some auxiliary definitions and theorems about lists *)

(* constructs a list of integers composed of n zeros *)
Fixpoint constructList(n:nat):list nat:=
match n with
| 0=> nil
|(S k)=>0::(constructList k)
end.


Fixpoint getSubLists (A:Set)(l1:list A) (n:nat) {struct n}:
  option (list A *list A):=
 match l1, n with
 |nil , _ => None
 |cons a l , O => Some (nil , l1)
 |cons a l,  S m=> 
    match getSubLists l m with
           | None =>None 
           | Some ( pair l1 l2) =>Some  (cons a l1, l2)
              end
 end.




Lemma map_length:forall (A B:Set)(f:A->B)(l:list A),
                  length (map f l)=length l.
Proof.
 intros.
 elim l.
 simpl in |- *.
 auto.
 simpl in |- *.
 auto with arith.
Qed.

Lemma forall_eq_list:forall (A:Set)(l1 l2:list A) ,
    (forall i:nat, nth_error l1 i=nth_error l2 i)->
     l1=l2.

intros A0 l1.
elim l1.
simpl in |- *.
intros.
cut (nth_error l2 0 = None).
simpl in |- *.
case l2.
auto.
discriminate 1.
eauto.
rewrite <- (H 0).
auto.
intros.
cut (nth_error l2 0 = Some a).
generalize H0; case l2.
simpl in |- *.
discriminate 2.
intros.
simpl in H2.
injection H2; intros; subst.
cut (l = l0).
intro; subst; auto.
apply H.
intro i.
replace (nth_error l i) with (nth_error (a :: l) (S i)).
replace (nth_error l0 i) with (nth_error (a :: l0) (S i)).
auto.
simpl in |- *; auto.
simpl in |- *; auto.
rewrite <- (H0 0); auto.
Qed.

Lemma nth_map:forall(A B:Set)(f:A->B)(l:list A) (a:A)(i:nat),
                nth_error l i=Some a->
                nth_error (map f l) i=Some (f a).
Proof.
 intros A B f l; elim l; intros.
 generalize H; case i; simpl in |- *.
 discriminate 1.
 discriminate 2.
 simpl in |- *.
 generalize H0; case i.
 simpl in |- *.
 injection 1; intro; subst; auto.
 simpl in |- *.
 auto.
Qed.

Lemma nth_sup_length:forall (A:Set)(l1:list A) i , 
              length l1 <=i ->
              nth_error l1 i=None.
Proof.
 intros A0 l1.
 elim l1.
 simpl in |- *.
 intro i; case i.
 simpl in |- *; auto.
 simpl in |- *.
 auto.
 intros.
 generalize H0; clear H0.
 simpl in |- *; case i.
 intro.
 inversion H0.
 simpl in |- *.
 intro; auto with arith.
Qed.




Definition sum_all(l:list Z):Z:=
op_all Zplus (0%Z) l.



Lemma nth_error_length:forall (A:Set)(n:nat)(l:list A), 
                        n<length l->
                       (exists a:A, nth_error l n=Some a).
Proof.
 intros A n l; generalize n; elim l; intros.
 simpl in H; absurd (n0 < 0); auto with arith.
 simpl in |- *.
 generalize H0; case n0; intros.
 exists a; auto.
 simpl in |- *.
 simpl in H1.
 apply H.
 auto with arith.
Qed.

Lemma nth_error_some_length:forall(A:Set)(n:nat)(l:list A)a, 
                           nth_error l n=Some a->
                           n<length l.
Proof.
 intros.
 case (le_lt_dec (length l) n).
 intro.
 rewrite nth_sup_length in H.
 discriminate H.
 auto.
 auto.
Qed.

Lemma nth_error_app:forall (A:Set)(l1 l2:list A) (n:A)(i:nat), 
                      nth_error (l1++l2) i=Some n->
                      nth_error l1 i =Some n \/
                      (i>=length l1/\nth_error l2 (i-length l1)=Some n). 
Proof.
 intros A l1; elim l1; intros.
 simpl in H.
 right.
 simpl in |- *.
 rewrite <- minus_n_O; split;auto with arith.
 rewrite <- app_comm_cons in H0.
 generalize H0; clear H0; case i.
 simpl in |- *.
 intro; left; auto.
 simpl in |- *.
 intros.
 elim (H l2 n n0 H0).
 tauto.
 intro H1; decompose [and] H1; clear H1.
 right; split; auto with arith.
Qed.

Lemma nth_error_fst_app:forall (A:Set)(l1 l2:list A) (n:A)(i:nat),
                            nth_error l1 i =Some n ->
                            nth_error (l1++l2) i=Some n.
Proof.
 intros A l1; elim l1.
 intros l2 n i; case i.
 simpl in |- *; discriminate 1.
 discriminate 1.
 intros.
 generalize H0; case i.
 simpl in |- *.
 auto.
 simpl in |- *.
 auto.
Qed.

Lemma nth_error_scd_app:forall (A:Set)(l1 l2:list A) (n:A)(i:nat),
                            nth_error l2 i =Some n ->
                            nth_error (l1++l2) (i+length l1)=Some n.
Proof.
 intros A0 l1; elim l1.
 simpl in |- *.
 intros.
 replace (i + 0) with i.
 auto.
 omega.
 simpl in |- *.
 intros.
 replace (i + S (length l)) with (S (i + length l)).
 simpl in |- *.
 auto.
 omega.
Qed.



Inductive extract_opt (A:Set):list A ->list (option A)->Prop:=
|exnil:extract_opt nil nil
|excons:forall l1 l2 a, extract_opt l1 l2 ->extract_opt (a::l1) ((Some
a)::l2).


Lemma extract_one:forall (A:Set)(l1:list A) l3,
                     extract_opt l1 l3->
                     forall l2,extract_opt l2 l3->
                     l1 =l2.
Proof.
 induction 1.
 inversion 1.
 auto.
 inversion 1.
 cut (l1 = l3).
 intro; subst; auto.
 auto.
Qed.

Lemma extract_app:forall (A:Set)(l1 :list (option A))l3,
                   extract_opt l3 l1->
                  forall l4 l2, extract_opt l4 l2->
                   extract_opt (l3++l4) (l1++l2).
Proof.
 induction 1.
 simpl in |- *.
 auto.
 simpl in |- *.
 intros; constructor.
 auto.
Qed.

Lemma extract_permut:forall (A:Set)(l1 l2:list (option A)),
                     permut l1 l2->
                    forall l1', extract_opt l1' l1->
                     (exists l2', extract_opt l2' l2).
Proof.
 induction 1.
 intros.
 exists l1'; auto.
 intros.
 inversion H0.
 elim (IHpermut _ H3).
 intros.
 exists (a0 :: x).
 constructor; auto.
 inversion 1.
 exists (l1 ++ a0 :: nil).
 apply extract_app.
 auto.
 constructor.
 constructor.
 intros.
 elim (IHpermut1 _ H1).
 intros l4 H2.
 elim (IHpermut2 _ H2); intros l5 H3.
 exists l5; auto.
Qed.

Lemma permut_extract:forall (A:Set)(l1' l2':list (option A)),
                       permut l1' l2'->
                      forall l1 l2, extract_opt l1 l1'->
                                    extract_opt l2 l2'->
                                    permut l1 l2.
Proof.
 induction 1.
 intros.
 replace l1 with l2.
 constructor.
 eapply extract_one; eauto.
 inversion 1; intros.
 inversion H5.
 subst.
 constructor.
 auto.
 inversion 1.
 intro.
 subst.
 replace l2 with (l0 ++ a0 :: nil).
 constructor.
 eapply extract_one.
 eapply extract_app.
 eauto.
 constructor 2.
 constructor.
 auto.
 intros.
 elim (extract_permut H H1).
 intros.
 econstructor.
 eauto. 
 auto.
Qed.

Lemma extract_forall:forall (A:Set)(l1:list A)l2,
                     length l1=length l2->
                     (forall i a , nth_error l1 i=Some a->
                                   nth_error l2 i=Some(Some a))->
                      extract_opt l1 l2.
Proof.
 intros A l1; elim l1.
 intro l2; case l2.
 intros; constructor.
 simpl in |- *; discriminate 1.
 simpl in |- *.
 intros a l H l2; case l2.
 discriminate 1.
 simpl in |- *.
 intros.
 replace o with (Some a).
 constructor.
 apply H.
 omega.
 intros.
 replace (nth_error l0 i) with (nth_error (o :: l0) (S i)).
 apply H1.
 simpl in |- *; auto.
 simpl in |- *; auto.
 cut (nth_error (o :: l0) 0 = Some (Some a)).
 simpl in |- *.
 injection 1; auto.
 apply H1; simpl in |- *; auto.
Qed.

(* some predicates *)
Fixpoint isIncl (A:Set)(l1 l2:list A){struct l1}:Prop:=
match l1 with 
|nil=> True
|a1::l=>In a1 l2 /\(isIncl l l2)
end.

Fixpoint distinct_elts (A:Set)(l1:list A){struct l1}:Prop:=
match l1 with 
|nil => True
|a::l=>~In a l /\distinct_elts l
end.

Fixpoint noInter (A:Set)(l1 l2:list A){struct l1}:Prop:=
match l1 with 
| nil =>True
| a::l=> ~In a l2 /\noInter l l2
end.

Lemma distinct_app:forall (A:Set) (l1 l2:list A),
                   distinct_elts l1 ->
                   distinct_elts l2->
                   noInter l1 l2 ->
                   distinct_elts (l1++l2).
Proof.
 intros A l1; elim l1; simpl in |- *.
 auto.
 intros.
 split.
 red in |- *.
 intro H3.
 elim (in_app_or _ _ _ H3).
 elim H0; tauto.
 elim H2; auto.
 apply H; tauto.
Qed.

Lemma add_in:forall(A:Set)(l1 l2:list A)a b,
                    add_somewhere a l1 l2->
                    In b l1-> 
                    In b l2.
Proof.
 induction 1.
 simpl in |- *; tauto.
 simpl in |- *; induction 1.
 tauto.
 right; auto.
Qed.

Lemma isIncl_in:forall (A:Set)(l1 l2:list A)a,
                 isIncl l1 l2->
                 In a l1->
                 In a l2.
Proof.
 intros A l1; elim l1; simpl in |- *.
 tauto.
 intros.
 elim H1.
 intro; subst; tauto.
 intros; elim H0; eauto.
Qed.

Lemma noInter_app:forall (A:Set)(l1 l2 l3:list A),
                   noInter l1 l3->
                   noInter l2 l3->
                   noInter (l1++l2) l3.
Proof.
 intros A l1; elim l1.
 simpl in |- *; auto.
 simpl in |- *.
 intros.
 split.
 tauto.
 apply H; tauto.
Qed.

Lemma isIncl_app:forall (A:Set)(l1 l2 l3:list A),
                 isIncl l1 l3->
                 isIncl l2 l3->
                 isIncl (l1++l2) l3.
Proof.
 intros A l1; elim l1; simpl in |- *.
 auto.
 intros.
 case H0; split.
 auto.
 auto.
Qed.

Lemma distinct_add:forall (A:Set)(l1 l2:list A)a,
                    add_somewhere a l1 l2->
                    distinct_elts l2->
                    distinct_elts l1.
Proof.
 induction 1.
 simpl in |- *; tauto.
 simpl in |- *; intros.
 elim H0; split.
 red in |- *; intro.
 elim H1; eapply add_in; eauto.
 auto.
Qed.

Require Import PermutSetoid.

Section permt.
Variable A:Set.
Variable decA :forall (a1 a2:A),{a1=a2}+{a1<>a2}.

Lemma multiplicity_0_notIn:forall(l1 :list A)a,
                           ~In a l1->
                           multiplicity  (list_contents (eq (A:=A))
                           decA l1) a=0.
Proof.
 intro l1; elim l1.
 simpl in |- *; auto.
 simpl in |- *.
 intros.
 case (decA a a0).
 intro; case H0.
 tauto.
 intro; rewrite H.
 auto.
 elim (In_dec decA a0 l).
 intro; elim H0; tauto.
 auto.
Qed.

Lemma multiplicity_one_distinct:forall(l1 :list A)a,
                           In a l1->
                           distinct_elts l1->
                           multiplicity  (list_contents (eq (A:=A))
                           decA l1) a=1.
Proof.
 intro l1; elim l1.
 simpl in |- *; tauto.
 simpl in |- *.
 intros.
 decompose [and] H1;clear H1.
 case H0.
 intro.
 case (decA a a0).
 intro;subst.
 rewrite multiplicity_0_notIn; auto.
 intro H4; case H4; auto.
 intro.
 case (decA a a0).
 intro; subst.
 elim H2; auto.
 intro; rewrite H;auto.
Qed.

Lemma incl_distinct_permut :forall (l1 l2:list A), 
                 isIncl l1 l2 ->
                 isIncl l2 l1 ->
                 distinct_elts l1->
                 distinct_elts l2 ->
                 permut l1 l2.
Proof.
 intros; apply eqmset_to_ind with decA.
 unfold permutation in |- *.
 unfold meq in |- *.
 intros.
 elim (In_dec decA a l1).
 intro.
 rewrite multiplicity_one_distinct.
 rewrite multiplicity_one_distinct.
 auto.
 eapply isIncl_in; eauto.
 auto.
 auto.
 auto.
 intro.
 rewrite multiplicity_0_notIn.
 rewrite multiplicity_0_notIn.
 auto.
 red in |- *; intro.
 case b.
 eapply isIncl_in; eauto.
 auto.
Qed.

End permt.
