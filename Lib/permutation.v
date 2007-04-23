(************************************************************************)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                        About List Permutation                        *)
(*                              LaBRI                                   *)
(************************************************************************)
Require Export Permutation.
Require Export List.
Require Export Arith.
Require Export Omega.
Require Export Multiset.

Set Implicit Arguments.

(* we prove in this file some properties 
  of the predicate permut inductively defined,
  we propose to establish the equivalence between
  this definition of permutation and the one proposed 
 in the library Permutation.v *)
Section perm.
Variables A B:Set.
Variable decA : forall a b : A, {a = b} + {a <> b}.

(* some additional lemmas and definitions about lists *)
Lemma length_app:forall (l1 l2:list A), length (l1++l2)=length
l1+length l2.
Proof.
 intros; elim l1; intros.
 simpl in |- *; auto.
 simpl in |- *.
 rewrite H.
 auto.
Qed.


Lemma map_app:forall (f:A->B)(l1 l2:list A), 
map f (l1++l2)=map f l1 ++ map f l2.
Proof.
 intros f l1; elim l1; intros.
 simpl in |- *.
 auto.
 simpl in |- *.
 rewrite (H l2).
 auto.
Qed.


Inductive add_somewhere(A:Set)(a:A):list A ->list A->Prop:=
|add_fst:forall (l1 :list A), add_somewhere a l1 (a::l1)
|add_2:forall l1 l2 b, add_somewhere a l1 l2 ->
                       add_somewhere a (b::l1) (b::l2).



Lemma add_in:forall (l1:list A)a, 
                    In a l1->
                    (exists l2, add_somewhere a l2 l1).
Proof.
 intros l1; elim l1.
 simpl in |- *; tauto.
 simpl in |- *.
 intros.
 case H0.
 intro; subst; exists l; constructor.
 intro.
 elim (H _ H1); intros.
 econstructor.
 constructor 2; eauto.
Qed.

(*********************************************************)
(*      Inductive definition of list permutation         *)
(*                permut predicate                       *)
(*********************************************************)

(* taken from Coq manual *)

Inductive permut(A:Set) :list A ->list A ->Prop:=
|perm_refl:forall l, permut l l
|perm_cons:forall a l0 l1, permut l0 l1->permut (a::l0)(a::l1)
|perm_app:forall a l, permut (a::l) (l++(a::nil))
|perm_trans:forall l1 l2 l3, 
              permut l1 l2 -> permut l2 l3 -> permut l1 l3.

(* some properties about permut predicate *)

(* permut conserves the length of its first argument *) 
Lemma permut_length:forall (l1 l2:list A), 
                    permut l1 l2->
                    length l1=length l2.
Proof.
 induction 1.
 auto.
 auto.
 simpl in |- *; auto with arith.
 simpl in |- *.
 rewrite length_app.
 simpl in |- *.
 omega.
 omega.
Qed.

(*permut  and map *)
Lemma map_permut:forall (l1 l2:list A)(f:A->B),
                   permut l1 l2->
                   permut (map f l1)(map f l2).
Proof.
 induction 1.
 constructor.
 simpl in |- *.
 constructor; auto.
 simpl in |- *.
 rewrite map_app.
 simpl in |- *.
 constructor.
 econstructor; eauto.
Qed.


Section op_permut.
(* binary operator *)
Variable op:A->A->A.
Variable a_neutral:A.
(* op is commutative *)
Hypothesis op_com:forall (a1 a2:A), op a1 a2=op a2 a1.
(* a_neutral is a neutral element *)
Hypothesis a_neutral_op:forall (a:A), op a_neutral a=a.
(* op is associative *)
Hypothesis op_assoc:forall (a1 a2 a3:A), op a1 (op a2 a3)=op (op a1
a2) a3.

(* applying op to all the elements of the list
   op(a1::a2::...an)=op(a1,(op a2, (op...an))) *)
Fixpoint op_all(l:list A):A:=
 match l with 
|nil => a_neutral
|b::l1=>op b (op_all l1)
end.


Lemma op_all_app:forall (l1 l2:list A), 
op_all (l1++l2) =op (op_all l1)(op_all l2).

 intro l1; elim l1; intros.
 simpl in |- *.
 rewrite a_neutral_op.
 auto.
 simpl in |- *.
 rewrite (H l2).
 rewrite op_assoc.
 auto.
Qed.


Lemma op_all_permut:forall (l1 l2:list A),
                permut l1 l2->
                op_all l1 =op_all l2.
Proof.
 induction 1.
 auto.
 simpl in |- *.
 rewrite IHpermut; auto.
 simpl in |- *.
 rewrite (op_all_app l (a :: nil)).
 simpl in |- *.
 pattern (op a a_neutral) in |- *.
 rewrite op_com.
 rewrite a_neutral_op.
 rewrite op_com.
 auto.
 rewrite IHpermut1; auto.
Qed.
End op_permut.

(* the permutation of an empty list is an empty list *)
Lemma permut_nil1:forall (l1 l2:list A),
                      permut l1 l2-> 
                      l1=nil->
                      l2=nil.
Proof.
 induction 1.
 auto.
 discriminate 1.
 discriminate 1.
 intro; eauto.
Qed.

(* if a permutation of a list is empty then the first 
 list is also empty *)
Lemma permut_nil2:forall (l1 l2:list A),
                      permut l1 l2-> 
                      l2=nil->
                      l1=nil.
Proof.
 induction 1.
 auto.
 auto.
 discriminate 1.
 case l.
 discriminate 1.
 discriminate 1.
 intro; eauto.
Qed.

Lemma permut_app_com:forall (l1 l2:list A),
                    permut (l1++l2)(l2++l1).
Proof.
 intro l1; elim l1.
 simpl in |- *.
 intro; rewrite <- app_nil_end.
 constructor.
 intros.
 econstructor 4.
 simpl in |- *.
 constructor 3. 
 rewrite app_ass.
 replace (l2 ++ a :: l) with ((l2 ++ a :: nil) ++ l).
 auto.
 rewrite app_ass.
 cut ((a :: nil) ++ l = a :: l).
 intro; subst; auto.
 simpl in |- *.
 auto.
Qed.

(* permut is a symmetric relation *)
Lemma permut_sym:forall (l1 l2:list A),
                  permut l1 l2 ->
                  permut l2 l1.
Proof.
 induction 1.
 constructor.
 constructor; auto.
 replace (a :: l) with ((a :: nil) ++ l).
 apply permut_app_com; constructor.
 simpl in |- *; auto.
 econstructor 4; eauto.
Qed.

(* permut and append *) 
(* generalization of the constructor perm_cons *)
Lemma permut_app_same_l:forall (l l1 l2:list A),
                      permut l1 l2->
                      permut (l++l1)(l++l2).
Proof.
intro l; elim l.
simpl in |- *; auto.
simpl in |- *.
intros; constructor.
auto.
Qed.

Lemma permut_add_a:forall (l1 l2:list A)a,
                   add_somewhere a l1 l2->
                   permut (a::l1) l2.
Proof.
 induction 1.
 constructor.
 econstructor 4.
 econstructor 3. 
 simpl in |- *.
 constructor.
 constructor 4 with (a :: l1).
 apply permut_sym; constructor.
 auto.
Qed.

(**************************************************)
(*   properties about permutation                 *)
(**************************************************)
Lemma mult_app:forall (l1 l2:list A)a, 
 multiplicity (list_contents (eq (A:=A)) decA (l1 ++l2)) a= 
multiplicity (list_contents (eq (A:=A))decA l1) a + multiplicity (list_contents (eq (A:=A))
decA l2) a.
Proof.
 intros l1; elim l1; simpl in |- *.
 auto.
 intros.
 rewrite (H l2 a0).
 omega.
Qed.


Lemma permutation_nil:forall (l:list A),
               permutation  (eq(A:=A)) decA nil l->
               l=nil.
Proof.
 unfold permutation, Multiset.meq in |- *.
 simpl in |- *.
 intro l; case l.
 auto.
 simpl in |- *.
 intros.
 absurd
  (0 = 1 + multiplicity (list_contents (eq (A:=A)) decA l0) a).
 omega.
 replace 1 with (if decA a a then 1 else 0).
 auto.
 case (decA a a).
 auto.
 induction 1.
 auto.
Qed.

Lemma mult_In:forall (l:list A) a,
             multiplicity (list_contents (eq (A:=A)) decA l) a >=1 ->
             In a l.
Proof.
 intro l; elim l.
 simpl in |- *.
 inversion 2.
 intros.
 simpl in H0.
 generalize H0; case (decA a a0).
 intros; subst; simpl in |- *; tauto.
 simpl in |- *.
 intros; right.
 auto.
Qed.

Lemma permutation_uncons:forall (l1 l2:list A) a,
         permutation (eq (A:=A)) decA (a :: l2) (a :: l1) ->
         permutation (eq (A:=A)) decA l2 l1.
Proof.
 unfold permutation, Multiset.meq in |- *.
simpl in |- *.
intros.
pose (H a0).
omega.
Qed.
                        
 
Lemma mult_add_somewhere1:forall (l1 l2:list A) a,
                    add_somewhere a l1 l2->
                   multiplicity (list_contents (eq (A:=A))
                    decA l2) a= S(multiplicity (list_contents (eq (A:=A))
                    decA l1) a).

 Proof.
 induction 1.
 simpl in |- *.
 case (decA a a).
 intro; omega.
 induction 1.
 auto.
 simpl in |- *.
 rewrite IHadd_somewhere; omega.
Qed.

Lemma mult_add_somewhere2:forall (l1 l2:list A) a a0,
                    add_somewhere a l1 l2->
                    a<>a0->
                    multiplicity (list_contents (eq (A:=A))
                    decA l2) a0= multiplicity (list_contents (eq (A:=A))
                    decA l1) a0.

 Proof.
 induction 1.
 simpl in |- *.
 case (decA a a0).
 intros.
 elim H; auto.
 intros; auto.
 simpl in |- *.
 intro; rewrite IHadd_somewhere.
 omega.
 auto.
Qed.

Lemma permutation_add':forall (l1 l2 :list A) a,
         add_somewhere a l1 l2 ->
       forall l3 ,  
          permutation (eq(A:=A)) decA (a::l3) l2->
         permutation (eq(A:=A)) decA l3 l1.
Proof.
 unfold permutation, meq in |- *.
 simpl in |- *.
 intros.
 pose (H0 a0).
 generalize e.
 clear e.
 case (decA a a0).
 intros H1 H2.
 subst.
 rewrite (mult_add_somewhere1 H) in H2.
 omega.
 intros H1 H2; rewrite (mult_add_somewhere2 H H1) in H2.
 omega.
Qed.

(************************************************)
(*               equivalence                    *)
(************************************************)

(* from inductive definition to multiset definition *)
Lemma ind_permu_to_eqmset:forall (l1 l2:list A),
                   permut l1 l2 ->
                   permutation (eq(A:=A)) decA l1 l2.
Proof.
 induction 1.
 apply permut_refl.
 apply permut_cons; auto.
 unfold permutation, meq in |- *.
 simpl in |- *.
 intros.
 rewrite mult_app.
 simpl in |- *.
 omega.
 eapply permut_tran; eauto.
Qed.


(* from multiset definition to inductive definition *)
Lemma eqmset_to_ind:forall (l1 l2:list A),
                   permutation (eq(A:=A)) decA l1 l2->
                    permut l1 l2.
Proof.
 intro l1; elim l1.
 intros.
 rewrite (permutation_nil H).
 constructor.
 intros.
 cut (In a l2).
 intro H1; elim (add_in _ _ H1).
 intros.
 constructor 4 with (a :: x).
 constructor.
 apply H.
 eapply permutation_add'.
 eauto.
 auto.   
 apply permut_add_a; auto.
 apply mult_In.
 unfold permutation, meq in H0.
 simpl in H0.
 rewrite <- (H0 a).
 case (decA a a).
 intro; omega.
 induction 1; auto.
Qed.

End perm.