(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2003 -2006                                *)
(*                              LaBRI                                   *)
(************************************************************************)



Require Export natDed.
Require Export struct_props.
Require Export  ZArith.
Require Export ZArithRing.


Set Implicit Arguments.
Section unaries.
Variables I J A W:Set.


 Variables (decI:eqdec I) (decJ:eqdec J).




(* some definitions that will be used the theorem bellow *)

Fixpoint diffDiamBox(j:J) (f:Form I J A){struct f}:Z:=
match f with
| At a => 0%Z
| Dot i1 C B => (diffDiamBox j C + diffDiamBox j B)%Z
| Slash i1 C B => (diffDiamBox j C - diffDiamBox j B)%Z
| Backslash i1 B C => (diffDiamBox j C - diffDiamBox j B)%Z
| Box i1 C =>match (decJ i1 j) with
             |left _=>  (diffDiamBox j C - 1%Z)%Z
             |right _ =>diffDiamBox j C
            end
| Diamond i1 C =>match (decJ i1 j) with
             |left _=> (diffDiamBox j C + 1%Z)%Z
             |right _ => diffDiamBox j C
            end
end.

Fixpoint diffDBTerm (j:J)(t:context I J A W){struct t}:Z:=
match t with 
| res _ F => diffDiamBox j F
| Comma i1 T1 T2 => ( diffDBTerm j T1 + diffDBTerm j T2)%Z
| TDiamond i1 T1 =>match (decJ i1 j) with
                   |left _ => (diffDBTerm j T1 + 1%Z)%Z
                   |right _ =>diffDBTerm j T1
                   end
end.

Fixpoint sum_diff_leaves (j:J)(t:context I J A W){struct t}:Z:=
match t with 
| res _ F => diffDiamBox j F
| Comma i1 T1 T2 => (sum_diff_leaves j T1 + sum_diff_leaves j T2)%Z
| TDiamond i1 T1 => sum_diff_leaves j T1
end.

(*Lemma context_leaf:forall (j:J)(t:context I J A W),
                  sum_diff_leaves j t <=diffDBTerm j t.*)
  

Lemma replaceDB:forall (T1 T2 T3 T4:context I J A W)(j:J),
                         replace T3 T4 T1 T2->
                         diffDBTerm j T3=diffDBTerm j T4 ->
                         diffDBTerm j T2 =diffDBTerm j T1.
 Proof.
 intros T1 T2 T3 T4 j H0.
 induction H0.
 auto.
 simpl in |- *.
 intros.
 auto with zarith.
 simpl in |- *; intro; auto with zarith.
 simpl in |- *.
 case (decJ j0 j).
 intros; auto with zarith.
 auto.
Qed.

(* condition on structural rules *)
Definition condStruct(ru:structrule I J):=
  forall T1 T2 j,   apply_rule ru decI decJ T1 =Some T2 ->
                  diffDBTerm j T1=diffDBTerm j T2.

Definition condExt (ext :(extension I J )):= 
forall Ru, in_extension Ru ext ->
           condStruct Ru.

Lemma structRepDB: forall (T1 T2 T3 T4:context I J A W)j(ext :extension I J)Ru,
                       condExt ext->
                       in_extension Ru ext->
                       struct_replace decI decJ Ru T1 T2 T3 T4->
                       diffDBTerm j T3=diffDBTerm j T4.
 Proof.
 induction 3.
 unfold condExt, condStruct in H;eapply H; eauto.
 simpl;auto with zarith.
 simpl in |- *; auto with zarith.
 simpl in |- *;case (decJ j0 j);intro; auto with zarith.
Qed.


(* final theorem *) 
Theorem eqDiffDiamBox:forall (Gamma:context I J A W)(F:Form I J A)j
                             (ext :extension I J),
                             condExt ext  ->
                             natded decI decJ ext Gamma F ->
                             (diffDBTerm j Gamma)=(diffDiamBox j F). 

 intros Gamma F j ext cond H0.
 elim H0; simpl; intros; auto with zarith.
 case (decJ j0 j); auto with zarith.
 generalize H; case (decJ i j); intros; auto with zarith.
 rewrite <- H2; eapply replaceDB;[eauto |simpl; auto with zarith].
 rewrite <- H1; eapply replaceDB;[eauto |simpl; auto with zarith].
 generalize H; case (decJ j0 j); intros; auto with zarith.
 rewrite <- H; eapply structRepDB;eauto.
Qed.

(* corollary of the theorem above *)
 Lemma eqDiffDB:forall (Gamma:context I J A W)(F:Form I J A)j
                             (ext :extension I J),
                             condExt ext  ->
                             (diffDBTerm j Gamma)<>(diffDiamBox j F)->
                              natded decI decJ ext Gamma F ->
                              False.
 intros.
 elim H0.
 eapply eqDiffDiamBox; eauto.
Qed.

(* linear rules that conserve the number of <>j verify the condStruct condition defined in the 
   file unaries.v *)

Lemma linearTocondStruct:forall(ru:structrule I J),
           linearDiam decJ ru  ->
           condStruct ru.
Admitted. (* same as the proof for polarity*)

 
End unaries.
