(* example using semantics *)

Require Export final_sem.
Require Export lambda_reduction.
Require Export interp_coq.
Require Export notations.
Open Scope mmg_scope.

Require Export struct_ex.
Require Export tacticsDed.

(* first example of the tutorial *)
(* binary modes of composition *)
Inductive I:Set:=
a.

(* unary modes of composition*)
(* empty set in that case!*)
Inductive J:Set:=.

(* atomic types *)
Inductive A:Set:=|np|s|n.

Definition eqdecI:eqdec I.
solve_eqdec.
Defined.

Definition eqdecJ:eqdec J.
solve_eqdec.
Defined.

Definition eqdecA:eqdec A.
solve_eqdec.
Defined.

Notation "'!' F":=(At (I:=I) (J:=J) F)(at level 40).
Notation "A '/1' B" 
 := (Slash a A B) (at level 42,  left associativity) .

Notation " A '\1' B"
 := (Backslash a A B) (at level 43,  right associativity).

Notation " A 'o1' B"
 := (Dot a A B) (at level 44, right associativity) .

Notation "T1 ,1 T2" :=
(Comma a T1 T2)(at level 45, right associativity).

Notation "A ;1 B":=
(comW a A B)(at level 45, right associativity).
Notation "'#' w":=(oneW I J w)(at level 40).

Notation "h :> ty":=(res h ty)(at level 35).

(* terminals*)
Inductive W:Set:=
|que|la|raison|ignore.

Definition lex(w:W):list ((Form I J  A )*option (lambda_terms logic_cst)):=
match w with 
|que=>((!n\1 !n)/1 (!s /1 !np), 
(Some ([[e-->t]]: [[e-->t]]: [[e]]: (appl (appl (@ AND) (appl (%1) (%0))) 
(appl (%2)(%0))))))::nil
|la => ((!s /1 (!np \1 !s))/1 !n , 
Some ([[e-->t]]: [[e-->t]]: (appl (@EXU) ([[e]]: 
 (appl (appl  (@ AND) (appl (%1) (%0))) (appl
(%2)(%0)))))))::nil
|raison=> (!n, None)::nil
|ignore=> ((!np \1 !s)/1 !np, None) ::nil
end.

(* mapping function *)
Definition map (a :A):semType:=
match a with
|n=>e-->t
|np=>e
|s=>t
end.

(* checking the well formedness of our lexicon *)
Lemma wf_lex:isWellTyped_lex map lex.
solve_wf.
Qed.


(* definition of a two dimensitional lexion *)
Definition lex2:lexicon:=mk_lex eqdecI eqdecJ eqdecA wf_lex.

(* definition of the set of structural rules *)
Definition ext:extension I J:=(L2 a) U NL.


Definition gram2:syn_sem_gram:=mk_gram lex2 ext.

(* definition of the expression to be analized *)
Definition clause:=que::la::raison::ignore::nil.

(* proof that the relative clause is a noun modifier:with type
 !n \1 !n *)
(* bottom-up derivation *)
Definition deriv1:||gram2||s: clause >> (!n \1 !n).
addAxioms0.
elimS Ax0 Ax1.
addHyp 0 (!np).
elimS Ax2 Hyp.
elimS H H0.
z_rootH H1.
structL_asc 0 H1.
introS H1.
elimS Ax H.
endDeriv.
Defined.


(* compute the whole semantics*)
(* we obtain a deeply embedded term, not yet reduced *)
Eval compute in (whole_sem deriv1).

(* after reduction *)
Definition nf_deriv1:hasNormalForm (whole_sem deriv1).
solve_nf.
Defined.

Eval compute in (extractNF nf_deriv1).

Definition noHyps:no_hyps_inside (whole_sem deriv1).
compute.
tauto.
Defined.

Definition wt:isWellTyped (type_cst (W:=W)) nil (whole_sem deriv1) (mapExt map (!n\1 !n)).
apply type_check_wellTyped.
compute;auto.
Defined.

Eval compute in (pretty_printer wt noHyps).