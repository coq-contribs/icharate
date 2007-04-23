Set Implicit Arguments.

Require Export natDedGram.
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
 := (Slash a A B) (at level 41,  right associativity) .

Notation " A '\1' B"
 := (Backslash a A B) (at level 41,  right associativity).

Notation " A 'o1' B"
 := (Dot a A B) (at level 38, left associativity) .

Notation "T1 ,1 T2" :=
(Comma a T1 T2)(at level 45, right associativity).

Notation "A ;1 B":=
(comW a A B)(at level 42, right associativity).
Notation "'#' w":=(oneW I J w)(at level 40).

Notation "h :> ty":=(res h ty)(at level 35).

(* terminals*)
Inductive W:Set:=
|que|la|raison|ignore.


Definition lex(w:W):list (Form I J  A ):=
match w with 
|que=>((!n\1 !n)/1 (!s /1 !np))::nil 
|la => (!np /1 !n) ::nil
|raison=> !n::nil
|ignore=> ((!np \1 !s)/1 !np) ::nil
end.

(* definition of a lexicon: direct way *)

Definition lex1:synLexicon:=(mk_lexS eqdecI eqdecJ eqdecA lex).

(* interactive construction of lexicon *)
Definition lex1':synLexicon.
esplit.
eexact eqdecI.
eexact eqdecJ.
eexact eqdecA.
eexact lex.
Defined.

(* just to test the use of Qed *)
Definition lex_opaq:synLexicon.
esplit.
eexact eqdecI.
eexact eqdecJ.
eexact eqdecA.
eexact lex.
Qed.

(* if we use `Defined' we can access to all the fields of the record*)
 Eval compute in (lex1'.(I_syn)).

(* otherwise, it won't be the case *)
Eval compute in (lex_opaq.(I_syn)).


(* definition of the set of structural rules *)
Definition ext1:extension I J:=(L2 a) U NL.

(* definition of the grammar *)
Print synGram.

Definition gram1:synGram:=mk_gramS lex1 ext1.

(* definition of the expression to be analized *)
Definition clause:=que::la::raison::ignore::nil.

(* proof that the relative clause is a noun modifier:with type
 !n \1 !n *)
(* bottom-up derivation *)

Definition deriv1:||gram1||: clause >> (!n \1 !n).
addAxioms0.
addHyp 0 (!np).
elimS Ax0 Ax1.
elimS Ax2 Hyp.
elimB H0 H.
z_rootH H1.
structL_asc 0 H1.
introS H1.
elimS Ax H.
endDeriv.
Defined.

(* using a top-down fashion *)
(* we should guess the structure of the sentence, it is not always 
 a trivial task!*)

Definition clause_tree:= #que ;1 (#la ;1 #raison) ;1 #ignore.

Definition deriv2:||gram1||: clause >> (!n \1 !n).
setCont0 clause_tree.
eslashE.
axiom.
slashI0.
z_root.
struct 0.
ebackE.
eslashE;axiom.
eslashE;axiom.
Defined.

