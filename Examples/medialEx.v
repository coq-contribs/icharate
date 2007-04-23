
Set Implicit Arguments.

Require Export natDedGram.
Require Export struct_ex.
Require Export tacticsDed.
Require Export medialExtraction.

(* in this example, we analyze medial extraction phenomena *)

Inductive I:Set:=m1.
Inductive J:Set:= m2.
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
 := (Slash m1 A B) (at level 41,  right associativity) .

Notation " A '\1' B"
 := (Backslash m1 A B) (at level 41,  right associativity).

Notation " A 'o1' B"
 := (Dot m1 A B) (at level 38, left associativity) .

Notation "T1 ,1 T2" :=
(Comma m1 T1 T2)(at level 45, right associativity).

Notation "A ;1 B":=
(comW m1 A B)(at level 42, right associativity).

Notation "'[]0' A" :=(Box m2 A) (at level 30).
Notation "'<>0' A":=(Diamond m2 A)(at level 30).
Notation "'#' w":=(oneW I J w)(at level 40).

Notation "h :> ty":=(res h ty)(at level 35).

(* terminals*)
Inductive W:Set:=|que|Marie|ignore|completement.

Definition lex(w:W):list (Form I J  A ):=
match w with 
|que=>((!n\1 !n)/1 (!s /1 <>0 []0 !np))::nil 
|Marie=> !np ::nil
|ignore=> ((!np \1 !s)/1 !np) ::nil
|completement=> ((!np \1 !s) \1 (!np \1 !s))::nil
end.

Definition lex1:synLexicon.
esplit.
eexact eqdecI.
eexact eqdecJ.
eexact eqdecA.
eexact lex.
Defined.


Definition ext1:extension I J:=(MA2Diam m1 m2) U ((MP1Diam m1 m2) U NL).

(* definition of the grammar *)
Definition gram1:synGram:=mk_gramS lex1 ext1.

Definition frag:=que::Marie::ignore::completement::nil.

Definition my_contW:= #que ;1 #Marie ;1 #ignore ;1 #completement.


Definition treeDeri:||gram1||: frag>>(!n \1 !n).
setCont0 my_contW.
simpl.
eslashE.
axiom.
apply medialExtraction;inExt.
Defined.

