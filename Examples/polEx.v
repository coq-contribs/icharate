Set Implicit Arguments.

Require Export natDedGram.
Require Export struct_ex.
Require Export tacticsDed.
Require Export polTac.


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
|que|la|raison|ignore|Houda.

Definition lex(w:W):list (Form I J  A ):=
match w with 
|que=>((!n\1 !n)/1 (!s /1 !np))::nil 
|la => (!np /1 !n) ::nil
|raison=> !n::nil
|ignore=> ((!np \1 !s)/1 !np) ::nil
|Houda=>!np::nil
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

Definition ext1:extension I J:=(L2 a) U NL.

(* definition of the grammar *)
Print synGram.

Definition gram1:synGram:=mk_gramS lex1 ext1.


(* proof that the relative clause is an ungrammatical noun modifier*)

Definition cont:=((word 0 que) :>((!n \1 !n)/1 (!s /1 !np)) ,1 ((word 0 la) :>(!np /1 !n) ,1 (word 0 raison) :> !n ) ,1 
(word 0 ignore) :> ((!np\1 !s)/1 !np) ,1 (word 0 Houda) :> !np).



Lemma deriv1: natded eqdecI eqdecJ ext1 cont (!n \1 !n)->False.
intros.
pol eqdecA np.
Qed.
