(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2004                                *)
(*                              LaBRI                                   *)
(************************************************************************)
Add LoadPath "..".
Set Implicit Arguments.
Require Export crossDep.

(* analysis of crossed-dependencies in Dutch: this phenomenon can't be anlysed by a CFG !*)
(* examples taken from 'Labelled Deduction in the composition of Form and Meaning: M.Moortgat 1999*)

Require Export notations.

Inductive I:Set:= |i0|i1.

Definition eqDecI: eqdec I.
 unfold eqdec; decide equality.
Defined.


Inductive W:Set:=
Peter|Mary|wil|plagen|slapen.

(* here the translation of the above words:
  wil --> wants
  plagen-->tease
  slapen-->sleep
  *)

Definition eqDecW:eqdec W.
unfold eqdec; decide equality.
Defined.

Inductive atoms:Set:= np |s|inf.

Definition eqDecA:eqdec atoms.
unfold eqdec; decide equality.
Defined.

Open Scope lamb_scope.
Definition mapping(ato: atoms):semType:=
match ato with
|np =>e
|s=>t
|inf=> e-->t (* a revoir je suis pas du tout sure!*)
end.

Open Scope mmg_scope.
Notation "'!' F":=(At F)(at level 40):mmg_scope.
Notation "A '/o' B" 
 := (Slash i0 A B) (at level 41,  right associativity) : mmg_scope.

Notation " A '\o' B"
 := (Backslash i0 A B) (at level 41,  right associativity) : mmg_scope.

Notation " A 'Oo B"
 := (Dot i0 A B) (at level 38, left associativity) : mmg_scope.

Notation "'[]o' A" :=(Box i0 A) (at level 30):mmg_scope.
Notation "'<>o' A":=(Diamond i0 A)(at level 30):mmg_scope.


Notation "A '/1' B" 
 := (Slash i1 A B) (at level 41,  right associativity) : mmg_scope.

Notation " A '\1' B"
 := (Backslash i1 A B) (at level 41,  right associativity) : mmg_scope.

Notation " A 'O1 B"
 := (Dot i1 A B) (at level 38, left associativity) : mmg_scope.

Notation "'[]1' A" :=(Box i1 A) (at level 30):mmg_scope.
Notation "'<>1' A":=(Diamond i1 A)(at level 30):mmg_scope.

(* set of semantic constants*)
Inductive consSem:Set:=
|mary|peter|wi|plag|slap.



Notation "'$' n" :=(num (semRess I I atoms W) n) (at level 40):mmg_scope.
Notation "% n" :=(num consSem n)(at level 40):mmg_scope.
Notation "'#' w":= (oneW I I  w)(at level 40):mmg_scope .
Notation " T1 ';1' T2 ":=(comW i1 T1 T2)(at level 41,right associativity):mmg_scope.
Notation " T1 ';o' T2 ":=(comW i0 T1 T2)(at level 41,right associativity):mmg_scope.

Definition setType(cs:consSem):semType:=
match cs with 
| peter => e
| mary => e
|wi =>(e-->t)-->e-->t
|plag=>(intention (e-->e-->t))
|slap=>(intention (e-->t))
end.

Definition lexic(w:W):list (prod (Form I I atoms) (lambdaC consSem)):=
match w with
|Peter => (! np , @peter)::nil
|Mary =>(! np, @mary)::nil
|wil=>([]o ((! np \1 !s)/o !inf) ,@wi)::nil
|plagen=>([]o (!np \1 !inf) ,@plag)::nil
|slapen=>([]o (!inf) ,@slap)::nil
end.

Definition lexic1:lexicon.
econstructor.
eexact eqDecI.
eexact eqDecI.
eexact eqDecA.
eexact eqDecW.
eexact mapping.
eexact setType.
eexact lexic.
Defined.

Definition ext:=add_rule (K2Diam i1 i1) (add_rule (incDiam I i1 i0) 
         (add_rule (KDiam i0 i0) (add_rule (MPDiam i1 i0 i0) NL))).
Definition gram:Grammar.
eapply mk_gram with (lexic:=lexic1).
simpl.
exact ext.
Defined.

Definition frag:= Mary::wil::slapen::nil.

Definition my_contextW:= #Mary ;1 #wil ;o #slapen.

Definition treeDeriv:[gram] frag>>[]1 (!s).
unfold deriveTo.
setCont0 my_contextW.
simpl.
boxI.
unfold ext.
eapply cross_depend.
repeat econstructor. (* faire une tactique !*)
repeat econstructor.
repeat econstructor.
simpl.
ebackE.
axiom.
eslashE.
boxE.
axiom.
boxE.
axiom.
Defined.

Definition frag2:=Peter::Mary::wil::plagen::nil.
Definition cw:= #Peter ;1 #Mary ;1 #wil ;o #plagen.
Definition tree2: [gram] frag2>> []1 (!s).
unfold deriveTo.
setCont0 cw.
simpl.
boxI.
eapply cross_depend;unfold ext.
repeat constructor.
repeat constructor.
repeat constructor.
simpl.
eapply StructRule.
constructor 2.
constructor 2.
constructor 2.
constructor 1.
constructor 3.
constructor.
apply MPDiam_rw.
ebackE.
axiom.
eslashE.
boxE.
axiom.
ebackE.
axiom.
boxE;axiom.
Defined.

