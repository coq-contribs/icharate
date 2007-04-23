(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2003 -2005                                *)
(*                              LaBRI                                   *)
(************************************************************************)

(* basic definitions for grammars based on natural deduction logic*)


Set Implicit Arguments.
Require Export natDed.
Require Export List.

Section syntaxNatDed.

Variables I
          J
          A
          W:Set.
Variable eqdecI:eqdec I.
Variable eqdecJ :eqdec J.
Variable lexSyn:W ->list (Form I J A).
Variable ext:extension I J.



(* predicate which tests that a given context Gamma is suitable with a sentence sent *)
Fixpoint flattenCont (Gamma:context I J A W)
(laux:list ((resource W)*(Form I J A))) {struct Gamma}:    
list ((resource W)*(Form I J A)):=
match Gamma with
| res r f => (r,f)::laux
| Comma _ G1 G2=> (flattenCont G1 (flattenCont G2 laux)) 
|TDiamond _ G1=> flattenCont G1 laux
end.


Fixpoint fits_aux (l:list ((resource W)*(Form I J A))) (sent:list W){struct l}
:Prop:=
match l with
|nil => match sent with 
 |nil => True
 |others=> False
 end
|cons ((word i w), f) ltail => match sent with
  |cons m1 stail=>match (nth_error (lexSyn w) i) with 
                             |None=>False
                             |Some f1=>w=m1/\ f1=f /\ fits_aux ltail stail
                             end
  |others =>False
end
| _=>False
end.  

Definition fitsContSent(Gamma:context I J A W)(sent:list W):=
fits_aux (flattenCont Gamma nil) sent.

Inductive reduceTo(sent:list W)(f:Form I J A):Set:=
|reduce1:forall (Gamma:context I J A W), 
   natded eqdecI eqdecJ ext Gamma f -> 
   fitsContSent Gamma sent->
   reduceTo sent f.

End syntaxNatDed.

(* definition of records for syntactic analyses *)

Record synLexicon : Type:= 
mk_lexS {
I_syn :Set;
J_syn:Set;
A_syn:Set;
W_syn:Set;
eqdecI_syn:eqdec I_syn;
eqdecJ_syn :eqdec J_syn;
eqdecA_syn:eqdec A_syn;
lex_syn:W_syn ->list (Form I_syn J_syn A_syn)}.


Definition setSynLex(I J :Set)(A:Set)(W:Set)(eqdecI:eqdec I)
 (eqdecJ:eqdec J)(eqdecA :eqdec A)
(lex:W -> list (Form I J A)):synLexicon:=
(mk_lexS eqdecI eqdecJ eqdecA  lex).

Record synGram:Type:=
mk_gramS{
lexic_syn:synLexicon;
ext_syn:extension lexic_syn.(I_syn) lexic_syn.(J_syn)}.


Definition deriveToSyn (gr:synGram):=
reduceTo  (gr.(lexic_syn)).(eqdecI_syn) (gr.(lexic_syn)).(eqdecJ_syn)
  (gr.(lexic_syn)).(lex_syn) gr.(ext_syn).

Hint Unfold deriveToSyn:ctl_db.

(* some notations *)

Notation "'||' gr '||:' sent '>>'  f ":= (deriveToSyn gr sent f) 
(at level 30).
Notation " sent '{{' eqdecI eqdecJ  lex ext '}}' '>->' f " := 
(reduceTo eqdecI eqdecJ lex ext sent f)(at level 20).
