(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                              LaBRI                                   *)
(************************************************************************)

Set Implicit Arguments.
Require Export natDedGram.
Require Export lambda_bruijn.
Require Export logic_const.
(* definition of semantic lexicon *)

(* a list formed of pairs of forms and lambda-terms is well typed
 iff forall (f,l)member of this list, l is of type (map f) *)

Fixpoint isWellTyped_pairs (I J A :Set)(map:A -> semType)
(l:list ((Form I J A) * (option (lambda_terms logic_cst))))
{struct l}:Prop:=
match l with
|nil => False
|(f,None)::nil=>True
|(f,(Some te))::nil => type_check setTypeLog nil te=Some (mapExt map f)
|(f,None)::l1=>isWellTyped_pairs map l1 
|(f,(Some te))::l1=> type_check  setTypeLog nil te =Some (mapExt map f)/\
                               isWellTyped_pairs map l1 
end.

Definition isWellTyped_lex (I J A W :Set)(map:A -> semType)
(lex:W->list ((Form I J A) * (option (lambda_terms logic_cst))))
:=forall (w:W), isWellTyped_pairs map (lex w).

Lemma well_typed_no_empty:forall(I J A W:Set)(map:A -> semType)
(lex:W->list ((Form I J A) * (option (lambda_terms logic_cst)))), 
   isWellTyped_lex map  lex->
  forall (w:W),lex w <>nil.
Proof.
 unfold isWellTyped_lex in |- *; intros.
 generalize (H w); case (lex w).
 simpl in |- *; induction 1.
 intros; auto with datatypes.
Qed.

(* lexicon for syntactic and semantic analysis *)
Record lexicon : Type:= 
mk_lex {
I :Set;
J:Set;
A:Set;
W:Set;
eqdecI:eqdec I;
eqdecJ :eqdec J;
eqdecA:eqdec A;
map:A -> semType;
lex: W -> (list (prod (Form I J A) (option (lambda_terms logic_cst)))); 
wt_lex:isWellTyped_lex map  lex
}.

Definition set_syn_sem_Lex(I J :Set)(A:Set)(W:Set)(consSem:Set)
(eqdecI:eqdec I) (eqdecJ:eqdec J)(eqdecA :eqdec A)(map:A -> semType)
(lex: W -> (list (prod (Form I J A) (option (lambda_terms
logic_cst)))))(wf_lex:isWellTyped_lex map lex)
:lexicon:=
(mk_lex eqdecI eqdecJ eqdecA wf_lex).



Record syn_sem_gram:Type:=
mk_gram{
lexic:lexicon;
ext:extension lexic.(I) lexic.(J)}.

Fixpoint extract_sub_list (I J A:Set)
(l:list ((Form I J A)*(option (lambda_terms logic_cst)))){struct l}:list (Form I J A):=
match l with 
|nil=> nil
|(a,s)::l1=>a::(extract_sub_list l1)
end.
 
Definition extract_lex_syn(I J A W :Set)(l:W->list ((Form I J
A)*(option (lambda_terms logic_cst))))(w:W):list (Form I J A):=
extract_sub_list  (l w).


Definition deriveTo (gr:syn_sem_gram):=
reduceTo  (gr.(lexic)).(eqdecI) (gr.(lexic)).(eqdecJ)
  (extract_lex_syn (gr.(lexic)).(lex)) gr.(ext).

Hint Unfold deriveTo:ctl_db.

(* some notations *)

Notation "'||' gr  '||s:' sent '>>' f ":= (deriveTo gr sent f) (at level
30).



(* to be applied only if W is inductuvely defined *)
Ltac solve_wf:=match goal with
| |-isWellTyped_lex _ _  =>
let wo:=fresh "w" in (
unfold isWellTyped_lex in |- *;intro wo;elim wo;simpl;tauto)
| |- _=>idtac
end.


(*
(* other representation of lexicon using coq-terms
  for semantic *)
Record lexicon_coq : Type:= 
mk_lex_coq {
I_coq :Set;
J_coq:Set;
A_coq:Set;
W_coq:Set;
eqdecI_coq:eqdec I_coq;
eqdecJ_coq :eqdec J_coq;
eqdecA_coq:eqdec A_coq;
map_coq:A_coq -> semType;
lex_coq: W_coq -> (list (prod (Form I_coq J_coq A_coq) pair_var_type))
(*wt_lex:isWellTyped_lex_coq lex*) 
}.

*)