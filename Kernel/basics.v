(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2006                                *)
(*                              LaBRI                                   *)
(************************************************************************)

Require Export Arith.
Require Export listAux.
Set Implicit Arguments.

Section Definitions.
 Definition eqdec (X:Set) := forall x y: X, {x=y}+{x<>y}.
Hint Unfold eqdec.

Section Main.
 Variables 
           I (* composition modes *)
           J (* unary modes *) 
           : Set.
 
 Section formulae_etc.
  Variable A W : Set.

(* definition of formulas *)
  Inductive Form   : Set :=
   | At : A -> Form 
   | Slash : I -> Form  -> Form  -> Form  
   | Backslash : I -> Form -> Form  -> Form 
   | Dot : I -> Form  -> Form  -> Form  
   | Box : J -> Form  -> Form  
   | Diamond : J -> Form  -> Form .
 
  (* decidability of equality within Form *) 
Definition eqDecF:forall(eqdecI :eqdec I) (eqdecJ :eqdec J) 
 (eqdecA :eqdec A), eqdec Form.
 intros; unfold eqdec.
 decide equality.
Defined.
 (* resources that will be used as leaves in the context *)
  Inductive resource : Set :=
   | word : nat -> W -> resource
   | hyp : nat -> resource.

 (* decidability of equality within the set of resources*)
 Definition eqdecRess:forall(eqdecW:eqdec W), eqdec resource.
  intros;unfold eqdec; decide equality.
  generalize n n0; decide equality.
  generalize n n0; decide equality.
Defined.

  Inductive bcontext : Set := (* bare contexts, without resources *)
  | form : Form -> bcontext
  | bComma : I -> bcontext -> bcontext -> bcontext
  | bDiamond : J -> bcontext -> bcontext.

  (* contexts with resources *)
  Inductive context  : Set :=
   | res  : resource -> Form -> context
   | Comma : I -> context -> context -> context
   | TDiamond : J -> context -> context.

Inductive is_sub_cont (T1:context):context ->Prop:=
|sub_all:is_sub_cont T1 T1
|sub_left:forall T2 T3 i, is_sub_cont T1 T2->
                                   is_sub_cont T1 (Comma i T2 T3)
|sub_right:forall T2 T3 i,is_sub_cont T1 T3->
                                   is_sub_cont T1 (Comma i T2 T3)
|sub_diam:forall T2 j, is_sub_cont T1 T2->
                                  is_sub_cont T1 (TDiamond j T2).


(* decidability of equality within the set of contexts*)
 Definition eqdecC:forall(eqdecI :eqdec I) (eqdecJ :eqdec J) 
 (eqdecA :eqdec A)(eqdecW:eqdec W), eqdec context.
  intros;unfold eqdec; decide equality.
  apply eqDecF; auto.
  apply eqdecRess; auto.
Defined.

  Inductive hcontext : Set := (* context with holes *)
   | hres :  resource -> Form -> hcontext
   | hComma : I -> hcontext -> hcontext -> hcontext
   | hDiamond : J -> hcontext -> hcontext
   | hole : hcontext.

   Fixpoint fill (h:hcontext)(Gamma : context) {struct h} : context :=
   match h with hole => Gamma
              | hComma i h1 h2 => Comma  i (fill  h1 Gamma) (fill h2 Gamma)
              | hDiamond j h1 => TDiamond  j (fill h1 Gamma)
              | hres r F => res r F
           end.

 
 Fixpoint context_inject (Gamma:context) : hcontext :=
  match Gamma with
  | res r F => hres r F
  | Comma i Gamma1 Gamma2 => hComma i (context_inject Gamma1)
                                      (context_inject Gamma2)
  | TDiamond j Gamma1 => hDiamond j (context_inject Gamma1)
  end.
  
 (* definition of function that converts a context to a form *)
  Fixpoint contextToForm (T:context) : Form :=
   match T with
   | res r f => f
   | Comma i t1 t2 =>
       Dot i (contextToForm t1) (contextToForm t2)
   | TDiamond j t => Diamond j (contextToForm t)
   end.
 

 (* from Huet's zippers *)

  Inductive zcontext : Set := (* context with 1 hole *)
   | zroot : zcontext
   | zleft  : I ->  zcontext -> context -> zcontext
   | zright : I -> context->  zcontext -> zcontext
   | zdown : J ->  zcontext -> zcontext.

  Fixpoint zfill (z:zcontext)(Gamma : context) {struct z} : context :=
   match z with zroot => Gamma
              | zleft i z1 Gamma2 => 
                   zfill z1 (Comma  i Gamma Gamma2)
              | zright i Gamma1 z2 => 
                   zfill z2 (Comma i Gamma1 Gamma)
              | zdown j z1 => zfill z1 (TDiamond j Gamma)
           end.

 Fixpoint zcontext_inject_aux (zx:zcontext)(hc : hcontext){struct zx}
   :hcontext
   := match zx with
   | zroot => hc
   | zleft  i zc1 c2 => 
       zcontext_inject_aux zc1 (hComma i hc (context_inject c2))
   | zright  i c1 zc2 => 
      zcontext_inject_aux zc2 (hComma i (context_inject c1) hc)
   | zdown j zc1 =>  zcontext_inject_aux zc1 (hDiamond j hc)
 end.

 Definition zcontext_inject zc : hcontext :=
   zcontext_inject_aux zc hole.

 Fixpoint zgraft (z z': zcontext){struct z} : zcontext :=
   match z with
  | zroot => z'
  | zleft i zc1 c2 => zleft i (zgraft zc1 z') c2
  | zright i c1 zc2 => zright i c1 (zgraft zc2 z')
  | zdown j zc1 => zdown j (zgraft zc1 z')
 end.

 Lemma zgraft_def : forall z z' c,
      zfill (zgraft z z') c = zfill z' (zfill z c).
  induction z.
  simpl.
  auto.
  intros; simpl; auto.
  intros; simpl; auto.
  intros; simpl; auto.
 Qed.

Theorem no_holes : forall (Gamma Delta:context),
     fill (context_inject Gamma) Delta = Gamma.
Proof.
 induction Gamma;simpl;auto.
 intros;rewrite IHGamma1; rewrite IHGamma2;auto.
 intros;rewrite IHGamma; auto. 
Qed.

Lemma zfill_fill_0 : forall (zc:zcontext)(hc:hcontext)(c:context),
   zfill zc (fill hc c) = fill (zcontext_inject_aux zc hc) c.
Proof.
 induction zc.
 simpl; auto.
 intros.
 simpl.
 rewrite <- IHzc.
 simpl.
 rewrite no_holes.
 auto.
 intros.
 simpl.
 rewrite <- IHzc.
 simpl.
 rewrite no_holes.
 auto.
 intros.
 simpl.
 rewrite <- IHzc.
 simpl.
 trivial.
Qed.

Theorem zfill_fill : forall (zc:zcontext)(c:context),
   zfill zc c = fill (zcontext_inject zc) c.
Proof.
 unfold zcontext_inject.
 intros; rewrite <- zfill_fill_0.
 simpl.
 auto.
Qed.


Inductive matches : bcontext -> context -> Prop :=
 |  form_matches : forall F r, matches (form F) (res r F)
 |  comma_matches : forall (i:I) b1 b2 Gamma1 Gamma2,
           matches b1 Gamma1 -> matches b2 Gamma2 ->
           matches (bComma i b1 b2) (Comma i Gamma1 Gamma2)
 |  diam_matches : forall (j:J) b  Gamma ,
           matches b Gamma ->
           matches (bDiamond j b) (TDiamond j Gamma).
                   
Fixpoint context_strip (Gamma :context): bcontext :=
  match Gamma with
  | res r F => form F
  | Comma i Gamma1 Gamma2 => bComma i (context_strip Gamma1) 
                                      (context_strip Gamma2) 
  | TDiamond j Gamma1 => bDiamond j (context_strip Gamma1)
  end.

 Theorem strip_match : forall Gamma : context,
                        matches (context_strip Gamma) Gamma.
 Proof.
   induction Gamma;simpl; constructor; auto.
 Qed.
 



Theorem match_strip : forall bGamma Gamma,
                         matches bGamma Gamma -> bGamma = context_strip Gamma.
 induction 1;   simpl ; auto.
 rewrite IHmatches1; rewrite IHmatches2; auto.
 rewrite IHmatches; auto.
 Qed.
 
(* definition of an equivalence relation between contexts *)
 Definition context_equiv Gamma Gamma' :=
        (context_strip Gamma)=(context_strip Gamma').

 Inductive context_eqv:context ->context ->Set:=
 |form_eqv:forall F r1 r2, context_eqv (res r1 F) (res r2 F)
 | com_eqv:forall Gamma1 Gamma2 Gamma1' Gamma2' (i:I),
               context_eqv Gamma1 Gamma1'->context_eqv Gamma2 Gamma2'->
               context_eqv (Comma i Gamma1 Gamma2) (Comma i Gamma1' Gamma2')
 |diam_eqv:forall (j:J)Gamma1 Gamma1' , context_eqv Gamma1 Gamma1'->
                                      context_eqv (TDiamond j Gamma1) (TDiamond j Gamma1').
(* a faire si c'est vraiment obligatoire
 Theorem context_eq_refl:forall (Gamma Gamma':context),
        context_equiv Gamma Gamma'->
        context_eqv Gamma Gamma'.

*)

 Definition matches_inv_form : forall F Gamma, matches (form F) Gamma ->
          {r: resource | Gamma = res r F}.
  intros F Gamma;case Gamma.
  intros r f H; exists r;inversion H; trivial.
  intros; cut False.
  destruct 1.
  inversion H.
  intros; cut False.
  destruct 1.
  inversion H.
 Defined.

 Definition matches_inv_Comma : forall i b1 b2  Gamma,
        matches (bComma i b1 b2) Gamma ->
        {Gamma1 : context & {Gamma2 : context | 
                                  Gamma = Comma i Gamma1 Gamma2 /\
                                  matches b1 Gamma1 /\
                                  matches b2 Gamma2}}.
 intros i b1 b2 Gamma; case Gamma.
 intros r f H; cut False.
 induction 1.
 inversion H.
 intros i0 c c0 H; exists c;exists c0; inversion H.
 split; auto.
 intros j c H;cut False.
 induction 1.
 inversion H.
 Defined.


 Definition matches_inv_Diam : forall j b  Gamma,
        matches (bDiamond j b) Gamma ->
        {Gamma1 : context | Gamma = TDiamond j Gamma1 /\
                                  matches b Gamma1}.
  intros j b Gamma; case Gamma.
  intros r f H; cut False.
  induction 1.
  inversion H.
  intros i c c0 H; cut False.
  induction 1.
  inversion H.
  intros j0 c H.
  exists c;inversion H;split; auto.
 Defined.

End formulae_etc.

Inductive rule_pattern : Set :=
 |  pvar : nat -> rule_pattern
 |  pcomma : I -> rule_pattern -> rule_pattern -> rule_pattern
 |  pdiam : J -> rule_pattern -> rule_pattern.

Fixpoint flatten_pattern(rp:rule_pattern):list nat:=
match rp with 
|pvar i => i::nil
|pcomma i T1 T2=>flatten_pattern T1 ++ flatten_pattern T2
|pdiam j T1=>flatten_pattern T1
end.


  (* symbolic structural rule *)
 Definition structrule := prod rule_pattern rule_pattern.

Inductive hasSubContexts (A W:Set): rule_pattern->context A W->list
(context A W)->Prop:=
|has_pvar:forall (i:nat)(Delta:context A W), 
   hasSubContexts (pvar i) Delta (Delta::nil)
|has_pcom:forall r1 r2 Delta1 Delta2 l1 l2 i,
                 hasSubContexts r1 Delta1 l1->
                 hasSubContexts r2 Delta2 l2->
                 hasSubContexts (pcomma i r1 r2)(Comma i Delta1
		 Delta2) (l1++l2)
|has_pdiam:forall  r Delta l j, 
              hasSubContexts r Delta l->
              hasSubContexts (pdiam j r) (TDiamond j Delta) l.



(* some functions *)
Fixpoint isLeaf (n:nat)(rp1 :rule_pattern){struct
rp1}:Prop:=
match rp1 with
|pvar j=> n=j
|pcomma i r1 r2=>(isLeaf n r1)\/(isLeaf n r2)
|pdiam _ r1 =>(isLeaf n r1)
end.

Lemma in_isLeaf:forall (rp:rule_pattern )n,
                In n (flatten_pattern rp)->
                isLeaf n rp.
Proof.
 intro rp; elim rp; simpl in |- *.
 intros n n0; induction 1.
 auto.
 tauto.
 intros.
 elim (in_app_or _ _ _ H1).
 intro; left; auto.
 intro; right; auto.
 auto.
Qed.

Lemma isLeaf_in:forall (rp:rule_pattern)n,
                isLeaf n rp->
                 In n (flatten_pattern rp).
Proof.
intro rp; elim rp; simpl in |- *.
intros; left; auto.
intros.
apply in_or_app.
case H1.
intro; left; auto.
intro; right; auto.
auto.
Qed.

Fixpoint noIntersection(rp1 rp2:rule_pattern){struct rp1}:Prop:=
match rp1 with
| pvar i => ~ (isLeaf i rp2)
|pcomma i r1 r2 =>noIntersection r1 rp2 /\ noIntersection r2 rp2
|pdiam i r1 =>noIntersection r1 rp2
end.


Fixpoint allDistinctLeaves (rp1:rule_pattern){struct rp1}:Prop:=
match rp1 with
|pvar i =>True
|pcomma i r1 r2=> allDistinctLeaves r1 /\  allDistinctLeaves r2 /\
 noIntersection r1 r2
|pdiam j r1 =>allDistinctLeaves r1 
end.

Fixpoint isIncluded (rp1 rp2:rule_pattern){struct
rp1}:Prop:=
match rp1 with 
|pvar i=>isLeaf i rp2
|pcomma _ r1 r2=>isIncluded r1 rp2 /\ isIncluded r2 rp2
|pdiam _ r1=>isIncluded r1 rp2
end.

(* some auxiliary lemmas about the functions above *)
Lemma noIntersectionLeaf:forall n (rp1 rp2:rule_pattern) , 
    noIntersection rp1 rp2 ->
    isLeaf n rp1->
   ~isLeaf n rp2.
 intros n rp1; elim rp1.
 simpl in |- *.
 intros; subst; auto.
 intros.
 simpl in H2.
 simpl in H1.
 elim H1; intros.
 elim H2; eauto.
 simpl in |- *.
 auto.
Qed.


Definition isLeaf_dec:forall (n:nat)(rp:rule_pattern), 
                 {isLeaf n rp}+{~ isLeaf n rp}.
 intros; elim rp.
 intros.
 simpl in |- *.
 elim (eq_nat_dec n n0).
 intro; left; auto.
 intro; right; auto.
 intros.
 elim H; elim H0; intros.
 left; simpl in |- *; tauto.
 left; simpl in |- *; tauto.
 left; simpl in |- *; tauto.
 right; simpl in |- *; tauto.
 intros.
 elim H; intros.
 left; simpl in |- *; auto.
 right; simpl in |- *; auto.
Defined.

Definition isLeaf_dec_com:forall (rp1 rp2:rule_pattern)(i:I)n,
                      noIntersection rp1 rp2 ->
                     isLeaf n (pcomma i rp1 rp2) ->
                     {isLeaf n rp1 /\ ~ isLeaf n rp2}+
                     {isLeaf n rp2 /\ ~ isLeaf n rp1}.

 simpl in |- *.
 intros.
 case (isLeaf_dec n rp1).
 case (isLeaf_dec n rp2).
 intros.
 elim (noIntersectionLeaf _ _ _ H i1).
 auto.
 intros; left; tauto.
 intro; elim (isLeaf_dec n rp2).
 intro.
 right; tauto.
 intro.
 cut False.
 intro F; elim F.
 elim H0; tauto.
Defined.


Lemma noInter_pattern_to_list:forall (rp1 rp2:rule_pattern),
                              noIntersection rp1 rp2->
                              noInter (flatten_pattern rp1)
                              (flatten_pattern rp2).
Proof.
 intro rp1; elim rp1; simpl in |- *.
 intros; split.
 red in |- *.
 intro; elim H.
 apply in_isLeaf; auto.
 auto.
 intros.
 apply noInter_app.
 elim H1; auto.
 elim H1; auto.
 auto.
Qed.

Lemma allDistinct_to_distinct:forall (rp:rule_pattern),
                              allDistinctLeaves rp->
                              distinct_elts (flatten_pattern rp).
 intro rp; elim rp; simpl in |- *.
 tauto.
 intros.
 decompose [and] H1; clear H1.
 apply distinct_app; auto.
 apply noInter_pattern_to_list; auto.
 auto.
Qed.


Lemma isIncluded_to_isIncl:forall(r1 r2:rule_pattern),
                         isIncluded r1 r2->
                         isIncl (flatten_pattern r1)(flatten_pattern
                              r2).
Proof.
 intro r1; elim r1; simpl in |- *.
 intros.
 split.
 apply isLeaf_in; auto.
 auto.
 intros.
 case H1; intros.
 apply isIncl_app; auto.
 auto.
Qed.


Inductive same_shape(A W:Set): rule_pattern->(context A
W)->Prop:=
|same_shape_leaf:forall(n:nat) Gamma, same_shape (pvar n) Gamma
|same_shape_comma:forall(i:I)(r1 r2:rule_pattern)(Gamma1
Gamma2:context A W), same_shape r1 Gamma1->
                     same_shape r2 Gamma2 ->
                     same_shape (pcomma i r1 r2) (Comma i Gamma1
		     Gamma2)
|same_shape_diam:forall(j:J)(rp:rule_pattern)(Gamma:context A W),
                    same_shape rp Gamma->
                    same_shape (pdiam j rp) (TDiamond j Gamma).


Lemma subCont_same_shape:forall (A W:Set) rp Gamma,
                          same_shape rp Gamma->
                         (exists l:list (context A W),
                          hasSubContexts rp Gamma l).
Proof.
 induction 1.
 econstructor; econstructor.
 elim IHsame_shape1.
 elim IHsame_shape2.
 intros; econstructor; econstructor; eauto.
 elim IHsame_shape.
 intros; econstructor; econstructor; eauto.
Qed.

Lemma same_shape_SubCont:forall  (A W:Set) rp (Gamma:context A W)l,
                          hasSubContexts rp Gamma l->
                           same_shape rp Gamma.
Proof.
 induction 1.
 constructor.
 constructor; auto.
 constructor; auto.
Qed.

Lemma nth_flatten_leaf:forall rp i n,
         nth_error (flatten_pattern rp) i=Some n-> 
         isLeaf n rp.
Proof.
 intro rp; elim rp; intros.
 generalize H; clear H; case i.
 simpl in |- *.
 injection 1; auto.
 simpl in |- *.
 intro n1; case n1; simpl in |- *.
 discriminate 1.
 discriminate 2.
 simpl in |- *.
 simpl in H1.
 elim (nth_error_app _ _ _ H1).
 intro; left; eauto.
 intro K;decompose [and] K;clear K; right; eauto.
 simpl in H0; simpl in |- *; eauto.
Qed.

Definition sameShapeCom:forall(A W:Set) (rp1 rp2:rule_pattern)(Gamma:context A W)i,
                        same_shape (pcomma i rp1 rp2) Gamma->
                        {Gamma1:context A W&{Gamma2:context  A W|Gamma=(Comma i Gamma1 Gamma2) /\
                                      same_shape rp1 Gamma1 /\same_shape rp2 Gamma2}}.
 intros.
 generalize H; clear H.
 case Gamma; intros.
 cut False.
 tauto.
 inversion H.
 econstructor; econstructor.
 split.
 cut (i = i0).
 intro; subst; auto.
 inversion H.
 auto.
 split; inversion H; auto.
 cut False.
 tauto.
 inversion H.
Defined.


            
Definition sameShapeDiam:forall(A W:Set) (rp1:rule_pattern)(Gamma:context A W)i,
                        same_shape (pdiam i rp1) Gamma->
                        {Gamma1:context A W|Gamma=(TDiamond i Gamma1) /\
                                    same_shape rp1 Gamma1}.
 intros.
 generalize H; clear H.
 case Gamma.
 intros; cut False.
 tauto.
 inversion H.
 intros; cut False.
 tauto.
 inversion H.
 intros.
 econstructor; cut (j = i).
 intro; subst.
 split.
 auto.  
 inversion H.
 auto.
 inversion H; auto.
Defined.



(* compilation from abstract rules to concrete rules 
    with the help of Paul Gloess *)

Fixpoint access (A W:Set)(eqdecI :eqdec I)(eqdecJ :eqdec J)
(rp:rule_pattern)(j:nat){struct rp}:(context A W)->(option (context A W))*bool:=
match rp with 
|pvar i =>match (eq_nat_dec i j) with
          |right _ =>fun Gamma:(context A W) =>(None, true)
          |left _ =>fun Gamma:(context A W) =>((Some Gamma),true)
          end
|pcomma i rp1 rp2=>(fun Gamma:context A W=> 
                                  match Gamma with
                                  |Comma l Gamma1 Gamma2 =>match (eqdecI l i) with
                                   |right _ =>(None,false)
                                   |left _ =>match (access eqdecI eqdecJ rp1 j Gamma1) with
                                            |(None, false)=> (None,false)
                                            |(None,true) =>(access eqdecI eqdecJ rp2 j Gamma2) 
                                            |((Some Delta),b)=> match (access eqdecI eqdecJ rp2 j Gamma2) with
                                                    |((Some _), _ )=>(None,false)
                                                    |(None,true) => ((Some Delta),b)
                                                    |(None, false)=>(None,false)
                                                     end end
                                    end
                                  |other =>(None,false)
                               end)
|pdiam i rp1 =>(fun Gamma:context A W=> 
                                  match Gamma with
                                  |TDiamond l Gamma1 =>
                                 match (eqdecJ i l) with 
                                   |right _ => (None,false)
                                   |left _ =>(access eqdecI eqdecJ rp1 j Gamma1)
                                   end
                                  |other => (None,false)
                                 end)
end.


Fixpoint compile (A W:Set)(eqdecI :eqdec I)(eqdecJ:eqdec J)
(rp1 rp2:rule_pattern){struct rp2}:(context A W) -> (option (context A W)):=
match rp2 with
|pvar i => fun Gamma:(context A W)=> match (access eqdecI eqdecJ rp1 i Gamma) with 
           |((Some Gamma') ,_ )=> Some Gamma'
           |other =>None
         end
|pcomma i r1 r2=>fun Gamma:(context A W) => match (compile eqdecI eqdecJ rp1 r1 Gamma) with
                                             |None =>None
                                             |Some Delta1 => match (compile eqdecI eqdecJ rp1 r2 Gamma) with
                                                  |None =>None
                                                  |Some Delta2 =>Some (Comma i Delta1 Delta2)
                                                  end
                                              end
|pdiam i r1=>fun Gamma:(context A W) =>match (compile eqdecI eqdecJ rp1 r1 Gamma) with
                                             |None =>None
                                             |Some Delta1 =>Some (TDiamond i Delta1)
                                              end
end.

 Definition apply_rule (st:structrule)(eqdecI: eqdec I)(eqdecJ : eqdec
       J)(A W:Set): context A W -> option (context A W):=
match st with
| (r1,r2)=>compile  eqdecI eqdecJ r1 r2
end.

Lemma subCont_length:forall (A W:Set) rp (Gamma:context A W) l,
                      hasSubContexts rp Gamma l->
                      length l=length (flatten_pattern rp).
Proof.
 induction 1.
 simpl in |- *; auto.
 simpl in |- *.
 rewrite length_app.
 rewrite length_app.
 auto.
 simpl in |- *; auto.
Qed.


                     
 Parameter bapply_rule :  structrule -> eqdec I -> eqdec J -> forall A,
       bcontext A -> option (bcontext A).


 (* extension is the data type that represents the set of structural rules*)
 Inductive extension : Type := 
      NL : extension
    | add_rule : structrule -> extension -> extension.

 Fixpoint add_extension (e e':extension) {struct e} :extension :=
  match e with
  | NL => e'
  | add_rule r e'' => add_rule r (add_extension e'' e')
  end.

 Inductive in_extension (s: structrule) :extension -> Prop :=
 | in_extension_rule : forall e, in_extension s (add_rule s e)
 | in_extension_right : forall e s',
                      in_extension s e ->
                      in_extension s (add_rule s' e).


 Section rep.

 Variables A W: Set.

 
 (* replace Delta Delta' Gamma Gamma' means :
    Gamma = Gamma0[Delta] and Gamma'=Gamma0[Delta'] 
    replacement at one location (one hole in Gamma0)
 *)
   
 Inductive replace (Delta Delta':context A W): 
    context A W -> context A W  -> Set :=
   | replaceRoot :  replace Delta Delta' Delta Delta'
   | replaceLeft :
       forall (Gamma1 Gamma2 Gamma3:context A W) (i:I),
         replace Delta Delta' Gamma1 Gamma2 ->
         replace  Delta Delta'  (Comma i Gamma1 Gamma3) 
                                (Comma i Gamma2 Gamma3)
   | replaceRight :
       forall (Gamma1 Gamma2 Gamma3:context A W) (i:I),
         replace Delta Delta' Gamma1 Gamma2 ->
         replace  Delta Delta'  (Comma i Gamma3 Gamma1) 
                                (Comma i Gamma3 Gamma2)
    | replaceDiamond :
       forall (Gamma1 Gamma2 :context A W) (j:J),
         replace Delta Delta' Gamma1 Gamma2 ->
         replace Delta Delta' (TDiamond j Gamma1) (TDiamond j Gamma2).

 (* generalisation of replace to any number of holes in Gamma0 *)
 Inductive par_replace (Delta Delta':context A W):
    context A W -> context A W -> Set :=
   | par_zero : forall Gamma, par_replace Delta Delta' Gamma Gamma 
   | par_root :  par_replace Delta Delta' Delta Delta'
   | par_replaceBin :
       forall (Gamma1 Gamma2 Gamma3 Gamma4 :context A W) (i:I),
         par_replace Delta Delta' Gamma1 Gamma3 ->
         par_replace Delta Delta' Gamma2 Gamma4 ->
         par_replace  Delta Delta'  (Comma i Gamma1 Gamma2) 
                                (Comma i Gamma3 Gamma4)
   | par_replaceDiamond :
       forall (Gamma1 Gamma2 :context A W) (j:J),
         par_replace Delta Delta' Gamma1 Gamma2 ->
         par_replace Delta Delta' (TDiamond j Gamma1) (TDiamond j Gamma2).



  Definition repToParRep:forall (T1 T2 T3 T4:context A W),
     replace T1 T2 T3 T4 -> par_replace T1 T2 T3 T4.
  induction 1; repeat constructor; auto.
Defined.


  Definition zfill_to_replace_0 : 
   forall (Delta1 Delta2: context A W)(ZGamma : zcontext A W)
     (Gamma1 Gamma2:context A W),
     replace Delta1 Delta2 Gamma1 Gamma2 ->
     replace Delta1 Delta2 (zfill ZGamma Gamma1) (zfill ZGamma Gamma2).

  induction ZGamma.
  simpl;auto.
  simpl; intros.
  apply IHZGamma.
  constructor 2.
  auto.
  simpl; intros.
  apply IHZGamma.
  constructor 3.
  auto.
  simpl; intros.
  apply IHZGamma.
  constructor 4.
  auto.
Defined.


Definition zfill_to_replace : 
   forall (ZGamma : zcontext A W)(Delta1 Delta2: context A W),
     replace Delta1 Delta2 (zfill ZGamma Delta1) (zfill ZGamma Delta2).
  
  intros; apply zfill_to_replace_0. 
  constructor 1. 
 Defined.

Definition replace_to_zfill:
   forall (Delta1 Delta2 Gamma1 Gamma2: context A W),
    replace Delta1 Delta2 Gamma1 Gamma2 ->
      {ZGamma : zcontext A W | zfill ZGamma Delta1 = Gamma1 /\
                               zfill ZGamma Delta2 = Gamma2}.
   induction 1.  
   exists (zroot A W).
   simpl; split; auto.
   case IHreplace; intros Z1 [e1 e2].
   exists (zgraft Z1 (zleft i (zroot _ _)  Gamma3)).
   rewrite zgraft_def.
   rewrite zgraft_def.
   simpl.
   rewrite e1;rewrite e2; auto.
   case IHreplace; intros Z1 [e1 e2].
   exists (zgraft Z1 (zright i Gamma3  (zroot _ _))).
   rewrite zgraft_def.
   rewrite zgraft_def.
   simpl.
   simpl.
   rewrite e1;rewrite e2; auto.
   case IHreplace; intros Z1 [e1 e2].
   exists (zgraft Z1 (zdown j (zroot _ _))).
   rewrite zgraft_def.
   rewrite zgraft_def.
   simpl.
   rewrite e1;rewrite e2; auto.
Defined.


Definition fill_to_par_replace :
     forall (HGamma : hcontext A W)(Delta1 Delta2: context A W),
     par_replace Delta1 Delta2 (fill HGamma Delta1) (fill HGamma Delta2).

 simple induction HGamma.
 simpl.
 constructor 1.
 simpl; intros.
 constructor 3.
 auto.
 auto.
 simpl; constructor 4; auto.
 simpl;constructor 2.
Defined.

Definition par_replace_to_fill:
   forall (Delta1 Delta2 Gamma1 Gamma2: context A W),
    par_replace Delta1 Delta2 Gamma1 Gamma2 ->
      {HGamma : hcontext A W | fill HGamma Delta1 = Gamma1 /\
                               fill HGamma Delta2 = Gamma2}.
    induction 1. 
    elim Gamma. 
    intros r f;exists (hres r f);simpl.
    split;auto.
    intros.
    case H; intros HG1 H1; case H0; intros HG2 H2.    
    exists (hComma i HG1 HG2); simpl; auto.
    case H1; case H2; intros.
    rewrite H3; rewrite H4 ; rewrite H5 ; rewrite H6.
    split; auto.
    intros.
    case H; intros HG1 [H1 H2].
    exists (hDiamond j HG1); simpl.
    rewrite H1; rewrite H2; auto.
    exists (hole A W).
    simpl; auto.
    case IHpar_replace1; intros HG1 [e1 e2].
    case IHpar_replace2; intros HG2 [e3 e4].
    exists (hComma i HG1 HG2).
    simpl; rewrite e1;rewrite e2;rewrite e3;rewrite e4; auto.
    case IHpar_replace; intros HG1 [e1 e2].
    exists (hDiamond j HG1).
    simpl;rewrite e1; rewrite e2;auto.
 Defined.

(* same_shape and par_replace *)
Lemma same_shape_par_replace:forall (r:resource W)(Delta Gamma1
Gamma2:context A W)A1,
           par_replace (res r A1) Delta Gamma1 Gamma2->
	   forall (r1:rule_pattern),same_shape r1 Gamma1 ->
                                   same_shape r1 Gamma2.
 induction 1.
 auto.
 intros.
 inversion H.
 constructor 1.
 intros.
 inversion H1.
 constructor.
 constructor.
 eauto.
 eauto.
 intros.
 inversion H0; constructor.
 eauto.
Qed.


 Section struct_replace_def.
        
             Variables  (decI : eqdec I)
                        (decJ : eqdec J).
                       
             Variable   (Ru : structrule).
 (* application of the structural rule Ru to a context Delta
    gives Delta' 
 *)

 Inductive struct_replace (Delta Delta': context A W): 
   context A W -> context A W -> Set :=
   | struct_replaceRoot : 
        apply_rule Ru decI decJ Delta = Some Delta' -> 
          struct_replace Delta Delta' Delta Delta'
   | struct_replaceLeft :
       forall (Gamma1 Gamma2 Gamma3:context A W) (i:I),
         struct_replace Delta Delta' Gamma1 Gamma2 ->
         struct_replace  Delta Delta'  (Comma i Gamma1 Gamma3) 
                                (Comma i Gamma2 Gamma3)
   | rstruct_replaceRight :
       forall (Gamma1 Gamma2 Gamma3:context A W) (i:I),
         struct_replace Delta Delta' Gamma1 Gamma2 ->
         struct_replace  Delta Delta'  (Comma i Gamma3 Gamma1) 
                                (Comma i Gamma3 Gamma2)
   | struct_replaceDiamond :
       forall (Gamma1 Gamma2 :context A W) (j:J),
         struct_replace Delta Delta' Gamma1 Gamma2 ->
         struct_replace Delta Delta' (TDiamond j Gamma1) (TDiamond j Gamma2).


  Definition zfill_to_struct_replace_0 : 
   forall (ZGamma : zcontext A W)(Delta1 Delta2: context A W),
     apply_rule Ru decI decJ Delta1 = Some Delta2 -> 
   forall  (Gamma1 Gamma2:context A W),
     struct_replace Delta1 Delta2 Gamma1 Gamma2 ->
     struct_replace Delta1 Delta2 (zfill ZGamma Gamma1) (zfill ZGamma Gamma2).
  
  induction ZGamma.
  simpl;auto.
  simpl; intros.
  apply IHZGamma.
  auto.
  constructor 2.
  auto.
  simpl; intros.
  apply IHZGamma.
  auto.
  constructor 3.
  auto.
  simpl; intros.
  apply IHZGamma.
  auto.
  constructor 4.
  auto.
Defined.


Definition struct_replace_as_zfill : 
   forall (ZGamma : zcontext A W)(Delta Delta':context A W),
      apply_rule Ru decI decJ Delta = Some Delta' -> 
      struct_replace Delta Delta' (zfill ZGamma Delta) (zfill ZGamma Delta').

 intros.
 apply zfill_to_struct_replace_0.
 auto.
 constructor 1.
 auto.
Defined.

Definition struct_replace_to_zfill : 
   forall (Gamma Gamma' Delta Delta':context A W),
   struct_replace Delta Delta' Gamma Gamma' ->
   {ZGamma:zcontext A W |
     Gamma = zfill ZGamma Delta /\ Gamma' = zfill ZGamma Delta' /\
     apply_rule Ru decI decJ Delta = Some Delta'}.
 induction 1.
 exists (zroot A W);simpl; auto.
 case IHstruct_replace; intros ZG1 [e1 [e2 e3]].
 exists (zgraft ZG1 (zleft i (zroot _ _)  Gamma3)).
 rewrite zgraft_def.
 rewrite zgraft_def.
 simpl.
 rewrite e1;rewrite e2; auto.
 case IHstruct_replace; intros ZG1 [e1 [e2 e3]].
 exists (zgraft ZG1 (zright i Gamma3  (zroot _ _))).
 rewrite zgraft_def.
 rewrite zgraft_def.
 simpl.
 rewrite e1;rewrite e2; auto.
 case IHstruct_replace; intros ZG1 [e1 [e2 e3]].
 exists (zgraft ZG1 (zdown j  (zroot _ _))).
 rewrite zgraft_def.
 rewrite zgraft_def.
 simpl.
 rewrite e1;rewrite e2; auto.
Defined.

(*
Definition struct_replace_rep:forall (Delta1 Delta2 Gamma1 Gamma2 :context  A W),
                              apply_rule Ru decI decJ Delta1=Some Delta2 ->
                              replace Delta2 Delta1 Gamma2 Gamma1->
                              struct_replace Delta1 Delta2 Gamma1 Gamma2.
*)
End struct_replace_def.
End rep.
End Main.
End Definitions.

Section replace_props.
 Definition replace_to_par : forall I J A W 
                           (Delta Delta' Gamma Gamma': context I J A W),
                          replace Delta Delta' Gamma Gamma' ->
                          par_replace Delta Delta' Gamma Gamma'.
 induction 1.
 constructor 2.
 constructor 3;auto.
 constructor 1.
 constructor 3;auto.
 constructor 1.
 constructor 4;auto.
Defined.

Definition replaceProp:forall (I J A W  : Set)(T1 T2 T3 T4 T5:context I J A W),
                         replace T1 T2 T3 T4 ->
                         {T6:context I J A W & (replace T1 T5 T3 T6 *
                                               replace T5 T2 T6 T4)%type}.
 induction 1.
 exists T5.
 split.
 constructor 1.
 constructor.
 elim IHreplace.
 intros.
 exists (Comma i x Gamma3);split; constructor;tauto.
 elim IHreplace; intros.
 exists (Comma i Gamma3 x); split; constructor 3;tauto.
 elim IHreplace.
 intros.
 exists (TDiamond j x); split; constructor 4; tauto.
Defined.

Definition replaceParCom: forall (I J A W  : Set) 
                                 (A1:resource W)(f1: Form  I J A)
                                 (Delta Delta1 Delta2 Gamma:context I J A W)
                                 (i:I),
  par_replace (res A1 f1) Delta (Comma i Delta1 Delta2) Gamma ->
  {Delta1' :context I J A W  & 
     {Delta2' :context I J A W &
        {H1: par_replace (res A1 f1) Delta Delta1 Delta1' & 
           { H2 : par_replace (res A1 f1) Delta Delta2 Delta2' 
                   | Gamma =Comma i Delta1' Delta2'}}}}.

 intros.
 inversion H.
 exists Delta1.
 exists Delta2.
 exists (par_zero (res A1 f1) Delta Delta1).
 exists (par_zero (res A1 f1) Delta Delta2).
 auto.
 exists Gamma3.
 exists Gamma4.
 exists H4.
 exists H5.
 auto.
Defined.

Definition replaceParDiam:forall (I J A W  : Set) 
                                 (A1:resource W)
                                 (f1: Form  I J A)
                                 (Delta Delta1  Gamma:context I J A W)
                                 (j:J),
 par_replace (res A1 f1) Delta (TDiamond j Delta1) Gamma ->
  { Delta2 :context I J A W &
   { H :par_replace (res A1 f1) Delta Delta1 Delta2 |
         Gamma = TDiamond j Delta2}}.

 intros.
 inversion H.
 exists Delta1.
 exists (par_zero (res A1 f1) Delta Delta1).
 auto.
 exists Gamma2.
 exists H3.
 auto.
Defined.

Definition doubleReplacePar:
   forall (I J A W  : Set) (A1:resource W)(f1: Form  I J A)
          (Delta1 Delta2 Gamma1 Gamma2 Delta :context I J A W),
   replace Delta1 Delta2 Gamma1 Gamma2 ->
   forall (Gamma':context I J A W),
     par_replace (res A1 f1) Delta Gamma2 Gamma' ->
     {Delta2' :context I J A W &
      {Gamma1' :context I J A W & 
            (par_replace (res A1 f1) Delta Gamma1 Gamma1' *
              ((par_replace  (res A1 f1) Delta Delta2 Delta2') *
                 (replace Delta1 Delta2' Gamma1' Gamma'))%type)%type}}.


 induction 1; intros.
 exists Gamma'.
 exists Delta1.
 split.
 constructor.
 split.
 auto.
 constructor.
 elim (replaceParCom H0).
 intros Gamma4 H1; elim H1; clear H1; intros Delta2' H1; elim H1; clear H1;
 intros H1 H2.
 elim H2; clear H2; intros H2 H3.
 elim (IHreplace Gamma4 H1).
 intros Gamma5 H4.
 elim H4; clear H4; intros Gamma6 H4.
 exists Gamma5.
 exists (Comma i Gamma6 Delta2').
 split.
 constructor; tauto.
 split.
 tauto.
 rewrite H3; constructor; tauto.
 elim (replaceParCom H0).
 intros Gamma4 H1; elim H1; clear H1; intros Delta2' H1; elim H1; clear H1;
 intros H1 H2.
 elim H2; clear H2; intros H2 H3.
 elim (IHreplace Delta2' H2).
 intros Gamma5 H4.
 elim H4; clear H4; intros Gamma6 H4.
 exists Gamma5.
 exists (Comma i Gamma4 Gamma6).
 split.
 constructor; tauto.
 split.
 tauto.
 rewrite H3; constructor; tauto.
 elim (replaceParDiam H0).
 intros Gamma3 H1.
 elim H1; clear H1; intros H1 H2.
 elim (IHreplace Gamma3 H1).
 intros Gamma4 H3.
 elim H3; clear H3; intros Gamma5 H3.
 exists Gamma4.
 exists (TDiamond j Gamma5).
 split.
 constructor; tauto.
 split.
 tauto.
 rewrite H2; constructor; tauto.
Defined.


(* gives a sufficient condition to ensure cut rule :
   At present, it is defined abstractly in terms of 
   a property of substitution.
   Must be changed in further releases.
*)
Definition weak_sahlqvist_rule (I J :Set) (s:structrule I J) :=
 forall  (decI : eqdec I)(decJ : eqdec J) A W 
         (T1 T2 Delta T1': context I J A W)
         (A1:resource W)(f1: Form I J A), 
          apply_rule s decI decJ  T1 = Some T2 ->
          par_replace (res A1 f1) Delta T1 T1' ->
           {T2':context I J A W  &
            {H:par_replace (res A1 f1) Delta T2 T2'
             | apply_rule s decI decJ  T1' = Some T2'}}.



Definition weak_sahlqvist_ext (I J:Set)(R:extension I J):=
  forall (s:structrule I J) , 
    in_extension s R -> 
    weak_sahlqvist_rule  s.

Definition structrule_subst_commute:forall (I J A W:Set) (decI : eqdec I)
                  (decJ : eqdec J)(ru:structrule I J ),
      weak_sahlqvist_rule  ru ->
    forall (T1 T2 Gamma Gamma' Delta:context I J A W) 
       (A1:resource W)(f1: Form  I J A), 
    struct_replace  decI decJ ru T1 T2 Gamma Gamma'->
   forall (Gamma0':context I J A W), 
       (par_replace (res A1 f1) Delta Gamma Gamma0')->
          {T1':context I J A W & 
              {T2':context I J A W &
                {Gamma1 :context I J A W &
                    (((par_replace  (res A1 f1) Delta T1 T1') * 
                      (par_replace  (res A1 f1) Delta T2 T2'))%type *
                             ((par_replace  (res A1 f1) Delta Gamma' Gamma1)* 
                                               (struct_replace  decI decJ  ru 
                                                                T1'  T2' 
                                               Gamma0' Gamma1))%type)%type}}}.
  induction 2.
  intros.
  unfold weak_sahlqvist_rule in X.
  elim (X decI decJ A W T1 T2 Delta Gamma0' A1 f1 e H).
  intros Gamma1 H1.
  elim H1; clear H1; intros H1 H2.
  exists Gamma0'.
  exists Gamma1.
  exists Gamma1.
  split; split; auto.
  econstructor; eauto.
  intros.
  elim (replaceParCom H0).
  intros Gamma4 H2; elim H2; clear H2; intros Delta2' H2; elim H2; clear H2;
  intros H2 H3.
  elim H3; clear H3; intros H3 H4.
  elim (IHstruct_replace Gamma4 H2).
  intros Gamma5 H5; elim H5; clear H5; intros T2' H5.
  elim H5; clear H5; intros Gamma6 H5.
  exists Gamma5.
  exists T2'.
  exists (Comma i Gamma6 Delta2').
  split; split.
  tauto.
  tauto.
  constructor; tauto.
  rewrite H4; constructor; tauto.
  intros.
  elim (replaceParCom H0).
  intros Gamma4 H2; elim H2; clear H2; intros Delta2' H2; elim H2; clear H2;
  intros H2 H3; elim H3; clear H3; intros H3 H4.
  elim (IHstruct_replace Delta2' H3).
  intros Gamma5 H5; elim H5; clear H5; intros T2' H5.
  elim H5; clear H5; intros Gamma6 H5.
  exists Gamma5.
  exists T2'.
  exists (Comma i Gamma4 Gamma6).
  split; split.
  tauto.
  tauto.
  constructor; tauto.
  rewrite H4; constructor; tauto.
  intros.
  elim (replaceParDiam H0).
  intros Gamma3 H2.
  elim H2; clear H2; intros H2 H3.
  elim (IHstruct_replace Gamma3 H2).
  intros Gamma4 H4; elim H4; clear H4; 
  intros T2' H4; elim H4; clear H4;
  intros Gamma5 H4.
  exists Gamma4.
  exists T2'.
  exists (TDiamond  j Gamma5).
  split; split.
  tauto.
  tauto.
  constructor; tauto.
  rewrite H3; constructor; tauto.
Defined.

End replace_props.

Arguments hyp [W]. 
Arguments pvar [I J].
Arguments pcomma [I J].
Arguments pdiam [I J].
Arguments NL [I J].
Arguments res [I].
Arguments res [I J A W].
Arguments At [I J A].

Hint Resolve zgraft_def no_holes zfill_fill_0 zfill_fill strip_match match_strip 
zfill_to_replace struct_replace_as_zfill:ctl_db. 
Hint Resolve subCont_length isIncluded_to_isIncl allDistinct_to_distinct.

Notation "r1 'U' r2":=(add_rule r1 r2)(at level 30). 
