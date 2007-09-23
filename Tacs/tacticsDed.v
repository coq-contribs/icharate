(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                          Pierre CASTERAN                             *)
(*                            2003 -2004                                *)
(*                              LaBRI                                   *)
(************************************************************************)

Set Implicit Arguments.
Require Export listAux.
Require Export natDedGram.
Require Export semLex.


(* tactic that solves a goal of the form (in_extension e1 e2) *)
Ltac inExt :=
match goal with
| |- in_extension ?e ?ex=>
 try unfold ex;repeat constructor
end.

(*tactic that eliminates all hypothesis whose type is of the form
 {_|_}or {_&_} *)


Ltac elimSig:=
match goal with 
H:(sig _)|- _ => elim H; clear H; intros;elimSig
|H:(sigS _)|-_ =>elim H; clear H; intros;elimSig
| _=>idtac
end.
(* to build the decidability of equality algorithm within enumerative sets *)
Ltac solve_eqdec:=
unfold eqdec; decide equality.

(* inductive type that contains three constant constructor :
 rP: to go in the right subtree
 lP: to go in the left subtree
 dP: to go within the diamond node <>j *)
Inductive path : Set :=
  | rP : path
  | lP : path
  | dP : path.


Ltac here :=
   match goal with
   |   |- (struct_replace  (A:=?A) (I:=?I) (J:=?J)(W:=?W) ?e ?eI ?eJ 
           ?Delta ?Delta' ?Gamma ?Gamma')  => econstructor 1
 |   |- (replace  (A:=?A) (I:=?I) (J:=?J)(W:=?W)  
          ?Delta ?Delta' ?Gamma ?Gamma')  => econstructor 1
end.
(* replace in the left subtree *)
Ltac down_l :=
   match goal with
   |  [ |- (struct_replace  (A:=?A) (I:=?I) (J:=?J)(W:=?W) ?eI ?eJ ?r
           ?Delta ?Delta' ?Gamma ?Gamma') ] => econstructor 2
 |  [ |- (replace  (A:=?A) (I:=?I) (J:=?J)(W:=?W)  
           ?Delta ?Delta' ?Gamma ?Gamma') ] => econstructor 2
end.

(* replace in the right subtree *)
Ltac down_r :=
   match goal with
   |  [ |- (struct_replace  (A:=?A) (I:=?I) (J:=?J)(W:=?W)  ?eI ?eJ ?r
           ?Delta ?Delta' ?Gamma ?Gamma') ] => econstructor 3
 |  [ |- (replace  (A:=?A) (I:=?I) (J:=?J)(W:=?W)  
           ?Delta ?Delta' ?Gamma ?Gamma') ] => econstructor 3
end.
(* go inside the structural <> *)
Ltac down_diam :=
   match goal with
   |  [ |- (struct_replace  (A:=?A) (I:=?I) (J:=?J)(W:=?W)  ?eI ?eJ ?e
           ?Delta ?Delta' ?Gamma ?Gamma') ] => econstructor 4
 |  [ |- (replace  (A:=?A) (I:=?I) (J:=?J)(W:=?W)  
           ?Delta ?Delta' ?Gamma ?Gamma') ] => econstructor 4
end.

Implicit Arguments zroot [I J A W].
Ltac unfocus :=
   match goal with 
    | |- (natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R
                     (zfill ?zgamma  ?Gamma) ?F) =>
        let Gamma' := eval simpl in (zfill zgamma  Gamma)
            in change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     Gamma' F)
    | |- ?anygoal => idtac
  end.

Ltac z_root :=
    match goal with
    | |- (natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R
                     (zfill ?zgamma  ?Gamma) ?F) =>
        let Gamma' := eval simpl in (zfill zgamma  Gamma)
            in change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill zroot Gamma') F)
   | |- natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  ?Gamma ?F  =>
        change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill zroot  Gamma) F)
   end.

(* move the focus to the left *)
Ltac z_left :=
  match goal with
   | |- natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                (zfill ?z (Comma ?i ?G1 ?G2)) ?F  =>
      change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill (zleft i z G2) G1) F)
   | |-  natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                   (Comma ?i ?G1 ?G2) ?F =>
     change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill (zleft i zroot G2) G1) F)
   | _ => fail
              
end.

(* move the focus to the right son *)
Ltac z_right :=
  match goal with
   | |- natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                (zfill ?z (Comma ?i ?G1 ?G2)) ?F  =>
      change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill (zright i G1 z) G2) F)
  | |- natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                (Comma ?i ?G1 ?G2) ?F  =>
      change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill (zright i G1 zroot) G2) F)
  | _ => fail
end.

(* go inside the unary <> *)
Ltac z_down:=  match goal with
   | |- natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                (zfill ?z (TDiamond ?j ?G1)) ?F  =>
        change (natded  (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                (zfill (zdown j z) G1) F)
  | |- natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                (TDiamond ?j ?G1) ?F =>
       change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                (zfill (zdown j zroot) G1) F)
 | _ =>fail

end.


(* p: path *)
Ltac zpath0 p:=match eval compute in p with
|nil =>idtac
|cons ?p1 ?pl =>match eval compute in p1 with
         |lP=>z_left;(zpath0 pl)
         |rP=>z_right;(zpath0 pl)
         |dP=>z_down;(zpath0 pl)
      end
end.

(* focus the subterm found if we follow the path p
  we first initialize the focus which should point
  the root of the context *) 
Ltac zpath p:=z_root;zpath0 p.

Ltac axiom := 
  match goal with 
        |  H : matches (form (I:=?I)(J:=?J) (A:=?A) ?F) ?Gamma |- 
         natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) _ _ _ ?Gamma _ => 
         let x0:= fresh in let e0 := fresh in
     (elim (matches_inv_form H);intros x0 e0;rewrite e0;apply Wd)
   | |- natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) _ _ _ _ _ =>  try apply Wd
 end.

Ltac axiom_auto:=axiom ||auto.
(* works only if Gamma is a variable *)
Ltac Gamma_rw H :=
  match goal with
  |  H : matches (form (I:=?I)(J:=?J) (A:=?A) ?F) ?Gamma |- ?any
     =>(elim (matches_inv_form H);intros x0 e0;rewrite e0)
  |  H : matches (bComma (I:=?I)(J:=?J) (A:=?A) ?i ?B1 ?B2) ?Gamma |- ?any
     =>let x := fresh in 
        let p := fresh in 
         let x0 := fresh in 
        let p0 := fresh in  
            let H1 := fresh in 
        let H2 := fresh in 
             let H3 := fresh in 
        let H4 := fresh in 
         (elim (matches_inv_Comma H);intros x p; elim p; intros x0 p0; elim
             p0; intros H1 H2; elim H2; intros H3 H4; try (rewrite H1))
 (* add diamond case *)
   end.
     
(* tactics for top-down proofs *)
Ltac slashI nhyp :=
  unfocus; match goal with 
    |  |- natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) _ _ _ _ (Slash ?i ?F ?G)  =>
      apply SlashI with (n:=nhyp)
             end.

Ltac slashI0:=slashI 0.
Ltac backI nhyp :=
  unfocus; match goal with 
    |  |- natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) _ _ _ _ (Backslash ?i ?F ?G)  =>
      apply BackI with (n:=nhyp)
             end.

Ltac dotI :=
   unfocus; eapply DotI.

Ltac dotE n' p' :=
  match goal with
   | |- natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) _ _ _ (zfill ?z ?gamma) ?F =>
        eapply DotE' with (n:=n')(p:=p');[try axiom |simpl]
   | |- ?other => eapply DotE with (n:=n')(p:=p')
  end.

Ltac dotE0 :=dotE 0 0.   
Ltac eslashE := unfocus; eapply SlashE.

Ltac slashE G1 := unfocus; apply SlashE with (G:=G1).

Ltac ebackE := unfocus; eapply BackE.

Ltac backE G1 := unfocus; apply BackE with (G:=G1).

Ltac boxI := unfocus; apply BoxI.

Ltac boxE := unfocus; apply BoxE.

Ltac diamI := unfocus; apply DiamI.

Ltac nthExt n:=
match goal with | |-(in_extension _ ?ext0)=>
match eval compute in n with
 |0 =>try unfold ext0;eapply in_extension_rule
 |_=>try unfold ext0;eapply in_extension_right;nthExt (pred n)
end
end.

Ltac struct n:=eapply Structrule';[nthExt n|autorewrite with ctl_db;auto|simpl].
Ltac structH H:=eapply Structrule';[eexact H|autorewrite with
ctl_db;eauto|simpl].

(* simplified datatype, that will be used by users to input datas
 such as the structure of the sentence to be analysed *)
Inductive contextW (I J W:Set):Set:=
|oneW:W -> contextW I J W
|comW:I->contextW I J W ->contextW I J W->contextW I J W
|diamW:J ->contextW I J W->contextW I J W.


(* to calculate the number of leaves(words) 
 of a structured sentence*)
Fixpoint lengthW(I J W:Set)(cw:contextW I J W){struct cw}:nat :=
match cw with 
|oneW w=> 1
|comW _ t1 t2=> lengthW t1 + lengthW t2
|diamW _ t1 => lengthW t1
end.



(* construction of a context using a structured sentence
 and a list of numbers *)

Fixpoint getContext1 (I J W A:Set)(cw:contextW I J W)(l:list nat)(i:nat)
(lex:W->list (Form I J A)){struct cw}:
(option (context I J A W)):=
match cw with 
| oneW w1=>match l with 
          |a::nil => match (nth_error (lex w1) a) with
                    |Some f =>Some (res (word i w1) f)
                    | None => None
                   end
          |others => None
         end
| comW i0 t1 t2 =>match (getSubLists l (lengthW t1)) with 
                 |Some (l1, l2) => match (getContext1 t1 l1 i lex) with
                        |Some co1 => match (getContext1 t2 l2 (i+ (lengthW t1))lex) with 
                                    |Some co2 => Some (Comma i0 co1 co2)
                                    |None => None
                                               end
                                   |None => None
                       end  
                |None => None 
               end
| diamW j t1 => match (getContext1 t1 l i lex) with 
                  |Some co1 => Some (TDiamond j co1)
                  |None => None
           end
end.

Fixpoint getContext (I J W A:Set)(cw:contextW I J W)(l:list nat)(i:nat)
(lex:W->list (Form I J A)){struct cw}:
nat*(option (context I J A W)):=
match cw with 
| oneW w1=>match (nth_error l i)with 
          |Some a => match (nth_error (lex w1) a) with
                    |Some f =>(i,Some (res (word a w1) f))
                    | None =>(i, None)
                   end
          |others => (i,None)
         end
| comW i0 t1 t2 =>match (getContext t1 l i lex) with
                        |(j, Some co1) => match (getContext t2 l (S
			j) lex) with 
                                    |(k,Some co2) => (k, Some (Comma i0 co1 co2))
                                    |(i0,None) => (i0,None)
                                               end
                                   
                |(k,None) => (k,None) 
               end
| diamW j t1 => match (getContext t1 l i lex) with 
                  |(m,Some co1) =>(m, Some (TDiamond j co1))
                  |(m,None) =>(m, None)
           end
end.

Ltac fits :=
match goal with
| |-(fitsContSent ?lex  ?ct ?sent) => 
unfold fitsContSent;simpl;try tauto
| _ => idtac
end.


Ltac setCont cw ln:=
match goal with 
| |-(reduceTo ?eqdecI ?eqdecJ ?lex ?ext ?sent ?f)=>
 match eval compute in
(getContext  cw ln 0 lex) with
  |(_,(Some ?gamma))=>apply reduce1 with gamma;
 [simpl|fits]
  |_ => fail
  end
| |-(deriveTo _ _ _)=> unfold deriveTo;simpl;setCont cw ln
| |-(deriveToSyn _ _ _)=>unfold deriveToSyn;simpl;setCont cw ln
| _=>idtac
end.


Fixpoint constructList(n:nat):list nat:=
match n with
| 0=> nil
|(S k)=>0::(constructList k)
end.
				   
Ltac setCont0 cw:=setCont cw (constructList (lengthW cw)).
(* other tactics  *)


(* resolve a goal which has a form (replace T1 T2 T3 T4) given the path 'p'
where the replacement is done *)
 Ltac pathRep p:=
  match eval compute in p with
  | nil  => apply replaceRoot
  | (cons ?X1 ?X2) => match eval compute in X1 with 
                           |lP => apply replaceLeft; pathRep X2
                           |rP => apply replaceRight; pathRep X2
                           |dP=> apply replaceDiamond; pathRep X2
                             end
   end.                    

(* this function looks for the first leaf whose form is <>j A
and returns the corresponding path if this leaf exists *)
Fixpoint getFirstPathDiam (I J A W:Set)(T:context I J A W)
{struct T}:option (list path):=
match T with 
| res _ F =>match F with 
                       |Diamond j B => Some (nil(A:=path))
                       | _ =>  None 
                       end
| Comma i T1 T2 =>match T1 with 
                     |res _ (Diamond _ _) => Some (lP::nil)
                     | _=> match T2 with 
                         | res _ (Diamond _ _) => Some (rP::nil) 
                         | _=> match (getFirstPathDiam T1) with 
                               | None => match (getFirstPathDiam T2) with 
                                         | None => None
                                         | Some p1 => Some (rP::p1)
                                         end
                               |Some p1 => Some (lP::p1)
                               end
                           end
                       end
|TDiamond j T1 =>  match (getFirstPathDiam T1) with 
                     |None => None
                     | Some p1 => Some (dP::p1)
                     end
end.

(* eliminates the first leaf of the form <>j A *)
Ltac elimDiam n:=
match goal with 
| |- (natded _ _ _ ?X11 _)  =>
  match eval compute in (getFirstPathDiam X11) with
 |(None _) =>idtac
 | (Some ?p1)=> eapply DiamE with (n:=n); [pathRep p1 | constructor 1 |idtac]
 end
| |- _ => idtac
end.


(* here some tactics for bottom-up proofs specially
used for analysing sentences in a given grammar *)


(* adds axioms to the context : here lex has the type 
W-> list (Form I J A) *)
Ltac addAxAux eqdecI eqdecJ ext lex i lw ln :=
match eval compute in (head lw) with
|Some ?m1 => match eval compute in (head ln) with
 |Some ?n1=> match eval compute in (nth_error (lex m1) n1) with
 |Some ?f=>
cut (natded eqdecI eqdecJ ext (res (word i m1) f) f);
[let ax:=fresh "Ax" in (intro ax;simpl in ax)|constructor 1]; 
addAxAux eqdecI eqdecJ ext lex (S i) (tail lw) (tail ln)
| _=> idtac
end
|_=>idtac
end
|_ => idtac
end.

(* final tactic that uses the above one *)
Ltac addAxioms_anc ln:=match goal with
| |-(deriveToSyn ?gr ?lw ?f)=>
  (addAxAux ((gr.(lexic_syn)).(eqdecI_syn)) ((gr.(lexic_syn)).(eqdecJ_syn)) 
   (gr.(ext_syn)) ((gr.(lexic_syn)).(lex_syn)) O lw ln)
| _ => idtac
end.

Ltac addAxioms0_anc :=match goal with
|-(deriveToSyn ?gr ?lw ?f)=>addAxioms_anc (constructList (length lw))
| _ =>idtac
end.


(* other version *)
(* adds axioms to the context : here lex has the type 
W-> list (Form I J A) *)
Ltac addAxAuxi eqdecI eqdecJ ext lex lw ln :=
match eval compute in (head lw) with
|Some ?m1 => match eval compute in (head ln) with
 |Some ?n1=> match eval compute in (nth_error (lex m1) n1) with
 |Some ?f=>
cut (natded eqdecI eqdecJ ext (res (word n1 m1) f) f);
[let ax:=fresh "Ax" in (intro ax;simpl in ax)|constructor 1]; 
addAxAuxi eqdecI eqdecJ ext lex (tail lw) (tail ln)
| _=> idtac
end
|_=>idtac
end
|_ => idtac
end.


(* final tactic that uses the above one *)
Ltac addAxioms ln:=match goal with
| |- (reduceTo ?eqdecI ?eqdecJ ?lex ?ext ?lw ?f)=>
 addAxAuxi eqdecI eqdecJ ext lex lw ln 
| |-(deriveTo _ _ _)=> unfold deriveTo;simpl;addAxioms ln
| |-(deriveToSyn _ _ _)=>unfold deriveToSyn;simpl;addAxioms ln
| _ => idtac
end.

Ltac addAxioms0 :=match goal with
| |-(reduceTo ?eqdecI ?eqdecJ ?lex ?ext ?lw ?f)=>
   addAxioms (constructList (length lw))
| |-(deriveTo _ _ _)=> unfold deriveTo;simpl;addAxioms0
| |-(deriveToSyn _ _ _)=>unfold deriveToSyn;simpl;addAxioms0
|_=>idtac
   
end.

(* elimination tactics*)
(* H1 has the type _|--A/B and H2 the type _|--B *)
(*Ltac elimS1 H1 H2:=
match goal with
| |- (reduceTo ?eqdecI ?eqdecJ ?lex ?ext ?lw ?f) =>
(let typ:= type of H1 in
(let typ0:= type of H2 in 
(match typ with (natded ?eqdecI ?eqdecJ ?ext ?G1 (Slash ?i ?A ?B))=>
match typ0 with (natded ?eqdecI ?eqdecJ ?ext ?G2 ?C)=>
match eval compute in 
 (eqDecF eqdecI eqdecJ ((gr.(lexic_s) B C) with
   |left _ _=>  (* B=C *)
 assert (natded eqdecI eqdecJ ext (Comma i G1 G2) A);
 [eapply SlashE;eauto |idtac];clear H1; clear H2
   |right _ _=>fail "you can't apply this tactic!"
 end end end))) 
|_ =>idtac
end.
*)

Ltac elimS H1 H2:=
match goal with
| |- (reduceTo ?eqdecI ?eqdecJ ?lex ?ext ?lw ?f)=>
(let typ:= type of H1 in
(let typ0:= type of H2 in 
(match typ with (natded ?eqdecI ?eqdecJ ?ext ?G1 (Slash ?i ?A ?B))=>
match typ0 with (natded ?eqdecI ?eqdecJ ?ext ?G2 ?C)=>
 assert (natded eqdecI eqdecJ ext (Comma i G1 G2) A);
 [(eapply SlashE;[eexact H1|(eexact H2 ||fail)]) |idtac];clear H1; clear H2
 end end)))
|_ =>idtac
end.


Ltac elimB H1 H2:=
match goal with
| |- (reduceTo ?eqdecI ?eqdecJ ?lex ?ext ?lw ?f)=>
(let typ:= type of H1 in
(let typ0:= type of H2 in 
(match typ with (natded ?eqdecI ?eqdecJ ?ext ?G1 (Backslash ?i ?A ?B))=>
match typ0 with (natded ?eqdecI ?eqdecJ ?ext ?G2 ?C)=>
 assert (natded eqdecI eqdecJ ext (Comma i G2 G1) B); 
[(eapply BackE;[eexact H2 |(eexact H1 ||fail)])|idtac];clear H1; clear H2
 end end)))
| _ => idtac
end.
 

Ltac elimBox H:=let typ:=type of H in
(match typ with  (natded ?eqdecI ?eqdecJ ?ext ?G1 (Box ?j ?C))=>
 cut (natded eqdecI eqdecJ ext (TDiamond j G1) C);[intro |apply BoxE;auto];clear H
|_ => fail
end).

(* to be continued*)
(*elimination of dot*)

(*elimination of diamond*)
Ltac elimD H1 H2:=
match goal with
| |- (reduceTo ?eqdecI ?eqdecJ ?lex ?ext ?lw ?f) =>
let typ1 := type of H1 in
(let typ2:=type of H2 in
(match typ1 with 
|natded ?eqdecI ?eqdecJ ?ext (zfill ?Gamma (TDiamond ?j (res ?r ?F))) ?G=>
match typ2 with 
|natded  ?eqdecI ?eqdecJ ?ext ?Delta (Diamond ?i ?F')=>
cut (natded eqdecI eqdecJ ext (zfill Gamma Delta)
G);[clear H1;clear H2;simpl;intro H1|(eapply DiamondE';[eexact H2|(eexact
H1 ||fail)])]
|_=>fail
end
|_=>fail
end))
|_ =>fail
end.

(* using zippers for hypothesis in the context *)
Ltac z_rootH H:=let typ := type of H in
(match typ with
    |(natded  (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R
                     (zfill ?zgamma  ?Gamma) ?F) =>
        let Gamma' := eval simpl in (zfill zgamma  Gamma)
            in (change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill zroot Gamma') F) in H)
   | (natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  ?Gamma ?F)  =>
        change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill zroot  Gamma) F)in H

   end).

(* move the focus to the left *)
Ltac z_leftH H := let typ := type of H in
(match typ with
   | natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                (zfill ?z (Comma ?i ?G1 ?G2)) ?F  =>
      change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill (zleft i z G2) G1) F) in H
   | natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                   (Comma ?i ?G1 ?G2) ?F =>
     change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill (zleft i zroot G2) G1) F) in H
   | _ => fail
              
end).

(* move the focus to the right son *)
Ltac z_rightH H :=
 let typ := type of H in
(match typ with
   |  natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                (zfill ?z (Comma ?i ?G1 ?G2)) ?F  =>
      change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill (zright i G1 z) G2) F) in H
   | natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                (Comma ?i ?G1 ?G2) ?F  =>
      change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                     (zfill (zright i G1 zroot) G2) F) in H
  | _ => fail
end).

(* go inside the unary <> *)
Ltac z_downH H:=  
let typ := type of H in
(match typ with
   | natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                (zfill ?z (TDiamond ?j ?G1)) ?F  =>
        change (natded  (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                (zfill (zdown j z) G1) F) in H
  |  natded (I:=?I)(J:=?J) (A:=?A)(W:=?W) ?dI ?dJ ?R  
                (TDiamond ?j ?G1) ?F =>
       change (natded (I:=I)(J:=J) (A:=A)(W:=W) dI dJ R
                (zfill (zdown j zroot) G1) F)in H
 | _ =>fail

end).
(* p: path *)

Ltac zpathH0 H p:=match eval compute in p with
|nil =>idtac
|cons ?p1 ?pl =>match eval compute in p1 with
         |lP=>z_leftH H;(zpathH0 H pl)
         |rP=>z_rightH H;(zpathH0 H pl)
         |dP=>z_downH H;(zpathH0 H pl)
      end
end.

Ltac zpathH H p:=z_rootH H;zpathH0 H p.

Ltac endDeriv:=
match goal with
|H : natded _ _ _ _ ?g |- reduceTo ?eqdecI ?eqdecJ ?lex ?ext ?lw ?f =>
   econstructor;[eauto|fits]
| _ =>idtac
end.

(* adds the axiom based on a hypothetical resource to the context *)
Ltac addHyp n f:=
match goal with
| |-(reduceTo  (W:=?W) ?eqdecI ?eqdecJ  _ ?ext _ _ )=>
 cut (natded eqdecI eqdecJ ext  (res (hyp (W:= W) n) f) f) ;
  [let hyp:= fresh "Hyp" in (intro hyp; simpl in hyp) | axiom]
| |-(natded ?eqdecI  ?eqdecJ ?ext _ _)=>
 cut (natded (I:=I)(J:=J)(A:=A) (W:=W) eqdecI eqdecJ ext (res (hyp (W:=W) n) f) f) ; 
  [let hyp:=fresh "Hyp" in (intro hyp; simpl in hyp) | axiom]
| _ =>idtac
end.

Definition getHypForm (I J A W:Set)(Gamma:context I J A W):option (Form I J A):=
match Gamma with
|(res (hyp _) f) => Some f
|other=>None
end.

(* H has the type (Gamma ,i (hyp k))|-C , the tactic here
 discharges the hypothesis k and introduces the / in the conclusion
 formula *)
Ltac introS H :=
let ty:=type of H in
(match ty with
| (natded (I:=?I)(J:=?J)(A:=?A) (W:=?W) ?eqdecI ?eqdecJ ?ext (Comma ?i ?G2 (res (hyp (W:=?W) ?k) ?g)) ?f)=>
(* match eval simpl in (getHypForm G1) with
 |None => fail
 |Some ?g =>*)
  let nv:= fresh in (
 cut (natded eqdecI eqdecJ ext G2 (Slash i f g)) ;
[intro nv;simpl in nv;clear H|eapply SlashI;eexact H])
| (natded ?eqdecI ?eqdecJ ?ext (zfill ?z ?G) ?f)=>simpl in H; introS H
|_ =>fail
end).

(* introduction of <> *)
Ltac introD j H:=
let ty:=type of H in
(match ty with
| (natded (I:=?I)(J:=?J)(A:=?A) (W:=?W) ?eqdecI ?eqdecJ ?ext ?Gamma
?F)=>
cut (natded eqdecI eqdecJ ext (TDiamond j Gamma) (Diamond j F));[clear
H;intro H|apply DiamI;exact H]
|_=>fail
end).

(* some functions that manipulate paths *)

(* returns the sub-context of a context T which 
  results if we follow the path p *)
Fixpoint getTermByPath(I J A W:Set) (T:context I J A W) (p:list path) {struct p} :
 option (context I J A W):=
  match T, p with
  | T, nil => Some T
  | (res _ _ ), cons _ _ => None 
  | Comma i T1 T2, cons p1 p2 =>
      match p1 with
      | lP => getTermByPath T1 p2
      | rP => getTermByPath T2 p2
      | dP => None 
      end
  | TDiamond i T, cons p1 p2 =>
      match p1 with
      | dP => getTermByPath T p2
      | other => None 
      end
  end.

(* replace a sub-term of a context by another one *)
Fixpoint replaceTermByTerm (I J A W:Set)(T1 T2:context I J A W) (p:list path) {struct p} :
 option (context I J A W ):=
  match T1, p with
  | _, nil => Some T2
  | res _ _, cons _ _ => None 
  | Comma i T'1 T'2, cons p1 p2 =>
      match p1 with
      | lP =>
          match replaceTermByTerm T'1 T2 p2 with
          | None => None 
          | Some t' => Some (Comma i t' T'2)
          end
      | rP =>
          match replaceTermByTerm T'2 T2 p2 with
          | None => None 
          | Some t' => Some (Comma i T'1 t')
          end
      | dP => None 
      end
  | TDiamond i T, cons p1 p2 =>
      match p1 with
      | dP =>
          match replaceTermByTerm T T2 p2 with
          | None => None 
          | Some t' => Some (TDiamond i t')
          end
      | other => None 
      end
  end.

Fixpoint getIthRule (I J :Set)(ext:extension I J)(i:nat){struct ext}:
(option (structrule I J)):=
match ext, i with
|NL, _ =>None
|(add_rule r ext1) , 0 =>Some r
|(add_rule r ext1) , (S k)=>getIthRule ext1 k
end.

(* i the number of the structural rule that will be applied
   p:path
   H hypothesis of the kind Gamma |- C where we will apply our structural rule to 
  the context Gamma *)

(* apply a linear structural rule in a bottom up proof *)
Ltac structL_asc i H:=
let typ:=type of H in (
match typ with
| (natded (I:=?I) (J:=?J) (A:=?A)(W:=?W) ?eqdecI ?eqdecJ  ?ext
 (zfill ?z ?Delta1) ?C) =>
match eval compute in (getIthRule ext i) with  
|None => idtac
|Some (?ru1,?ru2) =>
match eval compute in (apply_rule (ru2,ru1) eqdecI eqdecJ Delta1) with
|Some ?Delta2=>cut (natded eqdecI eqdecJ ext (zfill z
Delta2) C);[simpl;clear H;intro H|(apply XStructrule' with Delta1 (ru1, ru2);[autorewrite with
ctl_db;auto|inExt|exact H])]
|None=>idtac
end
end
|_=>fail
end).


Ltac structRule i H lemInv:=
let typ:=type of H in (
match typ with
| (natded (I:=?I) (J:=?J) (A:=?A)(W:=?W) ?eqdecI ?eqdecJ  ?ext (zfill ?z ?Delta1) ?C) =>
match eval simpl in (getIthRule ext i) with  (* Rq: eval compute here doesn't work !*)
|None => idtac
|Some ?ru =>
let hy:=fresh in(
   let delta:=fresh "Delta" in 
    (let nd:=fresh in (
      let app:=fresh in (
      let ex:=fresh "E" in (
cut (in_extension ru ext);[intro ex|inExt];
 cut ({Delta2:context I J A W|
      (apply_rule ru eqdecI eqdecJ Delta2)=Some Delta1});
  [intro hy; elim hy; clear hy; intros delta app
 |econstructor;autorewrite with ctl_db;auto]; 
 cut (natded eqdecI eqdecJ ext (zfill z delta) C);
[intro nd;simpl in nd;
rewrite lemInv with (1:=app) in nd;
 clear ex; clear app ;clear delta;clear H (* we should clear app before delta *)
|eapply XStructrule';eauto])))))
 end
| _ =>idtac
end ).


Ltac structRuleP i H p lem:=zpathH H p;structRule i H lem.


(* modifying slightly apply-rule in order to hold non linear rules*)

Fixpoint access_tac (I J A W:Set)(eqdecI :eqdec I)(eqdecJ :eqdec
J)(eqdecA:eqdec A)
(rp:rule_pattern I J)(j:nat){struct rp}:(context I J A W)->(option
(context I J A W))*bool:=
match rp with 
|pvar i =>match (eq_nat_dec i j) with
          |right _ =>fun Gamma:(context I J A W) =>(None, true)
          |left _ =>fun Gamma:(context I J A W) =>((Some Gamma),true)
          end
|pcomma i rp1 rp2=>(fun Gamma:context I J A W=> 
            match Gamma with
          |Comma l Gamma1 Gamma2 =>match (eqdecI l i) with
                |right _ =>(None,false)
                |left _ =>match (access_tac eqdecI eqdecJ eqdecA rp1 j Gamma1) with
                      |(_, false)=> (None,false)
                      |(None,true) =>(access_tac eqdecI eqdecJ eqdecA rp2 j Gamma2) 
                      |((Some (res (hyp h') ty')),true)=>
                          match (access_tac eqdecI eqdecJ eqdecA rp2 j Gamma2) with
                       | (_,false)=>(None,false)
                       |((Some (res (hyp h) ty)), true )=>
                           match (eq_nat_dec h h') with 
                        |left _ =>
                     match (eqDecF eqdecI eqdecJ eqdecA ty ty') with 
                     |left _=>((Some (res (hyp h) ty)),true)
                     |right _ =>(None,false)
                      end
                     |right _ =>(None, false)
                       end
                     |(None,true) =>((Some (res (hyp h') ty')),true)
                     |other=>(None, false)
                                    end
                        |((Some Delta),true)=> 
                            match  (access_tac eqdecI eqdecJ eqdecA rp2 j Gamma2) with
                              |(None,true)=>((Some Delta),true)
                              |other=>(None,false)
                               end end end
                 |other=>(None,false)
                 end)
|pdiam i rp1 =>(fun Gamma:context I J A W=> 
                 match Gamma with
                   |TDiamond l Gamma1 =>
                 match (eqdecJ i l) with 
                   |right _ => (None,false)
                   |left _ =>(access_tac eqdecI eqdecJ eqdecA rp1 j Gamma1)
                     end
                   |other => (None,false)
                     end)
end.


Fixpoint compile_tac (I J A W:Set)(eqdecI :eqdec I)(eqdecJ:eqdec
J)(eqdecA:eqdec A)
(rp1 rp2:rule_pattern I J){struct rp2}:(context I J A W) -> (option
(context I J A W)):=
match rp2 with
|pvar i => fun Gamma:(context I J A W)=> match (access_tac eqdecI
eqdecJ eqdecA rp1 i Gamma) with 
           |((Some Gamma') ,_ )=> Some Gamma'
           |other =>None
         end
|pcomma i r1 r2=>fun Gamma:(context I J A W) => 
   match (compile_tac eqdecI eqdecJ eqdecA rp1 r1 Gamma) with
          |None =>None
          |Some Delta1 => match (compile_tac eqdecI eqdecJ eqdecA rp1 r2 Gamma) with
                    |None =>None
                    |Some Delta2 =>Some (Comma i Delta1 Delta2)
                      end
                      end
|pdiam i r1=>fun Gamma:(context I J A W) =>
match (compile_tac eqdecI eqdecJ eqdecA rp1 r1 Gamma) with
                    |None =>None
                    |Some Delta1 =>Some (TDiamond i Delta1)
                      end
end.

 Definition apply_rule_tac(I J A W:Set) (st:structrule I J)(eqdecI: eqdec I)(eqdecJ : eqdec
       J)(eqdecA :eqdec A): context I J A W -> option (context I J A W):=
match st with
| (r1,r2)=>compile_tac  eqdecI eqdecJ eqdecA r1 r2
end.

(* if all the leaves are constants*)
Ltac struct_auxi i H eqdecA:=
let typ:=type of H in (
match typ with
| (natded (I:=?I) (J:=?J) (A:=?A)(W:=?W) ?eqdecI ?eqdecJ  ?ext
 (zfill ?z ?Delta1) ?C) =>
match eval compute in (getIthRule ext i) with  
|None => idtac
|Some (?ru1,?ru2) =>
match eval compute in (apply_rule_tac (ru2,ru1) eqdecI eqdecJ eqdecA Delta1) with
|Some ?Delta2=>cut (natded eqdecI eqdecJ ext (zfill z
Delta2) C);[simpl;clear H;intro H|(eapply XStructrule';[autorewrite with
ctl_db;auto|inExt|eexact H])]
|None=>idtac
end
end
|_=>fail
end).

Ltac struct_asc i H:=
match goal with 
|-deriveToSyn ?gram ?sent ?f => struct_auxi i H ((gram.(lex)).(eqdecA))
|_=>idtac
end.

Ltac convert_syn:=match goal with 
| |-deriveTo _ _ _=> unfold deriveTo; simpl
end.
