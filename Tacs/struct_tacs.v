(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                              LaBRI                                   *)
(************************************************************************)


Require Export Eqdep_dec.
Require Export apply_rule_props.
Set Implicit Arguments.
Unset Standard Proposition Elimination Names.


Lemma proof_irrelevanceA:forall(A:Set)(eqdecA:eqdec A)
                          (a :A)(p1:a=a), p1=refl_equal a.
 intros.
 apply eq_proofs_unicity.
 intros; case (eqdecA x y); tauto.
Qed.

Lemma eqdecX_rw:forall (X:Set)(decX:eqdec X)(i:X), 
decX i i=left (i<>i) (refl_equal i).
 intros.
 case (decX i i).
 intros.
 rewrite (proof_irrelevanceA decX e).
 auto.
 intro n; case n.
 auto.
Qed.

Hint Rewrite eqdecX_rw:rw.


(* tactic for solving rewriting lemmas *)
Ltac solve_rw:=
let Ivar:=fresh "I" in
(let Jvar:=fresh "J" in
(let decIvar:=fresh "decI" in
(let decJvar:= fresh "decJ" in
(let rew1:=fresh "Ri" in
(let rew2:=fresh"Rj" in
(intros Ivar Jvar decIvar decJvar; intros;
 simpl; generalize (eqdecX_rw decIvar);
generalize (eqdecX_rw decJvar);intros rew2 rew1;
repeat rewrite rew1;repeat rewrite rew2;auto)))))).

Ltac inverse_same :=match goal with 
| H:(same_shape (pcomma _ ?r1 ?r2) ?t)|-_ =>
  elim (sameShapeCom H); clear H; let Gamma:=fresh "Gamma" in (let
  Gamma':=fresh "Gamma" in (let x:=fresh "R" in (intros
  Gamma H;elim H; clear H; intros Gamma' H; elim H; clear H; intro; intro
  x; elim x; clear x; intros;subst;inverse_same)))
|H:(same_shape (pdiam _ ?r1) ?t) |- _ =>
 elim (sameShapeDiam H); clear H; let Gamma:=fresh "Gamma" in 
(intros Gamma H; elim H; clear H; intros;subst);inverse_same
| _ => idtac
end.

Ltac solve_Inv:=match goal with |H: (apply_rule ?ru ?decI ?decJ ?t)=Some ?t' |-?any
=>
match eval compute in ru with
|(?r1, ?r2) =>cut (same_shape r1 t);
 [intro;inverse_same; repeat econstructor;eauto
 |apply apply_rule_same_shape with decI decJ r2 t'; auto]
end
end.

Ltac solve_inv:=intros; solve_Inv.

Ltac solve_Img:=match goal with 
|H: (apply_rule ?ru ?decI ?decJ ?t)=Some ?t' |-?any
=>
match eval compute in ru with
|(?r1, ?r2) =>cut (same_shape r1 t);[intro;inverse_same;generalize
H;clear H;autorewrite
with ctl_db;injection 1;intros;subst;auto
 |apply apply_rule_same_shape with decI decJ r2 t'; auto]
end
end.

Ltac solve_img_inv:=intros;solve_Img.


(* tactic to solve goals of the form (weakSahlqvist ?rule) *)
Ltac solve_ws:=intros;simpl;auto with arith.

(*********************)
(* tests             *)
(*********************)

Ltac solve_aux I J decI decJ:=
match goal with 
|i:I |- _=>case (decI i i);
[generalize i;clear i;solve_aux I J decI decJ |induction 1;auto]
|j:J |- _=>case (decJ j j);
[generalize j;clear j;solve_aux I J decI decJ |induction 1;auto]
| _=>auto
end.


Ltac solve_rw_bis:=
 let Ivar:=fresh "I" in
(let Jvar:=fresh "J" in
(let decIvar:=fresh "decI" in
(let decJvar:= fresh "decJ" in
(intros Ivar Jvar decIvar decJvar;intros; simpl;solve_aux Ivar Jvar decIvar decJvar)))).


