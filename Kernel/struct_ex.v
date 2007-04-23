(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                              LaBRI                                   *)
(************************************************************************)

Require Export struct_tacs.
Require Export struct_props.
Set Implicit Arguments.

(* some structural rules that will be used to analyse Dutch cross-dependencies *)
(*******************************************************************************)
(*           weak distributivity of the structural connective <>               *)
(*               <>j (A oi B) --> A oi <>jB                                    *)
(*******************************************************************************)

Definition K2Diam(I J:Set)(i:I) (j:J):structrule I J:=
((pdiam j (pcomma i (pvar 1) (pvar 2))),
 (pcomma i (pvar 1) (pdiam j (pvar 2)))).

Lemma K2Diam_ws:forall(I J:Set)(i:I) (j:J),
                     weakSahlqvist (K2Diam i j).
solve_ws.
Qed.

Lemma K2Diam_rw:forall I J decI decJ  A W  (t1 t2 :context I J A W)
                 (i:I)(j:J),
                (apply_rule (K2Diam i j) decI decJ 
                  (TDiamond j (Comma i t1 t2)))=
                Some (Comma i t1 (TDiamond j t2)).
solve_rw_bis.
Qed.

Hint Rewrite K2Diam_rw:ctl_db.

Lemma K2Diam_Inv:forall I J decI decJ A W (t t':context I J A W)(i:I)(j:J),
                       (apply_rule (K2Diam i j) decI decJ  t)=Some t'->
                       {t1:context I J A W &{
                          t2:context I J A W |
                           t=(TDiamond j (Comma i t1 t2))}}.
solve_inv.
Qed.

Lemma K2DiamImgInv:forall I J decI decJ A W (t1 t2 Gamma:context I J A
W) (i:I)(j:J),
                (apply_rule (K2Diam i j) decI decJ Gamma)=
                Some (Comma i t1 (TDiamond j t2))->
               Gamma=(TDiamond j (Comma i t1 t2)).
solve_img_inv.
Qed.

(******************************************************************************)
(*                        inclusion postulate                                 *)
(*                         <>j1 A --><>j2 A                                   *)
(******************************************************************************)

Definition incDiam (I J:Set)(j1 j2 :J):structrule I J :=
((pdiam j1 (pvar 1)),
 (pdiam j2 (pvar 1))).

Definition incDiam_rw:forall I J decI decJ A W   (t1 :context I J A W)(j1 j2:J),
                      (apply_rule (incDiam I j1 j2) decI decJ (TDiamond j1 t1))=
                      Some (TDiamond j2 t1).
solve_rw_bis.
Qed.

Hint Rewrite incDiam_rw:ctl_db.
Lemma incDiam_Inv :forall I J decI decJ A W   (t t' :context I J A W)(j1 j2:J),
                     (apply_rule (incDiam I j1 j2) decI decJ    t)=Some t'->
                     {t1:context I J A W | t = TDiamond j1 t1}.
solve_inv.
Qed.

Lemma incDiamImgInv:forall I J decI decJ A W   (t1 t2 :context I J A W)(j1 j2:J),
                      (apply_rule (incDiam I j1 j2) decI decJ   t2)=
                      Some (TDiamond j2 t1)->
                      t2=(TDiamond j1 t1).
 solve_img_inv.
Qed.


(******************************************************************************)
(*                     Strong distributivity of <>                            *)
(*                    <>j (A oi B) --><>j A oi <>j B                          *)
(******************************************************************************)

Definition KDiam(I J:Set)(i:I)(j:J) :structrule I J:=
((pdiam j (pcomma i (pvar 1) (pvar 2))),
 (pcomma i (pdiam j (pvar 1)) (pdiam j (pvar 2)))).

Lemma KDiam_rw:forall (I J:Set) decI decJ A W   (t1 t2 :context I J A W) (i:I)(j:J),
                (apply_rule (KDiam i j) decI decJ   (TDiamond j (Comma i t1 t2)))=
                Some (Comma i (TDiamond j t1) (TDiamond j t2)).
solve_rw_bis.
Qed.

Hint Rewrite KDiam_rw:ctl_db.
Lemma KDiam_Inv:forall I J decI decJ A W   (t t':context I J A W)(i:I)(j:J),
                       (apply_rule (KDiam i j) decI decJ    t)=Some t'->
                       {t1:context I J A W &{
                          t2:context I J A W |
                           t=(TDiamond j (Comma i t1 t2))}}.
solve_inv.
Qed.


Lemma KDiamImgInv:forall I J decI decJ A W   (t1 t2 t3 :context I J A W) (i:I)(j:J),
                (apply_rule (KDiam i j) decI decJ   t3)=
                Some (Comma i (TDiamond j t1) (TDiamond j t2))->
                t3=(TDiamond j (Comma i t1 t2)).      
 solve_img_inv.
Qed.

(******************************************************************************)
(*                  Controled Mixed commutativity                             *)
(*            A oi1 (<>j B oi2 C) --> <>j B oi2 (A oi1 C)                     *)            
(******************************************************************************)

Definition MPDiam (I J:Set)(i1 i2:I)(j:J):structrule I J :=
((pcomma i1 (pvar 1) (pcomma i2 (pdiam j (pvar 2)) (pvar 3))),
 (pcomma i2 (pdiam j (pvar 2)) (pcomma i1 (pvar 1) (pvar 3)))).

Lemma MPDiam_rw :forall I J decI decJ A W   (t1 t2 t3 :context I J A W) (i1 i2:I)(j:J),
                (apply_rule (MPDiam i1 i2 j) decI decJ   
                (Comma i1 t1 (Comma i2 (TDiamond j t2) t3)))=
                 Some (Comma i2 (TDiamond j t2) (Comma i1 t1 t3)).
solve_rw_bis.
Qed.


Hint Rewrite MPDiam_rw:ctl_db.

Lemma MPDiam_Inv:forall I J decI decJ A W   (t t':context I J A W) (i1 i2:I)(j:J),
                 (apply_rule (MPDiam i1 i2 j) decI decJ   t)=Some t'->
                 {t1 : context I J A W &
                   {t2 : context I J A W &
                       {t3 :  context I J A W |
                      t=(Comma i1 t1 (Comma i2 (TDiamond j t2) t3))}}}.
solve_inv.
Qed.

Lemma MPDiamImgInv:forall I J decI decJ A W   (t1 t2 t3 t :context I J A W) (i1 i2:I)(j:J),
                (apply_rule (MPDiam i1 i2 j) decI decJ    t)=
                 Some (Comma i2 (TDiamond j t2) (Comma i1 t1 t3))->
                 t = (Comma i1 t1 (Comma i2 (TDiamond j t2) t3)).

 solve_img_inv.
Qed.

(* end of cross-dependencies postulates *)


(* other rules usually used *)

(* simpl rules *)

(******************************************************************************)
(*                       Simpl Associativity 1                                *)
(*                      A oi (B oi C) --> (A oi B) oi C                       *)
(******************************************************************************)
 
Definition L1 (I J:Set)(i:I) : structrule I J :=
   ((pcomma i (pvar 1) (pcomma i (pvar 2) (pvar 3))),
    (pcomma i (pcomma i (pvar 1) (pvar 2)) (pvar 3))).

Lemma L1_rw : forall I J decI decJ A W   (t1 t2 t3 :context I J A W) (i:I),
                (apply_rule (L1 J i) decI decJ   (Comma i t1 (Comma i t2 t3))) =
                Some (Comma i (Comma i t1 t2) t3).
solve_rw_bis.
Qed.

Hint Rewrite L1_rw:ctl_db.

Lemma L1_Inv :  forall I J decI decJ A W   (t t':context I J A W) (i :I),
                (apply_rule (L1 J i) decI decJ   t)= Some t' ->
                {t1 : context I J A W &
                   {t2 : context I J A W &
                       {t3 :  context I J A W |
                       t=  (Comma i t1 (Comma i t2 t3))}}}.        
solve_inv.
Qed.

Lemma L1ImgInv: forall I J decI decJ A W   (t1 t2 t3 t:context I J A W) (i:I),
                (apply_rule (L1 J i) decI decJ   t) =
                Some (Comma i (Comma i t1 t2) t3)->
                t=(Comma i t1 (Comma i t2 t3)).

 solve_img_inv.
Qed.

(******************************************************************************)
(*                           Simpl Associativity 2                            *)
(*                     (A oi B) oi C --> A oi (B oi c)                        *)
(******************************************************************************)

Definition L2(I J:Set) (i:I) : structrule I J :=
   ((pcomma i (pcomma i (pvar 1) (pvar 2)) (pvar 3)),
    (pcomma i (pvar 1) (pcomma i (pvar 2) (pvar 3)))).

Lemma L2_rw : forall (I J:Set)decI decJ A W   (t1 t2 t3 :context  I J A W) (i:I),
                (apply_rule (L2 J i) decI decJ   (Comma i (Comma i t1 t2) t3)
                     = Some (Comma i t1 (Comma i t2 t3))).
solve_rw_bis.
Qed.

Hint Rewrite L2_rw:ctl_db.

Lemma L2_Inv :  forall I J decI decJ A W   (t t':context I J A W) (i :I),
                (apply_rule (L2 J i) decI decJ t)= Some t' ->
                {t1 : context I J A W &
                   {t2 : context I J A W &
                       {t3 :  context I J A W |
                       t=  (Comma i (Comma i t1 t2) t3)}}}.        
solve_inv.
Qed.

Lemma L2ImgInv:forall I J decI decJ A W   (t1 t2 t3 t:context  I J A W) (i:I),
                (apply_rule (L2 J i) decI decJ   t)
                 = Some (Comma i t1 (Comma i t2 t3))->
                 t=(Comma i (Comma i t1 t2) t3).

 solve_img_inv.
Qed.

(******************************************************************************)
(*                          Simpl Commutativity                               *)
(*                           A oi B --> B oi A                                *)
(******************************************************************************)

Definition P (I J:Set)(i:I) : structrule I J :=
   ((pcomma i (pvar 1) (pvar 2)),
    (pcomma i (pvar 2) (pvar 1))).

Lemma P_rw : forall I J decI decJ A W   (t1 t2  :context I J A W) (i:I),
                (apply_rule (P J i) decI decJ   (Comma i t1 t2))
                     = Some (Comma i t2 t1).
solve_rw_bis.
Qed.

Hint Rewrite P_rw:ctl_db.

Lemma P_Inv :  forall I J decI decJ A W    (t t':context I J A W) (i :I),
                (apply_rule (P J i)  decI decJ   t)= Some t' ->
                {t1 : context I J A W &
                   {t2 : context I J A W |
                       t=  (Comma i t1 t2)}}.
solve_inv.
Qed.

Lemma PImgInv:forall I J decI decJ A W   (t1 t2 t :context I J A W) (i:I),
                (apply_rule (P J i) decI decJ   t)
                     = Some (Comma i t2 t1)->
                t=(Comma i t1 t2).
 solve_img_inv.
Qed.

(* interaction postulates *)

(******************************************************************************)
(*                    Controled permutation                                   *)
(*                   <>j A oi B --> B oi <>jA                                 *)
(******************************************************************************)

Definition comDiam(I J:Set) (i:I)(j:J) : structrule I J :=
   ((pcomma i (pdiam j (pvar 1)) (pvar 2)),
    (pcomma i (pvar 2) (pdiam j (pvar 1)))).

Lemma comDiam_rw : forall I J decI decJ A W   (t1 t2 :context I J A W) 
                           (i:I)(j:J),
                (apply_rule (comDiam i j) decI decJ   
                            (Comma i (TDiamond j t1) t2)
                     = Some (Comma i t2 (TDiamond j t1))).
solve_rw_bis.
Qed.


Hint Rewrite comDiam_rw:ctl_db.

Lemma comDiam_Inv :  forall I J decI decJ A W   (t t':context I J A W) (i :I)(j:J),
                (apply_rule (comDiam  i j) decI decJ   t)= Some t' ->
                {t1 : context I J A W &
                   {t2 : context I J A W |
                       t=  (Comma i (TDiamond j t1) t2)}}.
solve_inv.
Qed.

Lemma comDiamImgInv :forall I J decI decJ A W   (t1 t2 t3 t:context I J A W) 
                           (i:I)(j:J),
                (apply_rule (comDiam i j) decI decJ    t)
                = Some (Comma i t2 (TDiamond j t1)) ->
                t=(Comma i (TDiamond j t1) t2).   
 solve_img_inv.
Qed.


(******************************************************************************)
(*                        Mixed associativity 1                               *)
(*                     A oi (B oj C) -->(A oi B) oj C                         *)
(******************************************************************************)

Definition MA1(I J:Set) (i j:I) : structrule I J :=
   ((pcomma i (pvar 1) (pcomma j (pvar 2) (pvar 3))),
    (pcomma j (pcomma i  (pvar 1) (pvar 2)) (pvar 3))).

Lemma MA1_rw : forall I J decI decJ A W   (t1 t2 t3 :context  I J A W) (i j:I),
                (apply_rule (MA1 J i j) decI decJ   (Comma i t1 (Comma j t2 t3)))
                     = Some  (Comma j (Comma i t1 t2) t3).
solve_rw_bis.
Qed.

Hint Rewrite MA1_rw :ctl_db.

Lemma MA1_Inv :  forall I J decI decJ A W   (t t':context I J A W) (i j :I),
                (apply_rule (MA1 J i j) decI decJ   t)= Some t' ->
                {t1 : context I J A W &
                   {t2 : context I J A W &
                       {t3 :  context I J A W |
                       t=  (Comma i t1 (Comma j t2 t3))}}}.        
solve_inv.
Qed.

Lemma MA1ImgInv:forall I J decI decJ A W   (t1 t2 t3 t:context  I J A W) (i j:I),
                (apply_rule (MA1 J i j) decI decJ   t)
                     = Some  (Comma j (Comma i t1 t2) t3)->
                  t=(Comma i t1 (Comma j t2 t3)).
 solve_img_inv.
Qed.

(******************************************************************************)
(*                        Mixed Associativity  2                              *)
(*                     (A oi B) oj C --> A oi (B oj C)                        *)
(******************************************************************************)

Definition MA2 (I J:Set)(i j:I) : structrule I J :=
   ((pcomma j (pcomma i  (pvar 1) (pvar 2)) (pvar 3)),
    (pcomma i (pvar 1) (pcomma j (pvar 2) (pvar 3)))).


Lemma MA2_rw : forall I J decI decJ A W   (t1 t2 t3 :context  I J A W) (i j:I),
                (apply_rule (MA2 J i j) decI decJ   (Comma j (Comma i t1 t2) t3))
                     = Some (Comma i t1 (Comma j t2 t3)).
solve_rw_bis.
Qed.

Hint Rewrite MA2_rw :ctl_db.

Lemma MA2_Inv :  forall I J decI decJ A W   (t t':context I J A W) (i j :I),
                (apply_rule (MA2 J i j) decI decJ   t)= Some t' ->
                {t1 : context I J A W &
                   {t2 : context I J A W &
                       {t3 :  context I J A W |
                       t=  (Comma j (Comma i t1 t2) t3)}}}. 
solve_inv.
Qed.

Lemma MA2ImgInv:forall I J decI decJ A W   (t1 t2 t3 t:context  I J A W) (i j:I),
                (apply_rule (MA2 J i j) decI decJ   t)
                     = Some (Comma i t1 (Comma j t2 t3))->
                  t=(Comma j (Comma i t1 t2) t3).
 solve_img_inv.
Qed.
(******************************************************************************)
(*                       Controled Mixed Associativity 2                      *)
(*                      (A oi B) oi <>j C -->A oi (B oi <>j C)                *)
(******************************************************************************)

Definition MA2Diam(I J:Set) (i:I)(j:J):structrule I J :=
 ((pcomma i (pcomma i (pvar 1) (pvar 2)) (pdiam j (pvar 3))),
   (pcomma i (pvar 1) (pcomma i (pvar 2) (pdiam j (pvar 3))))).

Lemma MA2Diam_rw:forall I J decI decJ A W   (t1 t2 t3 :context  I J A W) (i:I)(j:J),
                 (apply_rule (MA2Diam i j) decI decJ   (Comma i (Comma i t1 t2) (TDiamond j t3)))=
                  Some (Comma i t1 (Comma i t2 (TDiamond j t3))).
solve_rw_bis.
Qed.

Hint Rewrite MA2Diam_rw:ctl_db.

Lemma MA2Diam_Inv :forall I J decI decJ A W   (t t':context I J A W) (i :I)(j:J),
                 (apply_rule (MA2Diam i j) decI decJ   t)= Some t' ->
                 {t1 : context I J A W &
                   {t2 : context I J A W &
                       {t3 :  context I J A W |
                        t = (Comma i (Comma i t1 t2)(TDiamond j t3))}}}.
solve_inv.
Qed.

Lemma MA2DiamImgInv:forall I J decI decJ A W   (t1 t2 t3 t :context  I J A W) (i:I)(j:J),
                 (apply_rule (MA2Diam i j) decI decJ   t)=
                  Some (Comma i t1 (Comma i t2 (TDiamond j t3)))->
                  t=(Comma i (Comma i t1 t2) (TDiamond j t3)).
solve_img_inv.
Qed.

(******************************************************************************)
(*                        Mixed Permutation                                   *)
(*                     A oj (B oi C) -->B oi (A oj C)                         *)
(******************************************************************************)

Definition  MP (I J:Set) (i j:I): structrule I J  :=
  ((pcomma j (pvar 2) (pcomma i (pvar 1) (pvar 3))),
   (pcomma i (pvar 1) (pcomma j (pvar 2) (pvar 3)))).

Lemma MP_rw : forall I J decI decJ A W   (t1 t2 t3 :context  I J A W) (i j:I),
                (apply_rule (MP J i j) decI decJ   (Comma j t2 (Comma i t1 t3)))
                     = Some (Comma i t1 (Comma j t2 t3)).
solve_rw_bis.
Qed.

Hint Rewrite MP_rw:ctl_db.

Lemma MP_Inv :  forall I J decI decJ A W   (t t':context I J A W) (i j :I),
                (apply_rule (MP J i j) decI decJ   t)= Some t' ->
                {t1 : context I J A W &
                   {t2 : context I J A W &
                       {t3 :  context I J A W |
                       t=  (Comma j t2 (Comma i t1 t3))}}}.        
solve_inv.
Qed.

Lemma MPImgInv: forall I J decI decJ A W   (t1 t2 t3 t :context  I J A W) (i j:I),
                (apply_rule (MP J i j) decI decJ   t)
                     = Some (Comma i t1 (Comma j t2 t3))->
                t=(Comma j t2 (Comma i t1 t3)).
 solve_img_inv.
Qed.
(******************************************************************************)
(*                    Controled Mixed Permutation1                            *)
(*                    (A oi B) oi <>j C --> (A oi <>j C) oi B                 *)
(******************************************************************************)

Definition MP1Diam(I J:Set) (i:I)(j:J):structrule I J :=
 ((pcomma i (pcomma i (pvar 1) (pvar 2)) (pdiam j (pvar 3))),
   (pcomma i (pcomma i (pvar 1) (pdiam j (pvar 3))) (pvar 2))).


Lemma MP1Diam_rw:forall I J decI decJ A W   (t1 t2 t3 :context  I J A W) (i:I)(j:J),
                 (apply_rule (MP1Diam i j) decI decJ   
                   (Comma i (Comma i t1 t2) (TDiamond j t3)))=
                  Some (Comma i (Comma i t1 (TDiamond j t3)) t2).
solve_rw_bis.
Qed.

Hint Rewrite MP1Diam_rw:ctl_db.

Lemma MP1Diam_Inv :forall I J decI decJ A W   (t t':context I J A W) (i :I)(j:J),
                 (apply_rule (MP1Diam i j) decI decJ   t)= Some t' ->
                 {t1 : context I J A W &
                   {t2 : context I J A W &
                       {t3 :  context I J A W |
                        t = (Comma i (Comma i t1 t2)(TDiamond j t3))}}}.
solve_inv.
Qed.
 
Lemma MP1DiamImgInv:forall I J decI decJ A W   (t1 t2 t3 t:context  I J A W) (i:I)(j:J),
                 (apply_rule (MP1Diam i j) decI decJ   t)=
                  Some (Comma i (Comma i t1 (TDiamond j t3)) t2)->
                 t= (Comma i (Comma i t1 t2) (TDiamond j t3)).
 solve_img_inv.
Qed.

(*****************************************************************************)
(*                     Controled Mixed Permutation                           *)
(*                      <>j A oi (B oi C) --> B oi (<>j A oi C)              *)
(*****************************************************************************)

Definition MP2Diam(I J:Set) (i:I)(j:J):structrule I J :=
 ((pcomma i (pdiam j (pvar 3)) (pcomma i (pvar 1) (pvar 2))),
   (pcomma i (pvar 1) (pcomma i (pdiam j (pvar 3)) (pvar 2)))).

Lemma MP2Diam_rw:forall I J decI decJ A W   (t1 t2 t3 :context  I J A W) (i:I)(j:J),
                 (apply_rule (MP2Diam i j) decI decJ   (Comma i (TDiamond j t3) (Comma i t1 t2)))=
                  Some (Comma i t1 (Comma i (TDiamond j t3) t2)).
solve_rw_bis.
Qed.

Hint Rewrite MP2Diam_rw:ctl_db.

Lemma MP2Diam_Inv :forall I J decI decJ A W   (t t':context I J A W) (i :I)(j:J),
                 (apply_rule (MP2Diam i j) decI decJ   t)= Some t' ->
                 {t1 : context I J A W &
                   {t2 : context I J A W &
                       {t3 :  context I J A W |
                        t = (Comma i (TDiamond j t3) (Comma i t1 t2))}}}.
solve_inv.
Qed.
 
Lemma MP2DiamImgInv:forall I J decI decJ A W   (t1 t2 t3 t:context  I J A W) (i:I)(j:J),
                 (apply_rule (MP2Diam i j) decI decJ   t)=
                  Some (Comma i t1 (Comma i (TDiamond j t3) t2))->
                  t=(Comma i (TDiamond j t3) (Comma i t1 t2)).
 solve_img_inv.
Qed.
(******************************************************************************)
(*                      Mixed contraction                                     *)
(*                (A oi B) oj C --> (A oj C) oi (B oj C)                      *)
(******************************************************************************)

Definition  MC (I J :Set) (i j:I): structrule I J :=
   ((pcomma j (pcomma i (pvar 1) (pvar 2)) (pvar 3)),
    (pcomma i (pcomma j (pvar 1) (pvar 3)) (pcomma j (pvar 2) (pvar 3)))).

Lemma MC_rw : forall I J decI decJ A W   (t1 t2 t3 :context  I J A W) (i j:I),
                (apply_rule (MC J i j) decI decJ   (Comma j (Comma i t1 t2) t3)
                     = Some (Comma i (Comma j t1 t3) (Comma j t2 t3))).
solve_rw_bis.
Qed.

Hint Rewrite MC_rw:ctl_db.

Lemma MC_Inv :  forall I J decI decJ A W   (t t':context I J A W) (i j :I),
                (apply_rule (MC J i j) decI decJ    t)= Some t' ->
                {t1 : context I J A W &
                   {t2 : context I J A W &
                       {t3 :  context I J A W |
                       t=  (Comma j (Comma i t1 t2) t3)}}}.        
solve_inv.
Qed.

Lemma MCImgInv: forall I J decI decJ A W   (t1 t2 t3 t :context  I J A W) (i j:I),
                (apply_rule (MC J i j) decI decJ   t)
                     = Some (Comma i (Comma j t1 t3) (Comma j t2 t3))->
                t=(Comma j (Comma i t1 t2) t3).
 solve_img_inv.
Qed.


Implicit Arguments L1 [I J].
Implicit Arguments L2 [I J].
Implicit Arguments P[I J].
Implicit Arguments MP[I J].
Implicit Arguments MC[I J].

