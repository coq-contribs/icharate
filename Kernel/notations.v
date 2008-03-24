(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                              LaBRI                                   *)
(************************************************************************)

Require Export lambda_bruijn.

Notation "t1 --> t2":=(funAppli t1 t2) (at level 55,right
associativity):mmg_scope.
Notation "t1 '|*|' t2":=(cartProd t1 t2) (at level 40,left
associativity):mmg_scope.
Notation "'s-->' t":=(intention t)(at level 39):mmg_scope.
Notation "'[[' ty ']]:' l" := (abs ty l )(at level 30):mmg_scope.
(*Notation "'((' l1 l2 '))' " := (appl l1 l2) (at level 41):mmg_scope.*)
(*Notation "'(' l1  ';'  l2 ')'":= (twoL l1 l2) (at level 41):mmg_scope.*)
Notation "'P1' l1" := (pi1 l1) (at level 41):mmg_scope.
Notation "'P2' l2" := (pi2 l2) (at level 41) : mmg_scope.
Notation "'[]' l1" :=(box l1) (at level 41) :mmg_scope.
Notation "'<>' l1" :=(diam l1) (at level 41) :mmg_scope.
Notation "'][' l1" :=(debox l1) (at level 41) :mmg_scope.
Notation "'><' l1 " :=(dediam l1) (at level 41) :mmg_scope.
Notation "'@' x":= (ress x)(at level 41) :mmg_scope.
Notation "'%' i":= (num _ i) (at level 41) :mmg_scope.