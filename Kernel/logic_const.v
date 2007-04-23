(************************************************************************)
(*                          Icharate Toolkit                            *)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                              LaBRI                                   *)
(************************************************************************)
Set Implicit Arguments.
Require Export lambda_bruijn.
Require Export notations.

(* definition of usual logical connectives *)
Inductive logic_cst:Set:=
|AND|EX|EXU|FORALL|OR|IMPL.
Open Scope mmg_scope.

Definition setTypeLog(lc:logic_cst):semType:=
match lc with 
|AND=> t-->t-->t
|OR=>t-->t-->t
|EX=>(e-->t)-->t
|EXU=>(e-->t)-->t
|FORALL=>(e-->t)-->t
|IMPL=>t-->t-->t
end.


