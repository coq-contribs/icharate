Require Export tacticsDed.
Require Export struct_ex.

(* G \a F |- (H\a G) \a (H \a F) *)
(* example of derived rule in L *)
Definition Geach_main_Back :
 forall (I J A W:Set)(r:resource W) (F G H : Form I J
 A)(a:I)(ext:extension I J)eqdecI eqdecJ,
 (in_extension (L1 a) ext)->
 natded  eqdecI eqdecJ ext (res r (Backslash a G F))
 (Backslash a (Backslash a H  G)
 (Backslash a H  F)).
intros.
backI 0.
backI 1.
z_root.
structH H0.
ebackE;[idtac|axiom].
ebackE;axiom.
Qed.