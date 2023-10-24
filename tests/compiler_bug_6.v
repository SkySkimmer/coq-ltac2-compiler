Require Import Ltac2.Ltac2 Ltac2Compiler.Ltac2Compiler.

Ltac2 foo φ := φ.

Ltac2 φ () := 1.

Ltac2 xx () := 2.

Ltac2 Compile foo φ xx.

(* "φ" gets replaced by "xx", ensure we avoided collision *)

Ltac2 Eval Control.assert_true (Int.equal (φ()) 1).

Ltac2 Eval Control.assert_true (Int.equal (xx()) 2).
