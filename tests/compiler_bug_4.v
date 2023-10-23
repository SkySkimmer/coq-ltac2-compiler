Require Import Ltac2.Ltac2 Ltac2Compiler.Ltac2Compiler.

Ltac2 foo class class0 := Int.add class class0.

Ltac2 bar class0 class := Int.add class class0.

Ltac2 Compile foo bar.

Ltac2 Eval Control.assert_true (Int.equal (foo 1 2) 3).
Ltac2 Eval Control.assert_true (Int.equal (bar 1 2) 3).
