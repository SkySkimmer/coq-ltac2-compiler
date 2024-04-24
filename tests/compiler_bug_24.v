Require Import Ltac2Compiler.Ltac2Compiler.
From Ltac2 Require Import Array.
Ltac2 test () := Array.empty.
Ltac2 Eval Array.length (test ()).
Ltac2 Compile Array.empty.
Ltac2 Eval Array.length (test ()).
