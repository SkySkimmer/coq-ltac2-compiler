From Ltac2 Require Import Ltac2 RedFlags.
From Ltac2Compiler Require Import Ltac2Compiler.

Ltac2 beta_iota :=
  let x := RedFlags.all in x.

Ltac2 Compile beta_iota.
