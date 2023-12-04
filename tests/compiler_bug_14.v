From Ltac2 Require Import Ltac2.
Ltac2 mutable mut : unit := ().
Ltac2 test () := match mut with () => () end.

From Ltac2Compiler Require Import Ltac2Compiler.

Set Warnings "+tac2compile-skipped-mutable".
Fail Ltac2 Compile test.

Set Warnings "-tac2compile-skipped-mutable".
Ltac2 Compile test.
(*
Dynlink error: execution of module initializers in the shared library failed:
File "plugins/ltac2/tac2env.ml", line 79, characters 2-8: Assertion failed
*)
