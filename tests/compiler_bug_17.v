From Ltac2 Require Import Ltac2 Printf.

From Ltac2Compiler Require Import Ltac2Compiler.

Declare ML Module "compiler-bugs.compiler_bug_17".

Ltac2 @ external push : unit -> int := "compiler-bugs.compiler_bug_17" "push".
Ltac2 @ external pop : int -> unit := "compiler-bugs.compiler_bug_17" "pop".
Ltac2 @ external reset : unit -> unit := "compiler-bugs.compiler_bug_17" "reset".

Ltac2 test2 () :=
  let outer := push () in
  let inner := push () in
  ltac1:(assert False) >
          [pop inner; pop outer|let outer := push () in pop outer].

Ltac2 Compile test2.

Goal True /\ True.
  test2 ().
Abort.
