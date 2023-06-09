Require Import Ltac2.Ltac2 Ltac2Compiler.Ltac2Compiler.

Ltac2 big_int := 5000000.

Ltac2 Compile big_int.

Ltac2 rec itern n f x :=
  if Int.equal n 0 then x else itern (Int.sub n 1) f (f x).

Ltac2 test1 n := itern n (fun () => ()) ().

Ltac2 test2 n := itern n (fun x => Int.add x 1) 0.

Ltac2 Compile test1 test2.

Time Ltac2 Eval test1 big_int.

Time Ltac2 Eval test2 big_int.

Ltac2 test3 n := Array.iter (fun () => ()) (Array.make n ()).

Ltac2 Compile test3.

Time Ltac2 Eval test3 big_int.
