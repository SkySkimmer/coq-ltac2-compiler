Fixpoint fact (n : nat) :=
  match n with
  | O => 1
  | S n' => fact n' * S n'
  end.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Constr.
Require Import Ltac2.Control.
Require Import Ltac2.Notations.
Require Import Ltac2Compiler.Ltac2Compiler.

Ltac2 rec iter tac ls :=
  match ls with
  | [] => ()
  | x :: xs => tac x; iter tac xs
  end.

Ltac2 rec find (id : ident) (term : constr) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Cast c cst ty => find id c; find id ty
  | Constr.Unsafe.App f xs => find id f; Array.iter (find id) xs
  | _ => ()
  end.

Ltac2 Compile find.

Goal True.
  ltac1:(pose proof True as x;
         let n := constr:(7) in
         let v := (eval cbv in (fact n)) in
         let c := constr:(eq_refl : fact n = v) in
         do 5 pose c).
  Time let v := Control.hyps () in
       let i := @x in
       iter (fun (h, body, ty) => find i ty; match body with Some b => find i b | None => () end) v.
  (* Finished transaction in 0.75 secs *)
Abort.
