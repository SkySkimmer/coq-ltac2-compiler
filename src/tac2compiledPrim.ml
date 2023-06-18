(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Ltac2_plugin
open Tac2ffi
open Proofview.Notations

let core_prefix path n = KerName.make path (Label.of_id (Id.of_string_soft n))

let coq_core n = core_prefix Tac2env.coq_prefix n

let err_outofbounds =
  Tac2interp.LtacError (coq_core "Out_of_bounds", [||])

let err_division_by_zero =
  Tac2interp.LtacError (coq_core "Division_by_zero", [||])

let return x = Proofview.tclUNIT x

let v_unit = Tac2ffi.of_unit ()
let v_blk = Valexpr.make_block

let throw = Tac2core.throw

let wrap f =
  return () >>= fun () -> return (f ())

let wrap_unit f =
  return () >>= fun () -> f (); return v_unit

let registered = ref []

let define name arity f =
  registered := (name,arity) :: !registered;
  f

(* Adds a thunk *)
let define0 name v =
  define name 1 (fun (_:valexpr) -> v)

let define1 name r0 f =
  define name 1 (fun x0 -> f (repr_to r0 x0))

let define2 name r0 r1 f =
  define name 2 (fun x0 x1 -> f (repr_to r0 x0) (repr_to r1 x1))

let define3 name r0 r1 r2 f =
  define name 3 (fun x0 x1 x2 -> f (repr_to r0 x0) (repr_to r1 x1) (repr_to r2 x2))

let array_empty = define0 "array_empty" (return (ValBlk (0, [||])))

let array_make = define2 "array_make" int valexpr begin fun n x ->
  if n < 0 || n > Sys.max_array_length then throw err_outofbounds
  else wrap (fun () -> v_blk 0 (Array.make n x))
end

let array_length = define1 "array_length" block begin fun (_, v) ->
  return (of_int (Array.length v))
end

let array_set = define3 "array_set" block int valexpr begin fun (_, v) n x ->
  if n < 0 || n >= Array.length v then throw err_outofbounds
  else wrap_unit (fun () -> v.(n) <- x)
end

let array_get = define2 "array_get" block int begin fun (_, v) n ->
  if n < 0 || n >= Array.length v then throw err_outofbounds
  else wrap (fun () -> v.(n))
end

let int_equal = define2 "int_equal" int int begin fun m n ->
  return (of_bool (m == n))
end

let unop n f = define1 n int begin fun m ->
  return (of_int (f m))
end

let binop n f = define2 n int int begin fun m n ->
  return (of_int (f m n))
end

let int_compare = binop "int_compare" Int.compare
let int_add = binop "int_add" (+)
let int_sub = binop "int_sub" (-)
let int_mul = binop "int_mul" ( * )
let int_div = define2 "int_div" int int begin fun m n ->
  if n == 0 then throw err_division_by_zero
  else return (of_int (m / n))
end
let int_mod = define2 "int_mod" int int begin fun m n ->
  if n == 0 then throw err_division_by_zero
  else return (of_int (m mod n))
end
let int_neg = unop "int_neg" (~-)
let int_abs = unop "int_abs" abs

let int_asr = binop "int_asr" (asr)
let int_lsl = binop "int_lsl" (lsl)
let int_lsr = binop "int_lsr" (lsr)
let int_land = binop "int_land" (land)
let int_lor = binop "int_lor" (lor)
let int_lxor = binop "int_lxor" (lxor)
let int_lnot = unop "int_lnot" lnot

let registered = CString.Map.of_list !registered
