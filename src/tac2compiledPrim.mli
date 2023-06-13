(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ltac2_plugin.Tac2ffi
open Proofview

val array_empty : valexpr -> valexpr tactic
val array_make : valexpr -> valexpr -> valexpr tactic
val array_length : valexpr -> valexpr tactic
val array_set : valexpr -> valexpr -> valexpr -> valexpr tactic
val array_get : valexpr -> valexpr -> valexpr tactic
val int_equal : valexpr -> valexpr -> valexpr tactic
val int_compare : valexpr -> valexpr -> valexpr tactic
val int_add : valexpr -> valexpr -> valexpr tactic
val int_sub : valexpr -> valexpr -> valexpr tactic
val int_mul : valexpr -> valexpr -> valexpr tactic
val int_div : valexpr -> valexpr -> valexpr tactic
val int_mod : valexpr -> valexpr -> valexpr tactic
val int_neg : valexpr -> valexpr tactic
val int_abs : valexpr -> valexpr tactic
val int_asr : valexpr -> valexpr -> valexpr tactic
val int_lsl : valexpr -> valexpr -> valexpr tactic
val int_lsr : valexpr -> valexpr -> valexpr tactic
val int_land : valexpr -> valexpr -> valexpr tactic
val int_lor : valexpr -> valexpr -> valexpr tactic
val int_lxor : valexpr -> valexpr -> valexpr tactic
val int_lnot : valexpr -> valexpr tactic

val registered : int CString.Map.t
