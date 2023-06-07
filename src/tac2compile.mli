(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val perform_compile : ?recursive:bool -> qualid list -> unit
(** Default [recursive:true] *)

(** for communication with dynlinked code *)

val spilled_kns : Names.KerName.t array ref

val spilled_exts : Tac2dyn.Arg.glb array ref
