open Ltac2_plugin
open Tac2ffi
open Tac2expr
open Tac2externals

let define s = define { mltac_plugin = "compiler-bugs.compiler_bug_17"; mltac_tactic = s }

let state : int Summary.Ref.t = Summary.ref ~name:"tac2compile_bug17" 0
let push  : unit -> int  = fun () ->
  let open Summary.Ref in
  state := 1 + !state; !state
let pop   : int -> unit  = fun i ->
  let open Summary.Ref in
  if i == !state then
    state := i - 1
  else
    raise Not_found
let reset : unit -> unit =
  let open Summary.Ref in
  fun _ -> state := 0

let _ = define "push"  (unit @-> ret int) push
let _ = define "pop"   (int @-> ret unit) pop
let _ = define "reset" (unit @-> ret unit) reset
