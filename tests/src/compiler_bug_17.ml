open Ltac2_plugin
open Tac2ffi
open Tac2expr
open Tac2externals

let define s = define { mltac_plugin = "compiler-bugs.compiler_bug_17"; mltac_tactic = s }

let state : int ref = Summary.ref ~name:"tac2compile_bug17" 0
let push  : unit -> int  = fun () ->
  state := 1 + !state; !state
let pop   : int -> unit  = fun i ->
  if i == !state then
    state := i - 1
  else
    raise Not_found
let reset : unit -> unit = fun _ -> state := 0

let _ = define "push"  (unit @-> ret int) push
let _ = define "pop"   (int @-> ret unit) pop
let _ = define "reset" (unit @-> ret unit) reset
