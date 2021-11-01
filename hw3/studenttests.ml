open Assert
open X86
open Ll
open Backend

(* These tests are provided by you -- they will not be graded  *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let arg_loc_tests = Test ("Unit: arg_loc",
  [ ("arg_loc1", assert_eqf (fun () -> arg_loc 0) (Reg Rdi))
  ; ("arg_loc2", assert_eqf (fun () -> arg_loc 1) (Reg Rsi))
  ; ("arg_loc3", assert_eqf (fun () -> arg_loc 2) (Reg Rdx))
  ; ("arg_loc4", assert_eqf (fun () -> arg_loc 3) (Reg Rcx))
  ; ("arg_loc5", assert_eqf (fun () -> arg_loc 4) (Reg R08))
  ; ("arg_loc6", assert_eqf (fun () -> arg_loc 5) (Reg R09))
  ; ("arg_loc7", assert_eqf (fun () -> arg_loc 6) (Ind3 (Lit 16L, Rbp)))
  ; ("arg_loc8", assert_eqf (fun () -> arg_loc 7) (Ind3 (Lit 24L, Rbp)))
  ; ("arg_loc9", assert_eqf (fun () -> arg_loc 10) (Ind3 (Lit 48L, Rbp)))
  ])

let provided_tests : suite = [
  arg_loc_tests
] 
