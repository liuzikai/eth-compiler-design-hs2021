open Assert
open X86
open Simulator
open Asm

(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)

let provided_tests : suite =
  Unittests_assembler.provided_tests @
  Unittests_simulator.provided_tests @
  Systests_dardanis_bernhard.provided_tests @
  Systests_zikai.provided_tests
