open Assert
open Frontend
open Ll

(* These tests are provided by you *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let provided_tests : suite = [
  Test ("decode_ptr_ty", [
    ("decode_ptr_ty_1", assert_eqf (fun () -> decode_ptr_ty (Ptr (I64)) Range.norange) I64)
  ]);

  Test ("decode_arr_elem_ty", [
    ("decode_arr_elem_ty_1", assert_eqf (fun () -> decode_arr_ty (Ptr (Struct [I64; Array (42, I1)]))  Range.norange) (Struct [I64; Array (42, I1)], I1))
  ]);
] 
