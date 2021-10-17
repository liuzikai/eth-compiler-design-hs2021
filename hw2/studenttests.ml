open Assert
open X86
open Simulator
open Asm

(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)

let helloword_text_elems = [ text "foo"
                             [ Xorq, [~%Rax; ~%Rax]
                             ; Movq, [~$100; ~%Rax]
                             ; Retq, []
                             ]
                      ; text "main"
                             [ Xorq, [~%Rax; ~%Rax]
                             ; Movq, [Ind1 (Lbl "baz"); ~%Rax]
                             ; Retq, []
                             ]]
let helloword_data_elems = [ data "baz" 
                                  [ Quad (Lit 99L)
                                  ; Asciz "Hello, world!"
                                  ]]
let helloword_text_labels = [("foo", 0x400000L); ("main", 0x400018L)]
let helloword_data_labels = [("baz", 0x400030L)]
let helloword_labels = helloword_text_labels @ helloword_data_labels

let provided_tests : suite = [
  Test ("separate_segments", [
    ("separate_segments_1", assert_eqf (fun () -> separate_segments []) ([], []));
    ("separate_segments_2", assert_eqf (fun () -> separate_segments [text "foo" []]) ([text "foo" []], []));
    ("separate_segments_3", assert_eqf (fun () -> separate_segments [text "foo" []; text "bar" []]) ([text "foo" []; text "bar" []], []));
    ("separate_segments_4", assert_eqf (fun () -> separate_segments [text "foo" []; data "xyz" [Quad (Lit 42L)]; gtext "bar" []; data "uvw" []]) ([text "foo" []; gtext "bar" []], [data "xyz" [Quad (Lit 42L)]; data "uvw" []]));
  ]);

  Test ("calc_label_addresses", [
    ("calc_label_addresses_1", assert_eqf (fun () -> calc_label_addresses 0L []) ([], 0L));
    ("calc_label_addresses_2", assert_eqf (fun () -> calc_label_addresses 0L [text "foo" []]) ([("foo", 0L)], 0L));
    ("calc_label_addresses_3", assert_eqf (fun () -> calc_label_addresses 100L [text "foo" [Retq, []]; text "bar" []]) ([("foo", 100L); ("bar", 108L)], 108L));
    ("calc_label_addresses_4", assert_eqf (fun () -> calc_label_addresses 100L [text "foo" [Retq, []]; text "bar" []; data "xyz" [Quad (Lit 42L)]]) ([("foo", 100L); ("bar", 108L); ("xyz", 108L)], 108L));
    ("calc_label_addresses_5", assert_eqf (fun () -> calc_label_addresses 0x400000L Gradedtests.helloworld) (helloword_labels, 0x400030L));
    ("calc_label_addresses_6", (fun () -> try ignore (calc_label_addresses 0L [text "foo" []; data "foo" []]); failwith "expecting Redefined_sym" with (Redefined_sym "foo") -> ()));
  ]);

  Test ("lookup_label_or_raise_exception", [
    ("lookup_label_or_raise_exception_1", assert_eqf (fun () -> lookup_label_or_raise_exception "foo" [("foo", 100L); ("bar", 108L)]) 100L);
    ("lookup_label_or_raise_exception_2", assert_eqf (fun () -> lookup_label_or_raise_exception "bar" [("foo", 100L); ("bar", 108L)]) 108L);
    ("lookup_label_or_raise_exception_3", (fun () -> try ignore (lookup_label_or_raise_exception "xyz" [("foo", 100L); ("bar", 108L)]); failwith "expecting Undefined_sym" with (Undefined_sym "xyz") -> ()));
    ("lookup_label_or_raise_exception_4", (fun () -> try ignore (lookup_label_or_raise_exception "xyz" []); failwith "expecting Undefined_sym" with (Undefined_sym "xyz") -> ()));
  ]);

  Test ("replace_labels_in_operand", [
    ("replace_labels_in_operand_1", assert_eqf (fun () -> replace_labels_in_operand (Imm (Lbl "foo")) [("foo", 100L); ("bar", 108L)]) (Imm (Lit 100L)));
    ("replace_labels_in_operand_2", assert_eqf (fun () -> replace_labels_in_operand (Imm (Lbl "bar")) [("foo", 100L); ("bar", 108L)]) (Imm (Lit 108L)));
    ("replace_labels_in_operand_3", assert_eqf (fun () -> replace_labels_in_operand (Ind1 (Lbl "bar")) [("foo", 100L); ("bar", 108L)]) (Ind1 (Lit 108L)));
    ("replace_labels_in_operand_4", assert_eqf (fun () -> replace_labels_in_operand (Ind3 (Lbl "bar", Rax)) [("foo", 100L); ("bar", 108L)]) (Ind3 (Lit 108L, Rax)));
    ("replace_labels_in_operand_5", (fun () -> try ignore (replace_labels_in_operand (Imm (Lbl "foo")) []); failwith "expecting Undefined_sym" with (Undefined_sym "foo") -> ()));
  ]);

  Test ("replace_labels_in_ins", [
    ("replace_labels_in_ins_1", assert_eqf (fun () -> replace_labels_in_ins (Jmp, [~$$"loop"]) [("loop", 42L)]) (Jmp, [~$42]));
    ("replace_labels_in_ins_2", assert_eqf (fun () -> replace_labels_in_ins (Jmp, [~$$"loop"; ~$$"loop"]) [("loop", 42L)]) (Jmp, [~$42; ~$42]));
    ("replace_labels_in_ins_3", (fun () -> try ignore (replace_labels_in_ins (Jmp, [~$$"loop"]) []); failwith "expecting Undefined_sym" with (Undefined_sym "loop") -> ()));
  ]);
  
  Test ("replace_labels_in_data", [
    ("replace_labels_in_data_1", assert_eqf (fun () -> replace_labels_in_data (Quad (Lbl "foo")) [("foo", 100L)]) (Quad (Lit 100L)));
    ("replace_labels_in_data_2", assert_eqf (fun () -> replace_labels_in_data (Quad (Lit 100L)) []) (Quad (Lit 100L)));
    ("replace_labels_in_data_3", (fun () -> try ignore (replace_labels_in_data (Quad (Lbl "foo")) []); failwith "expecting Undefined_sym" with (Undefined_sym "foo") -> ()));
  ]);

  Test ("assemble_text_elems", [
    ("assemble_text_elems_1", assert_eqf (fun () -> assemble_text_elems helloword_text_elems helloword_labels) Gradedtests.helloworld_textseg);
    ("assemble_text_elems_2", (fun () -> try ignore (assemble_text_elems helloword_text_elems helloword_text_labels); failwith "expecting Undefined_sym" with (Undefined_sym "baz") -> ()));
    ("assemble_text_elems_3", (fun () -> try ignore (assemble_text_elems Gradedtests.helloworld helloword_labels); failwith "expecting Invalid_argument" with (Invalid_argument _) -> ()));
  ]);
  
  Test ("assemble_data_elems", [
    ("assemble_data_elems_1", assert_eqf (fun () -> assemble_data_elems helloword_data_elems helloword_labels) Gradedtests.helloworld_dataseg);
    ("assemble_data_elems_2", assert_eqf (fun () -> assemble_data_elems [data "foo" [Quad (Lbl "bar")]] [("foo", 100L); ("bar", 108L)]) [Byte '\x6C'; Byte '\x00'; Byte '\x00'; Byte '\x00'; Byte '\x00'; Byte '\x00'; Byte '\x00'; Byte '\x00']);
    ("assemble_data_elems_3", (fun () -> try ignore (assemble_data_elems Gradedtests.helloworld helloword_labels); failwith "expecting Invalid_argument" with (Invalid_argument _) -> ()));
  ]);

] 
