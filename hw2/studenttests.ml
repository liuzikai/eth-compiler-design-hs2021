open Assert
open X86
open Simulator
open Asm

(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)

(* ============================================================ *)
(*                   Unit Tests for Simulator                   *)
(* ============================================================ *)

let simple_machine = Gradedtests.test_machine []

let provided_tests : suite = [

  Test ("get_ind_mem_addr", [
    ("get_ind_mem_addr_1", assert_eqf (fun () -> get_ind_mem_addr simple_machine (Ind1 (Lit 42L))) 42L);
    ("get_ind_mem_addr_2", assert_eqf (fun () -> get_ind_mem_addr simple_machine (Ind2 Rip)) mem_bot);
    ("get_ind_mem_addr_3", assert_eqf (fun () -> get_ind_mem_addr simple_machine (Ind3 (Lit 42L, Rip))) 0x40002AL);
    ("get_ind_mem_addr_4", (fun () -> try ignore (get_ind_mem_addr simple_machine (Imm (Lit 42L))); failwith "expecting Invalid_argument" with (Invalid_argument _) -> ()));
  ]);

  Test ("get_opd_val", [
    ("get_opd_val_1", assert_eqf (fun () -> get_opd_val simple_machine (Imm (Lit 42L))) 42L);
    ("get_opd_val_2", assert_eqf (fun () -> get_opd_val simple_machine (Reg Rip)) mem_bot);
    ("get_opd_val_3", assert_eqf (fun () -> get_opd_val simple_machine (Ind3 (Lit 0L, Rip))) 0L);
  ]);
]

(* ============================================================ *)
(*                   Unit Tests for Assembler                   *)
(* ============================================================ *)

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

let provided_tests : suite = provided_tests @ [
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


(* ============================================================ *)
(*   System Tests from Nicola Dardanis and David Bernhard       *)
(* ============================================================ *)
(* @nicdard and @dbernhard-0x7CD *)
(* https://github.com/nicdard/compiler-design-eth-tests/raw/main/02/studenttests.ml *)

(* Function prologue and epilogue. *)
let function_prologue : ins list =
  Asm.([
      Pushq, [~%Rbp]
    ; Movq, [~%Rsp; ~%Rbp]
  ])

let function_epilogue : ins list =
  Asm.([
      Popq, [~%Rbp]
    ; Retq, []
  ])

let empty_main = text "main" @@ function_prologue @ function_epilogue

(* A driver main, just call some other function *)
let main_driver = text "main" @@ function_prologue @ [
  Callq, [ Imm (Lbl ("fun")) ]
] @ function_epilogue

let function_builder (name:string) (body:ins list) =
  text name (function_prologue @ body @ function_epilogue)

let default_fun_builder = function_builder "fun"

let negq = [
  default_fun_builder [ Movq, [ Ind1 (Lbl "data1"); ~%Rax ]
                      ; Negq, [ ~%Rax ]
                      ; Movq, [ ~%Rax; Ind1 (Lbl "data1") ]
                      ]
  ; data "data1" [ Quad(Lit 99L)
                 ; Asciz "Some other data"
                 ]
]

let addq = [
  default_fun_builder [ Movq, [ ~$1; ~%Rax ]
                      ; Movq, [ ~$$"data1"; ~%R12 ]
                      ; Addq, [ Ind3 ( Lit 8L, R12 ); ~%Rax ]
                      ]
  ; data "data1" [ Quad(Lit (-1L))
                 ; Quad(Lit 2L)
                 ; Quad(Lit Int64.max_int)
                 ]
]

let fibonacci = [
  text "fibonacci" @@ function_prologue @
                   [ Movq, [ ~$1; ~%Rax ] (* Prepare the return value for base case. *)
                   ; Cmpq, [ ~$2; ~%Rdi ]
                   ; J Le, [ ~$$".exit" ]
                   ; Subq, [ ~$16; ~%Rsp ] (* Reserve stack space for recursive call argument and intermidiate result. *)
                   ; Subq, [ ~$2; ~%Rdi ]
                   ; Movq, [ ~%Rdi; Ind3 (Lit (-8L), Rbp) ] (* Save intermediate argument. *)
                   ; Addq, [ ~$1; ~%Rdi ] (* Prepare first recursive call argument. *)
                   ; Callq, [ ~$$"fibonacci" ] (* Recursively call with n - 1. *)
                   ; Movq, [ ~%Rax; Ind3 (Lit (-16L), Rbp) ] (* Store intermidiate result in stack. *)
                   ; Movq, [ Ind3 (Lit (-8L), Rbp); ~%Rdi ] (* Prepare second recursive call argument. *)
                   ; Callq, [ ~$$"fibonacci" ] (* Recursively call with n - 2. *)
                   ; Addq, [ Ind3 (Lit (-16L), Rbp); ~%Rax ] (* Prepare result. *)
                   ; Addq, [ ~$16; ~%Rsp ] (* Shrink the stack. *)
                   ]
  ; text ".exit" function_epilogue
  ; default_fun_builder [ Movq, [ ~$30; ~%Rdi ]
                        ; Callq, [ ~$$"fibonacci" ]
                        ]
]

let cc_not = fun () -> Gradedtests.test_machine
  [InsB0 (Movq, [~$1; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Notq, [~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let cc_not_negative = fun () -> Gradedtests.test_machine
  [InsB0 (Xorq, [~$1; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag (* sets all flags to false *)
  ;InsB0 (Movq, [~$1; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Notq, [~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let cc_and = fun () -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit 0x0F0F0F0FL); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Andq, [Imm (Lit 0xF0F0F0FFL); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let cc_or = fun () -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit 0x0F0F0F0FL); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Orq,  [Imm (Lit 0xF0F0F0F0L); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let cc_xor = fun () -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit 0x0F0F0F0FL); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Orq,  [Imm (Lit 0xF0F0F0F0L); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let cc_sar = fun (n:int) (v:Int64.t) -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit v); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Sarq, [~$n; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let cc_shl = fun (n:int) (v:Int64.t) -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit v); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Shlq, [~$n; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let cc_shr = fun (n:int) (v:Int64.t) -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit v); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Shrq, [~$n; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let cc_incr = fun (src:Int64.t) -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit src); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Incq, [~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let cc_decr = fun (src:Int64.t) -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit src); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Decq, [~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let cc_sub = fun (dest:Int64.t) (src:Int64.t) -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit dest); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Subq, [Imm (Lit src); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let condition_flag_set_tests =
  [ (* Logic instruction. *)
    ("cc_and", Gradedtests.cs_test 2 (cc_and ()) (false, false, false))
  ; ("cc_or",  Gradedtests.cs_test 2 (cc_or  ()) (false, false, false))
  ; ("cc_xor", Gradedtests.cs_test 2 (cc_xor ()) (false, false, false))
  ; ("cc_not", Gradedtests.csi_test 2 (cc_not ()))
  ; ("cc_not_negative", Gradedtests.cs_test 3 (cc_not_negative ()) (false, false, false))

    (* Bit-manipulation instructions. *)
  ; ("cc_sar_0_a", Gradedtests.cc_test "OF:false SF:false ZF:false" 2 (cc_sar 0 0x0F0F0F0FL) (false, false, false)
      (fun m -> not (m.flags.fo || m.flags.fs || m.flags.fz)))
  ; ("cc_sar_0_b", Gradedtests.cc_test "OF:false SF:false ZF:false" 2 (cc_sar 0 0x0F0F0F0FL) (true, false, true)
      (fun m -> m.flags.fo && (not m.flags.fs) && m.flags.fz))
  ; ("cc_sar_0_c", Gradedtests.csi_test 2 (cc_sar 0 0x0F0F0F0FL))
  ; ("cc_sar_1", Gradedtests.cso_test 2 (cc_sar 1 0x0F0F0F0FL) false)
  ; ("cc_sar_1_neg_a", Gradedtests.cso_test 2 (cc_sar 1 Int64.min_int) false)
  ; ("cc_sar_1_neg_b", Gradedtests.cc_test "OF:false SF:true ZF:false" 2 (cc_sar 1 Int64.min_int) (true, false, true)
      (fun m -> not m.flags.fo && m.flags.fs && not m.flags.fz))
  ; ("cc_sar_max_a", Gradedtests.cc_test "OF:false SF:false ZF:true" 2 (cc_sar 63 Int64.max_int) (true, true, false)
      (fun m -> m.flags.fo && not (m.flags.fs) && m.flags.fz))
  ; ("cc_sar_max_b", Gradedtests.cc_test "OF:false SF:false ZF:true" 2 (cc_sar 63 Int64.max_int) (false, true, false)
      (fun m -> not m.flags.fo && not m.flags.fs && m.flags.fz))

  ; ("cc_shl_0_a", Gradedtests.cc_test "OF:false SF:false ZF:false" 2 (cc_shl 0 Int64.max_int) (false, false, false)
    (fun m -> not (m.flags.fo || m.flags.fs || m.flags.fz)))
  ; ("cc_shl_0_b", Gradedtests.cc_test "OF:false SF:false ZF:false" 2 (cc_shl 0 Int64.max_int) (true, false, true)
    (fun m -> m.flags.fo && (not m.flags.fs) && m.flags.fz))
  ; ("cc_shl_0_c", Gradedtests.csi_test 2 (cc_shl 0 Int64.max_int))
  ; ("cc_shl_1", Gradedtests.cso_test 2 (cc_shl 1 Int64.max_int) true)
  ; ("cc_shl_1_neg_a", Gradedtests.cso_test 2 (cc_shl 1 Int64.min_int) true)
  ; ("cc_shl_1_neg_b", Gradedtests.cc_test "OF:true SF:false ZF:true" 2 (cc_shl 1 Int64.min_int) (false, true, false)
    (fun m -> m.flags.fo && (not m.flags.fs) && m.flags.fz))
  ; ("cc_shl_n_a", Gradedtests.cc_test "OF:false SF:false ZF:false" 2 (cc_shl 1 12L) (false, true, true)
    (fun m -> not m.flags.fo && not m.flags.fs && not m.flags.fz))
  ; ("cc_shl_n_a", Gradedtests.cc_test "OF:false SF:true ZF:false" 2 (cc_shl 60 12L) (false, false, true)
    (fun m -> not m.flags.fo && m.flags.fs && not m.flags.fz))
  ; ("cc_shl_zero", Gradedtests.cc_test "OF:false SF:false ZF:true" 2 (cc_shl 1 0L) (false, true, false)
    (fun m -> (not m.flags.fo) && (not m.flags.fs) && m.flags.fz))

  ; ("cc_shr_0_a", Gradedtests.cc_test "OF:false SF:false ZF:false" 2 (cc_shr 0 Int64.min_int) (false, false, false)
    (fun m -> not (m.flags.fo || m.flags.fs || m.flags.fz)))
  ; ("cc_shr_0_b", Gradedtests.csi_test 2 (cc_shr 0 Int64.max_int))
  ; ("cc_shr_1", Gradedtests.cso_test 2 (cc_shr 1 0x0F0F0F0FL) false)
  ; ("cc_shr_1_neg", Gradedtests.cso_test 2 (cc_shr 1 Int64.min_int) true)
  ; ("cc_shr_max", Gradedtests.cc_test "OF:true SF:false ZF:false" 2 (cc_shr 3 Int64.max_int) (true, true, true)
      (fun m -> m.flags.fo && not m.flags.fs && not m.flags.fz))
  ; ("cc_shr_max", Gradedtests.cc_test "OF:true SF:false ZF:true" 2 (cc_shr 63 Int64.max_int) (true, true, false)
      (fun m -> m.flags.fo && not m.flags.fs && m.flags.fz))

    (* Arithmetic instructions. *)
  ; ("cc_sub_1", Gradedtests.cs_test 2 (cc_sub 0xFFFFFFFFFFFFFFFFL (-1L)) (false, false, true))
  ; ("cc_sub_2", Gradedtests.cs_test 2 (cc_sub 0xFFFFFFFFFFFFFFFFL 1L) (false, true, false))
  ; ("cc_sub_3", Gradedtests.cs_test 2 (cc_sub Int64.min_int 42L) (true, false, false))
  ; ("cc_sub_4", Gradedtests.cs_test 2 (cc_sub (-1233291893L) Int64.max_int) (true, false, false))

  ; ("cc_incr", Gradedtests.cs_test 2 (cc_incr Int64.max_int) (true, true, false))
  ; ("cc_incr", Gradedtests.cs_test 2 (cc_incr (-1L)) (false, false, true))
  ; ("cc_decr", Gradedtests.cs_test 2 (cc_decr Int64.min_int) (true, false, false))
  ; ("cc_decr", Gradedtests.cs_test 2 (cc_decr 1L) (false, false, true))
  ]


let leaq = fun () -> Gradedtests.test_machine
  [InsB0 (Leaq, [Ind1 (Lit (mem_bot)); ~%R12]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [Imm (Lit (Int64.add mem_bot @@ Int64.mul ins_size 4L)); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Leaq, [Ind2 Rax; ~%Rbx]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Leaq, [Ind3 (Lit ins_size, Rbx); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let jmp = fun (src:operand) -> Gradedtests.test_machine
  [InsB0 (Jmp, [src]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let jmp_ind_1 = fun () -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit (Int64.add mem_bot 24L)); Ind1 (Lit (Int64.add mem_bot 24L))]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [Imm (Lit (Int64.add mem_bot 24L)); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Jmp, [Ind1 (Lit (Int64.add mem_bot 24L))]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let jmp_ind_2 = fun () -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit (Int64.add mem_bot 24L)); Ind1 (Lit (Int64.add mem_bot 24L))]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [Imm (Lit (Int64.add mem_bot 24L)); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Jmp, [Ind2 Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let jmp_ind_3 = fun () -> Gradedtests.test_machine
  [InsB0 (Movq, [Imm (Lit (Int64.add mem_bot 24L)); Ind1 (Lit (Int64.add mem_bot 32L))]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [Imm (Lit (Int64.add mem_bot 24L)); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Jmp, [Ind3 (Lit 8L, Rax)]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let callq = fun (src:quad) -> Gradedtests.test_machine
  [InsB0 (Movq,  [Imm (Lit src); Ind1 (Lit src)]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Callq, [Ind1 (Lit src)]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let ret = fun () -> Gradedtests.test_machine
  [InsB0 (Movq,  [Imm (Lit 4194328L); ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Callq, [~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Retq, []);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Retq, []);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let j = fun (cnd:cnd) (n:int) (src:quad) -> Gradedtests.test_machine
  [InsB0 (Addq, [~$n; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (J cnd, [Imm (Lit src)]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let bin_log = fun (op:opcode) -> Gradedtests.test_machine
  [InsB0 (Movq, [~$2; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [~$3; ~%Rbx]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [~$255; ~%Rcx]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [~$1; Gradedtests.stack_offset 0L]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (op, [~%Rax; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (op, [~$2; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (op, [~%Rax; ~%Rbx]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (op, [Gradedtests.stack_offset 0L; ~%Rcx]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let notq = fun () -> Gradedtests.test_machine
  [InsB0 (Movq, [~$2; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [Imm (Lit (Int64.min_int)); Gradedtests.stack_offset 0L]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Notq, [~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Notq, [Gradedtests.stack_offset 0L]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let shr = fun (op:opcode) -> Gradedtests.test_machine
  [InsB0 (Movq, [~$256; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [Imm (Lit (Int64.min_int)); Gradedtests.stack_offset 0L]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [~$63; ~%Rcx]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (op, [~$2; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (op, [~%Rcx; Gradedtests.stack_offset 0L]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let setb = fun (cnd:cnd) -> Gradedtests.test_machine
  [InsB0 (Addq, [~$256; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Set cnd, [~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Addq, [Imm (Lit (Int64.max_int)); Gradedtests.stack_offset 0L]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Set cnd, [Gradedtests.stack_offset 0L]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let bin_aop = fun (op:opcode) -> Gradedtests.test_machine
  [InsB0 (Movq, [~$2; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (Movq, [~$22; ~%Rbx]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ;InsB0 (op, [~%Rbx; ~%Rax]);InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag;InsFrag
  ]

let instruction_tests = [
  ("leaq", Gradedtests.machine_test "r12=4194304L rbx=4194336L rax=4194344L" 4 (leaq ())
    (fun m -> m.regs.(rind R12) = mem_bot
           && m.regs.(rind Rbx) = (Int64.add mem_bot @@ Int64.mul ins_size 4L)
           && m.regs.(rind Rax) = (Int64.add mem_bot @@ Int64.mul ins_size 5L)
    )
  );
  ("jmp_lit", Gradedtests.machine_test "rip=0x400000L" 1 (jmp @@ Imm (Lit(mem_bot)))
    (fun m -> m.regs.(rind Rip) = mem_bot)
  );
  ("jmp_reg", Gradedtests.machine_test "rip=4259832L" 1 (jmp ~%Rsp)
    (fun m -> m.regs.(rind Rsp) = Int64.sub mem_top 8L
           && m.regs.(rind Rip) = Int64.sub mem_top 8L)
  );
  ("jmp_ind1", Gradedtests.machine_test "rip=4194328L" 3 (jmp_ind_1 ())
    (fun m -> m.regs.(rind Rip) = Int64.add mem_bot 24L)
  );
  ("jmp_ind2", Gradedtests.machine_test "rip=4194328L" 3 (jmp_ind_2 ())
    (fun m -> m.regs.(rind Rip) = Int64.add mem_bot 24L)
  );
  ("jmp_ind3", Gradedtests.machine_test "rip=4194328L" 3 (jmp_ind_3 ())
    (fun m -> m.regs.(rind Rip) = Int64.add mem_bot 24L)
  );
  ("call", Gradedtests.machine_test "rip=4194328L rsp=4259824L" 2 (callq 4194328L)
    (fun m -> m.regs.(rind Rip) = 4194328L
           && m.regs.(rind Rsp) = Int64.sub mem_top 16L
           (* Stack contains next instruction to be called in the caller. *)
           && int64_of_sbytes (Gradedtests.sbyte_list m.mem (mem_size - 16)) = Int64.add mem_bot 16L));
  ("ret_1", Gradedtests.machine_test "rip=4194320L" 3 (ret ())
    (fun m -> m.regs.(rind Rip) = 4194320L));
  ("ret_2", Gradedtests.machine_test "rip=0L" 4 (ret ())
    (* machine_test doesn't set the sentinel address. *)
    (fun m -> m.regs.(rind Rip) = 0L));
  ("j_1", Gradedtests.machine_test "rip=4259832L" 2 (j Eq 0 4259832L)
    (fun m -> m.flags.fz && m.regs.(rind Rip) = 4259832L));
  ("j_2", Gradedtests.machine_test "rip=4194320L" 2 (j Neq 0 4259832L)
    (fun m -> m.flags.fz && m.regs.(rind Rip) = 4194320L));
  ("j_3", Gradedtests.machine_test "rip=4194320L" 2 (j Lt 12 4259832L)
    (fun m -> not m.flags.fz && not m.flags.fs && m.regs.(rind Rip) = 4194320L));
  ("orq", Gradedtests.machine_test "rax=2 rbx=3 rcx=255 *65528=1" 8 (bin_log Orq)
    (fun m -> m.regs.(rind Rax) = 2L
           && m.regs.(rind Rbx) = 3L
           && m.regs.(rind Rcx) = 255L
           && int64_of_sbytes (Gradedtests.sbyte_list m.mem (mem_size-8)) = 1L
    )
  );
  ("xorq", Gradedtests.machine_test "rax=2 rbx=1 rcx=254 *65528=1" 8 (bin_log Xorq)
    (fun m -> m.regs.(rind Rax) = 2L
           && m.regs.(rind Rbx) = 1L
           && m.regs.(rind Rcx) = 254L
           && int64_of_sbytes (Gradedtests.sbyte_list m.mem (mem_size-8)) = 1L
    )
  );
  ("notq", Gradedtests.machine_test "rax=-3L *65528=Int64.max_int" 4 (notq ())
    (fun m -> m.regs.(rind Rax) = -3L
           && int64_of_sbytes (Gradedtests.sbyte_list m.mem (mem_size-8)) = Int64.max_int
    )
  );
  ("shrq", Gradedtests.machine_test "rax=64L *65528=1L" 5 (shr (Shrq))
    (fun m -> m.regs.(rind Rax) = 64L
      && int64_of_sbytes (Gradedtests.sbyte_list m.mem (mem_size-8)) = 1L
    )
  );
  ("sraq", Gradedtests.machine_test "rax=64L *65528=-1L" 5 (shr (Sarq))
    (fun m -> m.regs.(rind Rax) = 64L
      && int64_of_sbytes (Gradedtests.sbyte_list m.mem (mem_size-8)) = -1L
    )
  );
  ("setb", Gradedtests.machine_test "rax=256L *65528=0x7FFFFFFFFFFFFF00L" 4 (setb (Lt))
    (fun m -> m.regs.(rind Rax) = 256L
      && int64_of_sbytes (Gradedtests.sbyte_list m.mem (mem_size-8)) = Int64.sub Int64.max_int 255L
    )
  );
  ("setb", Gradedtests.machine_test "rax=257L *65528=0x7FFFFFFFFFFFFF01L" 4 (setb (Gt))
    (fun m -> m.regs.(rind Rax) = 257L
      && int64_of_sbytes (Gradedtests.sbyte_list m.mem (mem_size-8)) = Int64.sub Int64.max_int 254L
    )
  );
  ("addq", Gradedtests.machine_test "rax=24L" 3 (bin_aop Addq)
    (fun m -> m.regs.(rind Rax) = 24L));
  ("subq", Gradedtests.machine_test "rax=24L" 3 (bin_aop Subq)
    (fun m -> m.regs.(rind Rax) = -20L));
]

let provided_tests : suite = provided_tests @ [
  Test ("Debug: End-to-end Tests", [
    ("empty main", Gradedtests.program_test [empty_main] 0L)
    ; ("negq", Gradedtests.program_test (main_driver::negq) (Int64.neg 99L) )
    ; ("addq", Gradedtests.program_test (main_driver::addq) 3L )
    ; ("fibonacci", Gradedtests.program_test (main_driver::fibonacci) 832040L)
  ]);
  Test ("Debug: Condition Flags Set Tests", condition_flag_set_tests);
  Test ("Debug: Instruction Tests", instruction_tests)
]

(* ============================================================ *)
(*                 System Tests from Zikai Liu                  *)
(* ============================================================ *)

let parse_int = [
  text "_Z9parse_intPKcl" [
      Pushq, [ ~%Rbp ]
    ; Movq, [ ~%Rsp; ~%Rbp ]
    ; Movq, [ ~%Rdi; Ind3 (Lit (-8L), Rbp) ]
    ; Movq, [ ~%Rsi; Ind3 (Lit (-16L), Rbp) ]
    ; Movq, [ ~$0; Ind3 (Lit (-24L), Rbp) ]
  ]
  ; text ".LBB0_1" [
      Movq, [ Ind3 (Lit (-8L), Rbp); ~%Rax ]
    ; Movq, [ Ind2 Rax; ~%Rax ]
    ; Andq, [ ~$255; ~%Rax ]
    ; Cmpq, [ ~$0; ~%Rax ]
    ; J Eq, [ ~$$".LBB0_15" ]
    ; Movq, [ Ind3 (Lit (-8L), Rbp); ~%Rax ]
    ; Movq, [ Ind2 Rax; ~%Rax ]
    ; Andq, [ ~$255; ~%Rax ]
    ; Movq, [ ~%Rax; Ind3 (Lit (-32L), Rbp) ]
    ; Movq, [ ~$0; Ind3 (Lit (-40L), Rbp) ]
    ; Cmpq, [ ~$48; Ind3 (Lit (-32L), Rbp) ]
    ; J Lt, [ ~$$".LBB0_5" ]
    ; Cmpq, [ ~$57; Ind3 (Lit (-32L), Rbp) ]
    ; J Gt, [ ~$$".LBB0_5" ]
    ; Movq, [ Ind3 (Lit (-32L), Rbp); ~%Rax ]
    ; Subq, [ ~$48; ~%Rax ]
    ; Movq, [ ~%Rax; Ind3 (Lit (-40L), Rbp) ]
    ; Jmp, [ ~$$".LBB0_13" ]
  ]
  ; text ".LBB0_5" [
      Cmpq, [ ~$65; Ind3 (Lit (-32L), Rbp) ]
    ; J Lt, [ ~$$".LBB0_8" ]
    ; Cmpq, [ ~$90; Ind3 (Lit (-32L), Rbp) ]
    ; J Gt, [ ~$$".LBB0_8" ]
    ; Movq, [ Ind3 (Lit (-32L), Rbp); ~%Rax ]
    ; Subq, [ ~$65; ~%Rax ]
    ; Addq, [ ~$10; ~%Rax ]
    ; Movq, [ ~%Rax; Ind3 (Lit (-40L), Rbp) ]
    ; Jmp, [ ~$$".LBB0_12" ]
  ]
  ; text ".LBB0_8" [
      Cmpq, [ ~$97; Ind3 (Lit (-32L), Rbp) ]
    ; J Lt, [ ~$$".LBB0_11" ]
    ; Cmpq, [ ~$122; Ind3 (Lit (-32L), Rbp) ]
    ; J Gt, [ ~$$".LBB0_11" ]
    ; Movq, [ Ind3 (Lit (-32L), Rbp); ~%Rax ]
    ; Subq, [ ~$97; ~%Rax ]
    ; Addq, [ ~$10; ~%Rax ]
    ; Movq, [ ~%Rax; Ind3 (Lit (-40L), Rbp) ]
  ]
  ; text ".LBB0_11" [
      Jmp, [ ~$$".LBB0_12" ]
  ]
  ; text ".LBB0_12" [
      Jmp, [ ~$$".LBB0_13" ]
  ]
  ; text ".LBB0_13" [
      Movq, [ Ind3 (Lit (-24L), Rbp); ~%Rax ]
    ; Imulq, [ Ind3 (Lit (-16L), Rbp); ~%Rax ]
    ; Addq, [ Ind3 (Lit (-40L), Rbp); ~%Rax ]
    ; Movq, [ ~%Rax; Ind3 (Lit (-24L), Rbp) ]
    ; Movq, [ Ind3 (Lit (-8L), Rbp); ~%Rax ]
    ; Addq, [ ~$1; ~%Rax ]
    ; Movq, [ ~%Rax; Ind3 (Lit (-8L), Rbp) ]
    ; Jmp, [ ~$$".LBB0_1" ]
  ]
  ; text ".LBB0_15" [
      Movq, [ Ind3 (Lit (-24L), Rbp); ~%Rax ]
    ; Popq, [ ~%Rbp ]
    ; Retq, []
  ]
  ; gtext "main" [
      Pushq, [ ~%Rbp ]
    ; Movq, [ ~%Rsp; ~%Rbp ]
    ; Movq, [ ~$$".L.str"; ~%Rdi ]
    ; Movq, [ ~$16; ~%Rsi ]
    ; Callq, [ ~$$"_Z9parse_intPKcl" ]
    ; Popq, [ ~%Rbp ]
    ; Retq, []
  ]
  ; data ".L.str" [
    Asciz "ECE1"
  ]
]

let provided_tests : suite = provided_tests @ [
  Test ("Debug: End-to-end Parse_Int", [
    ("parse_int", Gradedtests.program_test parse_int 0xECE1L)
  ]);
]
