open Assert
open X86
open Simulator
open Asm

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
