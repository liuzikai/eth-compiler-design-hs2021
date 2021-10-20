open Assert
open X86
open Simulator
open Asm

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
    Asciz "ECEB"
  ]
]

let provided_tests : suite = [
  Test ("Debug: End-to-end Tests", [
    ("parse_int", Gradedtests.program_test parse_int 0xECEBL)
  ]);
]