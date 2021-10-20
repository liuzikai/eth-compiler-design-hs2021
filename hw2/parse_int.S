_Z9parse_intPKcl:                       # @_Z9parse_intPKcl
        pushq   %rbp
        movq    %rsp, %rbp
        movq    %rdi, -8(%rbp)
        movq    %rsi, -16(%rbp)
        movq    $0, -24(%rbp)
.LBB0_1:                                # =>This Inner Loop Header: Depth=1
        movq    -8(%rbp), %rax
        movq    (%rax), %rax
        andq    $255, %rax
        cmpq    $0, %rax
        je      .LBB0_15
        movq    -8(%rbp), %rax
        movq    (%rax), %rax
        andq    $255, %rax
        movq    %rax, -32(%rbp)
        movq    $0, -40(%rbp)
        cmpq    $48, -32(%rbp)
        jl      .LBB0_5
        cmpq    $57, -32(%rbp)
        jg      .LBB0_5
        movq    -32(%rbp), %rax
        subq    $48, %rax
        movq    %rax, -40(%rbp)
        jmp     .LBB0_13
.LBB0_5:                                #   in Loop: Header=BB0_1 Depth=1
        cmpq    $65, -32(%rbp)
        jl      .LBB0_8
        cmpq    $90, -32(%rbp)
        jg      .LBB0_8
        movq    -32(%rbp), %rax
        subq    $65, %rax
        addq    $10, %rax
        movq    %rax, -40(%rbp)
        jmp     .LBB0_12
.LBB0_8:                                #   in Loop: Header=BB0_1 Depth=1
        cmpq    $97, -32(%rbp)
        jl      .LBB0_11
        cmpq    $122, -32(%rbp)
        jg      .LBB0_11
        movq    -32(%rbp), %rax
        subq    $97, %rax
        addq    $10, %rax
        movq    %rax, -40(%rbp)
.LBB0_11:                               #   in Loop: Header=BB0_1 Depth=1
        jmp     .LBB0_12
.LBB0_12:                               #   in Loop: Header=BB0_1 Depth=1
        jmp     .LBB0_13
.LBB0_13:                               #   in Loop: Header=BB0_1 Depth=1
        movq    -24(%rbp), %rax
        imulq   -16(%rbp), %rax
        addq    -40(%rbp), %rax
        movq    %rax, -24(%rbp)
        movq    -8(%rbp), %rax
        addq    $1, %rax
        movq    %rax, -8(%rbp)
        jmp     .LBB0_1
.LBB0_15:
        movq    -24(%rbp), %rax
        popq    %rbp
        retq
.globl _main
_main:                                   # @main
        pushq   %rbp
        movq    %rsp, %rbp
        subq    $16, %rsp
        movl    $0, -4(%rbp)
        movabsq $.L.str, %rdi
        movl    $16, %esi
        callq   _Z9parse_intPKcl
        movl    %eax, -8(%rbp)
        movl    -8(%rbp), %eax
        addq    $16, %rsp
        popq    %rbp
        retq
.L.str:
        .asciz  "ECEB"