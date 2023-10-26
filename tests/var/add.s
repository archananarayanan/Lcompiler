	.globl main
main:
    pushq %rbp
    movq %rsp, %rbp
    subq $0, %rsp
    movq $1, %rdx
    movq $42, %rsi
    addq $7, %rdx
    movq %rdx, %rcx
    addq %rsi, %rdx
    negq %rcx
    addq %rcx, %rdx
    movq %rdx, %rdi
    callq print_int
    addq $0, %rsp
    popq %rbp
    retq 

