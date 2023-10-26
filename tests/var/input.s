	.globl main
main:
    pushq %rbp
    movq %rsp, %rbp
    subq $0, %rsp
    callq read_int
    movq %rax, %rdi
    callq print_int
    addq $0, %rsp
    popq %rbp
    retq 

