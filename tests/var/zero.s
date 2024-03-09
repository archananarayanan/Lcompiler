	.align 16
sum:
    pushq %rbp
    movq %rsp, %rbp
    pushq %rbx
    subq $8, %rsp
    movq $0, 0(%r15)
    addq $0, %r15
    jmp sum_start

	.align 16
block.8:
    movq $0, %rax
    jmp sum_conclusion

	.align 16
block.9:
    leaq sum(%rip), %rcx
    movq %rbx, %rdi
    subq $1, %rdi
    callq *%rcx
    movq %rax, %rcx
    movq %rbx, %rax
    addq %rcx, %rax
    jmp sum_conclusion

	.align 16
sum_start:
    movq %rdi, %rbx
    cmpq $0, %rbx
    je block.8
    jmp block.9

	.align 16
sum_conclusion:
    subq $0, %r15
    addq $8, %rsp
    popq %rbx
    popq %rbp
    retq 

	.globl main
	.align 16
main:
    pushq %rbp
    movq %rsp, %rbp
    subq $0, %rsp
    movq $65536, %rdi
    movq $16, %rsi
    callq initialize
    movq rootstack_begin(%rip), %r15
    movq $0, 0(%r15)
    addq $0, %r15
    jmp main_start

	.align 16
main_start:
    leaq sum(%rip), %rcx
    movq $3, %rdi
    callq *%rcx
    movq %rax, %rdi
    addq $36, %rdi
    callq print_int
    movq $0, %rax
    jmp main_conclusion

	.align 16
main_conclusion:
    subq $0, %r15
    addq $0, %rsp
    popq %rbp
    retq 


