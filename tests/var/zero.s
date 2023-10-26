	.globl main
	.align 16
main:
    pushq %rbp
    movq %rsp, %rbp
    pushq %rbx
    subq $8, %rsp
    movq $65536, %rdi
    movq $16, %rsi
    callq initialize
    movq rootstack_begin(\%rip), %r15
    movq $0, 0(%r15)
    addq $0, %r15
    jmp start

	.align 16
block.2:
    movq %rbx, %rdi
    callq print_int
    movq $0, %rax
    jmp conclusion

	.align 16
block.4:
    addq $42, %rbx
    jmp block.3

	.align 16
block.5:
    jmp block.2

	.align 16
block.6:
    jmp block.4

	.align 16
block.7:
    jmp block.5

	.align 16
block.3:
    callq read_int
    movq %rax, %rcx
    cmpq $5, %rcx
    je block.6
    jmp block.7

	.align 16
start:
    movq $0, %rbx
    jmp block.3

	.align 16
conclusion:
    subq $0, %r15
    addq $8, %rsp
    popq %rbx
    popq %rbp
    retq 


