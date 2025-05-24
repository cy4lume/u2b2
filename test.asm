        .section .data
array:  .word 10, 20, 30, 40, 50
length: .word 1

        .section .text
        .globl __start

__start:
        li $sp, 0x80000000

        la $t0, array
        lw $t1, length

        li $t2, 0        # sum
        li $t3, 0        # i

loop:
        beq $t3, $t1, done
        sll $t4, $t3, 2
        add $t5, $t0, $t4
        lw $t6, 0($t5)
        add $t2, $t2, $t6
        addi $t3, $t3, 1
        j loop

done:
        # exit(sum)
        move $a0, $t2         # exit code in $a0
        li   $v0, 4001        # syscall number for exit in Linux MIPS
        syscall
