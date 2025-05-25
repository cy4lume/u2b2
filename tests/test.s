        .text
        .globl  exploit
        .ent   exploit
exploit:
        addiu   $sp, $sp, -8
        sw      $ra, 4($sp)


loop:
        # while (x < y)
        slt     $t0, $a0, $a1      # $t0 = (x < y) ? 1 : 0
        beq     $t0, $zero, done
        nop

        # if (x == 42) _exit(y);
        li      $t0, 42
        beq     $a0, $t0, exit_y
        nop

        # x += y
        addu    $a0, $a0, $a1

        j       loop
        nop

exit_y:
        # _exit(y);
        move    $a0, $a1
        li      $v0, 4001          # __NR_exit (Linux MIPS BE)
        syscall                    

done:
        # _exit(0);
        li      $a0, 0             # status = 0
        li      $v0, 4001          # __NR_exit
        syscall                    

        lw      $ra, 4($sp)
        addiu   $sp, $sp, 8
        jr      $ra
        nop
        .end   exploit
