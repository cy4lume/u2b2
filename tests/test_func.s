
test_func.elf:     file format elf32-tradbigmips


Disassembly of section .init:

004004e4 <_init>:
  4004e4:	3c1c0002 	lui	gp,0x2
  4004e8:	279c7b2c 	addiu	gp,gp,31532
  4004ec:	0399e021 	addu	gp,gp,t9
  4004f0:	27bdffe0 	addiu	sp,sp,-32
  4004f4:	afbc0010 	sw	gp,16(sp)
  4004f8:	afbf001c 	sw	ra,28(sp)
  4004fc:	8f828020 	lw	v0,-32736(gp)
  400500:	10400004 	beqz	v0,400514 <_init+0x30>
  400504:	00000000 	nop
  400508:	8f998020 	lw	t9,-32736(gp)
  40050c:	0320f809 	jalr	t9
  400510:	00000000 	nop
  400514:	8fbf001c 	lw	ra,28(sp)
  400518:	03e00008 	jr	ra
  40051c:	27bd0020 	addiu	sp,sp,32

Disassembly of section .text:

00400520 <__start>:
  400520:	03e00025 	move	zero,ra
  400524:	04110001 	bal	40052c <__start+0xc>
  400528:	00000000 	nop
  40052c:	3c1c0002 	lui	gp,0x2
  400530:	279c7ae4 	addiu	gp,gp,31460
  400534:	039fe021 	addu	gp,gp,ra
  400538:	0000f825 	move	ra,zero
  40053c:	8f848018 	lw	a0,-32744(gp)
  400540:	8fa50000 	lw	a1,0(sp)
  400544:	27a60004 	addiu	a2,sp,4
  400548:	2401fff8 	li	at,-8
  40054c:	03a1e824 	and	sp,sp,at
  400550:	27bdffe0 	addiu	sp,sp,-32
  400554:	00003825 	move	a3,zero
  400558:	afa00010 	sw	zero,16(sp)
  40055c:	afa20014 	sw	v0,20(sp)
  400560:	afbd0018 	sw	sp,24(sp)
  400564:	8f99802c 	lw	t9,-32724(gp)
  400568:	0320f809 	jalr	t9
  40056c:	00000000 	nop

00400570 <hlt>:
  400570:	1000ffff 	b	400570 <hlt>
  400574:	00000000 	nop
	...

00400580 <deregister_tm_clones>:
  400580:	3c040042 	lui	a0,0x42
  400584:	3c020042 	lui	v0,0x42
  400588:	24840014 	addiu	a0,a0,20
  40058c:	24420014 	addiu	v0,v0,20
  400590:	10440007 	beq	v0,a0,4005b0 <deregister_tm_clones+0x30>
  400594:	3c1c0043 	lui	gp,0x43
  400598:	279c8010 	addiu	gp,gp,-32752
  40059c:	8f998028 	lw	t9,-32728(gp)
  4005a0:	13200003 	beqz	t9,4005b0 <deregister_tm_clones+0x30>
  4005a4:	00000000 	nop
  4005a8:	03200008 	jr	t9
  4005ac:	00000000 	nop
  4005b0:	03e00008 	jr	ra
  4005b4:	00000000 	nop

004005b8 <register_tm_clones>:
  4005b8:	3c040042 	lui	a0,0x42
  4005bc:	3c020042 	lui	v0,0x42
  4005c0:	24840014 	addiu	a0,a0,20
  4005c4:	24450014 	addiu	a1,v0,20
  4005c8:	00a42823 	subu	a1,a1,a0
  4005cc:	00051083 	sra	v0,a1,0x2
  4005d0:	00052fc2 	srl	a1,a1,0x1f
  4005d4:	00a22821 	addu	a1,a1,v0
  4005d8:	00052843 	sra	a1,a1,0x1
  4005dc:	10a00007 	beqz	a1,4005fc <register_tm_clones+0x44>
  4005e0:	3c1c0043 	lui	gp,0x43
  4005e4:	279c8010 	addiu	gp,gp,-32752
  4005e8:	8f99801c 	lw	t9,-32740(gp)
  4005ec:	13200003 	beqz	t9,4005fc <register_tm_clones+0x44>
  4005f0:	00000000 	nop
  4005f4:	03200008 	jr	t9
  4005f8:	00000000 	nop
  4005fc:	03e00008 	jr	ra
  400600:	00000000 	nop

00400604 <__do_global_dtors_aux>:
  400604:	27bdffe0 	addiu	sp,sp,-32
  400608:	afb00018 	sw	s0,24(sp)
  40060c:	3c100042 	lui	s0,0x42
  400610:	afbf001c 	sw	ra,28(sp)
  400614:	92020050 	lbu	v0,80(s0)
  400618:	14400006 	bnez	v0,400634 <__do_global_dtors_aux+0x30>
  40061c:	8fbf001c 	lw	ra,28(sp)
  400620:	0c100160 	jal	400580 <deregister_tm_clones>
  400624:	00000000 	nop
  400628:	24020001 	li	v0,1
  40062c:	a2020050 	sb	v0,80(s0)
  400630:	8fbf001c 	lw	ra,28(sp)
  400634:	8fb00018 	lw	s0,24(sp)
  400638:	03e00008 	jr	ra
  40063c:	27bd0020 	addiu	sp,sp,32

00400640 <frame_dummy>:
  400640:	0810016e 	j	4005b8 <register_tm_clones>
  400644:	00000000 	nop
	...

00400650 <inc>:
  400650:	27bdfff8 	addiu	sp,sp,-8
  400654:	afbe0004 	sw	s8,4(sp)
  400658:	03a0f025 	move	s8,sp
  40065c:	afc40008 	sw	a0,8(s8)
  400660:	8fc20008 	lw	v0,8(s8)
  400664:	24420001 	addiu	v0,v0,1
  400668:	03c0e825 	move	sp,s8
  40066c:	8fbe0004 	lw	s8,4(sp)
  400670:	27bd0008 	addiu	sp,sp,8
  400674:	03e00008 	jr	ra
  400678:	00000000 	nop

0040067c <func1>:
  40067c:	27bdffe0 	addiu	sp,sp,-32
  400680:	afbf001c 	sw	ra,28(sp)
  400684:	afbe0018 	sw	s8,24(sp)
  400688:	03a0f025 	move	s8,sp
  40068c:	afc40020 	sw	a0,32(s8)
  400690:	afc50024 	sw	a1,36(s8)
  400694:	8fc30020 	lw	v1,32(s8)
  400698:	2402002a 	li	v0,42
  40069c:	14620004 	bne	v1,v0,4006b0 <func1+0x34>
  4006a0:	00000000 	nop
  4006a4:	00001025 	move	v0,zero
  4006a8:	1000000c 	b	4006dc <func1+0x60>
  4006ac:	00000000 	nop
  4006b0:	8fc40020 	lw	a0,32(s8)
  4006b4:	0c100194 	jal	400650 <inc>
  4006b8:	00000000 	nop
  4006bc:	00401825 	move	v1,v0
  4006c0:	8fc20020 	lw	v0,32(s8)
  4006c4:	14430004 	bne	v0,v1,4006d8 <func1+0x5c>
  4006c8:	00000000 	nop
  4006cc:	24024242 	li	v0,16962
  4006d0:	10000002 	b	4006dc <func1+0x60>
  4006d4:	00000000 	nop
  4006d8:	24020001 	li	v0,1
  4006dc:	03c0e825 	move	sp,s8
  4006e0:	8fbf001c 	lw	ra,28(sp)
  4006e4:	8fbe0018 	lw	s8,24(sp)
  4006e8:	27bd0020 	addiu	sp,sp,32
  4006ec:	03e00008 	jr	ra
  4006f0:	00000000 	nop

004006f4 <dead_func>:
  4006f4:	27bdfff8 	addiu	sp,sp,-8
  4006f8:	afbe0004 	sw	s8,4(sp)
  4006fc:	03a0f025 	move	s8,sp
  400700:	afc40008 	sw	a0,8(s8)
  400704:	afc5000c 	sw	a1,12(s8)
  400708:	8fc30008 	lw	v1,8(s8)
  40070c:	2402002a 	li	v0,42
  400710:	14620004 	bne	v1,v0,400724 <dead_func+0x30>
  400714:	00000000 	nop
  400718:	00001025 	move	v0,zero
  40071c:	10000002 	b	400728 <dead_func+0x34>
  400720:	00000000 	nop
  400724:	24020001 	li	v0,1
  400728:	03c0e825 	move	sp,s8
  40072c:	8fbe0004 	lw	s8,4(sp)
  400730:	27bd0008 	addiu	sp,sp,8
  400734:	03e00008 	jr	ra
  400738:	00000000 	nop

0040073c <main>:
  40073c:	27bdffd8 	addiu	sp,sp,-40
  400740:	afbf0024 	sw	ra,36(sp)
  400744:	afbe0020 	sw	s8,32(sp)
  400748:	03a0f025 	move	s8,sp
  40074c:	3c1c0043 	lui	gp,0x43
  400750:	279c8010 	addiu	gp,gp,-32752
  400754:	afbc0010 	sw	gp,16(sp)
  400758:	afc40028 	sw	a0,40(s8)
  40075c:	afc5002c 	sw	a1,44(s8)
  400760:	afc60030 	sw	a2,48(s8)
  400764:	8fc30028 	lw	v1,40(s8)
  400768:	24020003 	li	v0,3
  40076c:	1062000b 	beq	v1,v0,40079c <main+0x60>
  400770:	00000000 	nop
  400774:	3c020040 	lui	v0,0x40
  400778:	24440840 	addiu	a0,v0,2112
  40077c:	8f828024 	lw	v0,-32732(gp)
  400780:	0040c825 	move	t9,v0
  400784:	0320f809 	jalr	t9
  400788:	00000000 	nop
  40078c:	8fdc0010 	lw	gp,16(s8)
  400790:	2402ffff 	li	v0,-1
  400794:	10000006 	b	4007b0 <main+0x74>
  400798:	00000000 	nop
  40079c:	8fc5001c 	lw	a1,28(s8)
  4007a0:	8fc40018 	lw	a0,24(s8)
  4007a4:	0c10019f 	jal	40067c <func1>
  4007a8:	00000000 	nop
  4007ac:	8fdc0010 	lw	gp,16(s8)
  4007b0:	03c0e825 	move	sp,s8
  4007b4:	8fbf0024 	lw	ra,36(sp)
  4007b8:	8fbe0020 	lw	s8,32(sp)
  4007bc:	27bd0028 	addiu	sp,sp,40
  4007c0:	03e00008 	jr	ra
  4007c4:	00000000 	nop
	...

Disassembly of section .MIPS.stubs:

004007d0 <_MIPS_STUBS_>:
  4007d0:	8f998010 	lw	t9,-32752(gp)
  4007d4:	03e07825 	move	t7,ra
  4007d8:	0320f809 	jalr	t9
  4007dc:	24180009 	li	t8,9
  4007e0:	8f998010 	lw	t9,-32752(gp)
  4007e4:	03e07825 	move	t7,ra
  4007e8:	0320f809 	jalr	t9
  4007ec:	24180007 	li	t8,7
	...

Disassembly of section .fini:

00400800 <_fini>:
  400800:	3c1c0002 	lui	gp,0x2
  400804:	279c7810 	addiu	gp,gp,30736
  400808:	0399e021 	addu	gp,gp,t9
  40080c:	27bdffe0 	addiu	sp,sp,-32
  400810:	afbc0010 	sw	gp,16(sp)
  400814:	afbf001c 	sw	ra,28(sp)
  400818:	8fbf001c 	lw	ra,28(sp)
  40081c:	03e00008 	jr	ra
  400820:	27bd0020 	addiu	sp,sp,32
