
test_func2.elf:     file format elf32-tradbigmips


Disassembly of section .interp:

00400194 <.interp>:
  400194:	2f6c6962 	sltiu	t4,k1,26978
  400198:	2f6c642e 	sltiu	t4,k1,25646
  40019c:	736f2e31 	.word	0x736f2e31
	...

Disassembly of section .MIPS.abiflags:

004001a8 <.MIPS.abiflags>:
  4001a8:	00002002 	srl	a0,zero,0x0
  4001ac:	01010005 	lsa	zero,t0,at,0x1
	...

Disassembly of section .reginfo:

004001c0 <.reginfo>:
  4001c0:	b20000f6 	.word	0xb20000f6
	...
  4001d4:	00428010 	.word	0x428010

Disassembly of section .note.gnu.build-id:

004001d8 <.note.gnu.build-id>:
  4001d8:	00000004 	sllv	zero,zero,zero
  4001dc:	00000014 	.word	0x14
  4001e0:	00000003 	sra	zero,zero,0x0
  4001e4:	474e5500 	bz.w	$w14,4155e8 <__FRAME_END__+0x14dc8>
  4001e8:	59520a3c 	.word	0x59520a3c
  4001ec:	e9fcdb60 	swc2	$28,-9376(t7)
  4001f0:	90b65429 	lbu	s6,21545(a1)
  4001f4:	3c22aa5f 	.word	0x3c22aa5f
  4001f8:	f00122a2 	.word	0xf00122a2

Disassembly of section .note.ABI-tag:

004001fc <__abi_tag>:
  4001fc:	00000004 	sllv	zero,zero,zero
  400200:	00000010 	mfhi	zero
  400204:	00000001 	movf	zero,zero,$fcc0
  400208:	474e5500 	bz.w	$w14,41560c <__FRAME_END__+0x14dec>
  40020c:	00000000 	nop
  400210:	00000003 	sra	zero,zero,0x0
  400214:	00000002 	srl	zero,zero,0x0
  400218:	00000000 	nop

Disassembly of section .dynamic:

0040021c <_DYNAMIC>:
  40021c:	00000001 	movf	zero,zero,$fcc0
  400220:	00000049 	.word	0x49
  400224:	0000000c 	syscall
  400228:	00400500 	.word	0x400500
  40022c:	0000000d 	break
  400230:	004007b0 	tge	v0,zero,0x1e
  400234:	00000019 	multu	zero,zero
  400238:	0041fff8 	.word	0x41fff8
  40023c:	0000001b 	divu	zero,zero,zero
  400240:	00000004 	sllv	zero,zero,zero
  400244:	0000001a 	div	zero,zero,zero
  400248:	0041fffc 	.word	0x41fffc
  40024c:	0000001c 	.word	0x1c
  400250:	00000004 	sllv	zero,zero,zero
  400254:	00000004 	sllv	zero,zero,zero
  400258:	0040031c 	.word	0x40031c
  40025c:	00000005 	lsa	zero,zero,zero,0x1
  400260:	0040040c 	syscall	0x10010
  400264:	00000006 	srlv	zero,zero,zero
  400268:	0040035c 	.word	0x40035c
  40026c:	0000000a 	movz	zero,zero,zero
  400270:	000000ad 	.word	0xad
  400274:	0000000b 	movn	zero,zero,zero
  400278:	00000010 	mfhi	zero
  40027c:	70000016 	udi6	zero,zero,zero,0x0
  400280:	00420010 	.word	0x420010
  400284:	70000035 	.word	0x70000035
  400288:	0001fd8c 	syscall	0x7f6
  40028c:	00000015 	.word	0x15
  400290:	00000000 	nop
  400294:	00000003 	sra	zero,zero,0x0
  400298:	00420020 	add	zero,v0,v0
  40029c:	70000001 	maddu	zero,zero
  4002a0:	00000001 	movf	zero,zero,$fcc0
  4002a4:	70000005 	msubu	zero,zero
  4002a8:	00000002 	srl	zero,zero,0x0
  4002ac:	70000006 	.word	0x70000006
  4002b0:	00400000 	.word	0x400000
  4002b4:	7000000a 	.word	0x7000000a
  4002b8:	00000003 	sra	zero,zero,0x0
  4002bc:	70000011 	udi1	zero,zero,zero,0x0
  4002c0:	0000000b 	movn	zero,zero,zero
  4002c4:	70000012 	udi2	zero,zero,zero,0x0
  4002c8:	0000001d 	.word	0x1d
  4002cc:	70000013 	udi3	zero,zero,zero,0x0
  4002d0:	00000005 	lsa	zero,zero,zero,0x1
  4002d4:	6ffffffe 	.word	0x6ffffffe
  4002d8:	004004d0 	.word	0x4004d0
  4002dc:	6fffffff 	.word	0x6fffffff
  4002e0:	00000001 	movf	zero,zero,$fcc0
  4002e4:	6ffffff0 	.word	0x6ffffff0
  4002e8:	004004ba 	.word	0x4004ba
	...

Disassembly of section .hash:

0040031c <.hash>:
  40031c:	00000003 	sra	zero,zero,0x0
  400320:	0000000b 	movn	zero,zero,zero
  400324:	00000006 	srlv	zero,zero,zero
  400328:	00000005 	lsa	zero,zero,zero,0x1
  40032c:	00000003 	sra	zero,zero,0x0
  400330:	00000000 	nop
  400334:	00000009 	jalr	zero,zero
  400338:	0000000a 	movz	zero,zero,zero
  40033c:	00000002 	srl	zero,zero,0x0
  400340:	00000007 	srav	zero,zero,zero
  400344:	00000004 	sllv	zero,zero,zero
  400348:	00000000 	nop
  40034c:	00000008 	jr	zero
  400350:	00000001 	movf	zero,zero,$fcc0
	...

Disassembly of section .dynsym:

0040035c <.dynsym>:
	...
  40036c:	00000013 	mtlo	zero
  400370:	00000001 	movf	zero,zero,$fcc0
  400374:	00000000 	nop
  400378:	1300fff1 	beqz	t8,400340 <_DYNAMIC+0x124>
  40037c:	0000003a 	.word	0x3a
  400380:	004007e0 	.word	0x4007e0
  400384:	00000004 	sllv	zero,zero,zero
  400388:	11000010 	beqz	t0,4003cc <_DYNAMIC+0x1b0>
  40038c:	00000024 	and	zero,zero,zero
  400390:	00420010 	.word	0x420010
  400394:	00000000 	nop
  400398:	11000015 	beqz	t0,4003f0 <_DYNAMIC+0x1d4>
  40039c:	0000000e 	.word	0xe
  4003a0:	00400670 	tge	v0,zero,0x19
  4003a4:	000000f4 	teq	zero,zero,0x3
  4003a8:	1200000d 	beqz	s0,4003e0 <_DYNAMIC+0x1c4>
  4003ac:	0000007e 	.word	0x7e
	...
  4003b8:	20000000 	addi	zero,zero,0
  4003bc:	00000053 	mtlhx	zero
	...
  4003c8:	22000000 	addi	zero,s0,0
  4003cc:	0000002e 	.word	0x2e
  4003d0:	00400790 	.word	0x400790
  4003d4:	00000000 	nop
  4003d8:	12000000 	beqz	s0,4003dc <_DYNAMIC+0x1c0>
  4003dc:	00000062 	.word	0x62
	...
  4003e8:	20000000 	addi	zero,zero,0
  4003ec:	00000001 	movf	zero,zero,$fcc0
  4003f0:	00400780 	.word	0x400780
  4003f4:	00000000 	nop
  4003f8:	12000000 	beqz	s0,4003fc <_DYNAMIC+0x1e0>
  4003fc:	00000033 	tltu	zero,zero
  400400:	00400770 	tge	v0,zero,0x1d
  400404:	00000000 	nop
  400408:	12000000 	beqz	s0,40040c <_DYNAMIC+0x1f0>

Disassembly of section .dynstr:

0040040c <.dynstr>:
  40040c:	005f5f6c 	.word	0x5f5f6c
  400410:	6962635f 	.word	0x6962635f
  400414:	73746172 	.word	0x73746172
  400418:	745f6d61 	jalx	17db584 <_gp+0x13b3574>
  40041c:	696e005f 	.word	0x696e005f
  400420:	44594e41 	.word	0x44594e41
  400424:	4d49435f 	.word	0x4d49435f
  400428:	4c494e4b 	.word	0x4c494e4b
  40042c:	494e4700 	.word	0x494e4700
  400430:	5f5f524c 	.word	0x5f5f524c
  400434:	445f4d41 	.word	0x445f4d41
  400438:	50007075 	beqzl	zero,41c610 <__FRAME_END__+0x1bdf0>
  40043c:	74730073 	jalx	1cc01cc <_gp+0x18981bc>
  400440:	7472636d 	jalx	1c98db4 <_gp+0x1870da4>
  400444:	70005f49 	.word	0x70005f49
  400448:	4f5f7374 	.word	0x4f5f7374
  40044c:	64696e5f 	.word	0x64696e5f
  400450:	75736564 	jalx	5cd9590 <_gp+0x58b1580>
  400454:	006c6962 	.word	0x6c6962
  400458:	632e736f 	.word	0x632e736f
  40045c:	2e36005f 	sltiu	s6,s1,95
  400460:	5f676d6f 	.word	0x5f676d6f
  400464:	6e5f7374 	.word	0x6e5f7374
  400468:	6172745f 	.word	0x6172745f
  40046c:	5f005f49 	bgtzl	t8,418194 <__FRAME_END__+0x17974>
  400470:	544d5f64 	bnel	v0,t5,418204 <__FRAME_END__+0x179e4>
  400474:	65726567 	.word	0x65726567
  400478:	69737465 	.word	0x69737465
  40047c:	72544d43 	.word	0x72544d43
  400480:	6c6f6e65 	.word	0x6c6f6e65
  400484:	5461626c 	bnel	v1,at,418e38 <__FRAME_END__+0x18618>
  400488:	65005f49 	.word	0x65005f49
  40048c:	544d5f72 	bnel	v0,t5,418258 <__FRAME_END__+0x17a38>
  400490:	65676973 	.word	0x65676973
  400494:	74657254 	jalx	195c950 <_gp+0x1534940>
  400498:	4d436c6f 	.word	0x4d436c6f
  40049c:	6e655461 	.word	0x6e655461
  4004a0:	626c6500 	.word	0x626c6500
  4004a4:	474c4942 	bz.w	$w12,4129b0 <__FRAME_END__+0x12190>
  4004a8:	435f322e 	c0	0x15f322e
  4004ac:	33340047 	andi	s4,t9,0x47
  4004b0:	4c494243 	.word	0x4c494243
  4004b4:	5f322e30 	.word	0x5f322e30
	...

Disassembly of section .gnu.version:

004004ba <.gnu.version>:
  4004ba:	00000001 	movf	zero,zero,$fcc0
  4004be:	00010001 	movt	zero,zero,$fcc0
  4004c2:	00010001 	movt	zero,zero,$fcc0
  4004c6:	00010002 	srl	zero,at,0x0
  4004ca:	00010003 	sra	zero,at,0x0
  4004ce:	Address 0x4004ce is out of bounds.


Disassembly of section .gnu.version_r:

004004d0 <.gnu.version_r>:
  4004d0:	00010002 	srl	zero,at,0x0
  4004d4:	00000049 	.word	0x49
  4004d8:	00000010 	mfhi	zero
  4004dc:	00000000 	nop
  4004e0:	069691b4 	.word	0x69691b4
  4004e4:	00000003 	sra	zero,zero,0x0
  4004e8:	00000098 	.word	0x98
  4004ec:	00000010 	mfhi	zero
  4004f0:	0d696910 	jal	5a5a440 <_gp+0x5632430>
  4004f4:	00000002 	srl	zero,zero,0x0
  4004f8:	000000a3 	.word	0xa3
  4004fc:	00000000 	nop

Disassembly of section .init:

00400500 <_init>:
  400500:	3c1c0002 	lui	gp,0x2
  400504:	279c7b10 	addiu	gp,gp,31504
  400508:	0399e021 	addu	gp,gp,t9
  40050c:	27bdffe0 	addiu	sp,sp,-32
  400510:	afbc0010 	sw	gp,16(sp)
  400514:	afbf001c 	sw	ra,28(sp)
  400518:	8f828020 	lw	v0,-32736(gp)
  40051c:	10400004 	beqz	v0,400530 <_init+0x30>
  400520:	00000000 	nop
  400524:	8f998020 	lw	t9,-32736(gp)
  400528:	0320f809 	jalr	t9
  40052c:	00000000 	nop
  400530:	8fbf001c 	lw	ra,28(sp)
  400534:	03e00008 	jr	ra
  400538:	27bd0020 	addiu	sp,sp,32

Disassembly of section .text:

00400540 <__start>:
  400540:	03e00025 	move	zero,ra
  400544:	04110001 	bal	40054c <__start+0xc>
  400548:	00000000 	nop
  40054c:	3c1c0002 	lui	gp,0x2
  400550:	279c7ac4 	addiu	gp,gp,31428
  400554:	039fe021 	addu	gp,gp,ra
  400558:	0000f825 	move	ra,zero
  40055c:	8f848018 	lw	a0,-32744(gp)
  400560:	8fa50000 	lw	a1,0(sp)
  400564:	27a60004 	addiu	a2,sp,4
  400568:	2401fff8 	li	at,-8
  40056c:	03a1e824 	and	sp,sp,at
  400570:	27bdffe0 	addiu	sp,sp,-32
  400574:	00003825 	move	a3,zero
  400578:	afa00010 	sw	zero,16(sp)
  40057c:	afa20014 	sw	v0,20(sp)
  400580:	afbd0018 	sw	sp,24(sp)
  400584:	8f99802c 	lw	t9,-32724(gp)
  400588:	0320f809 	jalr	t9
  40058c:	00000000 	nop

00400590 <hlt>:
  400590:	1000ffff 	b	400590 <hlt>
  400594:	00000000 	nop
	...

004005a0 <deregister_tm_clones>:
  4005a0:	3c040042 	lui	a0,0x42
  4005a4:	3c020042 	lui	v0,0x42
  4005a8:	24840014 	addiu	a0,a0,20
  4005ac:	24420014 	addiu	v0,v0,20
  4005b0:	10440007 	beq	v0,a0,4005d0 <deregister_tm_clones+0x30>
  4005b4:	3c1c0043 	lui	gp,0x43
  4005b8:	279c8010 	addiu	gp,gp,-32752
  4005bc:	8f998028 	lw	t9,-32728(gp)
  4005c0:	13200003 	beqz	t9,4005d0 <deregister_tm_clones+0x30>
  4005c4:	00000000 	nop
  4005c8:	03200008 	jr	t9
  4005cc:	00000000 	nop
  4005d0:	03e00008 	jr	ra
  4005d4:	00000000 	nop

004005d8 <register_tm_clones>:
  4005d8:	3c040042 	lui	a0,0x42
  4005dc:	3c020042 	lui	v0,0x42
  4005e0:	24840014 	addiu	a0,a0,20
  4005e4:	24450014 	addiu	a1,v0,20
  4005e8:	00a42823 	subu	a1,a1,a0
  4005ec:	00051083 	sra	v0,a1,0x2
  4005f0:	00052fc2 	srl	a1,a1,0x1f
  4005f4:	00a22821 	addu	a1,a1,v0
  4005f8:	00052843 	sra	a1,a1,0x1
  4005fc:	10a00007 	beqz	a1,40061c <register_tm_clones+0x44>
  400600:	3c1c0043 	lui	gp,0x43
  400604:	279c8010 	addiu	gp,gp,-32752
  400608:	8f99801c 	lw	t9,-32740(gp)
  40060c:	13200003 	beqz	t9,40061c <register_tm_clones+0x44>
  400610:	00000000 	nop
  400614:	03200008 	jr	t9
  400618:	00000000 	nop
  40061c:	03e00008 	jr	ra
  400620:	00000000 	nop

00400624 <__do_global_dtors_aux>:
  400624:	27bdffe0 	addiu	sp,sp,-32
  400628:	afb00018 	sw	s0,24(sp)
  40062c:	3c100042 	lui	s0,0x42
  400630:	afbf001c 	sw	ra,28(sp)
  400634:	92020050 	lbu	v0,80(s0)
  400638:	14400006 	bnez	v0,400654 <__do_global_dtors_aux+0x30>
  40063c:	8fbf001c 	lw	ra,28(sp)
  400640:	0c100168 	jal	4005a0 <deregister_tm_clones>
  400644:	00000000 	nop
  400648:	24020001 	li	v0,1
  40064c:	a2020050 	sb	v0,80(s0)
  400650:	8fbf001c 	lw	ra,28(sp)
  400654:	8fb00018 	lw	s0,24(sp)
  400658:	03e00008 	jr	ra
  40065c:	27bd0020 	addiu	sp,sp,32

00400660 <frame_dummy>:
  400660:	08100176 	j	4005d8 <register_tm_clones>
  400664:	00000000 	nop
	...

00400670 <main>:
  400670:	27bdffe0 	addiu	sp,sp,-32
  400674:	afbf001c 	sw	ra,28(sp)
  400678:	afbe0018 	sw	s8,24(sp)
  40067c:	03a0f025 	move	s8,sp
  400680:	3c1c0043 	lui	gp,0x43
  400684:	279c8010 	addiu	gp,gp,-32752
  400688:	afbc0010 	sw	gp,16(sp)
  40068c:	afc40020 	sw	a0,32(s8)
  400690:	afc50024 	sw	a1,36(s8)
  400694:	afc60028 	sw	a2,40(s8)
  400698:	8fc30020 	lw	v1,32(s8)
  40069c:	24020002 	li	v0,2
  4006a0:	1062000b 	beq	v1,v0,4006d0 <main+0x60>
  4006a4:	00000000 	nop
  4006a8:	3c020040 	lui	v0,0x40
  4006ac:	244407f0 	addiu	a0,v0,2032
  4006b0:	8f828024 	lw	v0,-32732(gp)
  4006b4:	0040c825 	move	t9,v0
  4006b8:	0320f809 	jalr	t9
  4006bc:	00000000 	nop
  4006c0:	8fdc0010 	lw	gp,16(s8)
  4006c4:	2402ffff 	li	v0,-1
  4006c8:	10000020 	b	40074c <main+0xdc>
  4006cc:	00000000 	nop
  4006d0:	8fc20024 	lw	v0,36(s8)
  4006d4:	24420004 	addiu	v0,v0,4
  4006d8:	8c430000 	lw	v1,0(v0)
  4006dc:	3c020040 	lui	v0,0x40
  4006e0:	244507fc 	addiu	a1,v0,2044
  4006e4:	00602025 	move	a0,v1
  4006e8:	8f828030 	lw	v0,-32720(gp)
  4006ec:	0040c825 	move	t9,v0
  4006f0:	0320f809 	jalr	t9
  4006f4:	00000000 	nop
  4006f8:	8fdc0010 	lw	gp,16(s8)
  4006fc:	1440000b 	bnez	v0,40072c <main+0xbc>
  400700:	00000000 	nop
  400704:	3c020040 	lui	v0,0x40
  400708:	24440804 	addiu	a0,v0,2052
  40070c:	8f828024 	lw	v0,-32732(gp)
  400710:	0040c825 	move	t9,v0
  400714:	0320f809 	jalr	t9
  400718:	00000000 	nop
  40071c:	8fdc0010 	lw	gp,16(s8)
  400720:	00001025 	move	v0,zero
  400724:	10000009 	b	40074c <main+0xdc>
  400728:	00000000 	nop
  40072c:	3c020040 	lui	v0,0x40
  400730:	24440810 	addiu	a0,v0,2064
  400734:	8f828024 	lw	v0,-32732(gp)
  400738:	0040c825 	move	t9,v0
  40073c:	0320f809 	jalr	t9
  400740:	00000000 	nop
  400744:	8fdc0010 	lw	gp,16(s8)
  400748:	2402fffe 	li	v0,-2
  40074c:	03c0e825 	move	sp,s8
  400750:	8fbf001c 	lw	ra,28(sp)
  400754:	8fbe0018 	lw	s8,24(sp)
  400758:	27bd0020 	addiu	sp,sp,32
  40075c:	03e00008 	jr	ra
  400760:	00000000 	nop
	...

Disassembly of section .MIPS.stubs:

00400770 <_MIPS_STUBS_>:
  400770:	8f998010 	lw	t9,-32752(gp)
  400774:	03e07825 	move	t7,ra
  400778:	0320f809 	jalr	t9
  40077c:	2418000a 	li	t8,10
  400780:	8f998010 	lw	t9,-32752(gp)
  400784:	03e07825 	move	t7,ra
  400788:	0320f809 	jalr	t9
  40078c:	24180009 	li	t8,9
  400790:	8f998010 	lw	t9,-32752(gp)
  400794:	03e07825 	move	t7,ra
  400798:	0320f809 	jalr	t9
  40079c:	24180007 	li	t8,7
	...

Disassembly of section .fini:

004007b0 <_fini>:
  4007b0:	3c1c0002 	lui	gp,0x2
  4007b4:	279c7860 	addiu	gp,gp,30816
  4007b8:	0399e021 	addu	gp,gp,t9
  4007bc:	27bdffe0 	addiu	sp,sp,-32
  4007c0:	afbc0010 	sw	gp,16(sp)
  4007c4:	afbf001c 	sw	ra,28(sp)
  4007c8:	8fbf001c 	lw	ra,28(sp)
  4007cc:	03e00008 	jr	ra
  4007d0:	27bd0020 	addiu	sp,sp,32

Disassembly of section .rodata:

004007e0 <_IO_stdin_used>:
  4007e0:	00020001 	.word	0x20001
	...
  4007f0:	77726f6e 	jalx	dc9bdb8 <_gp+0xd873da8>
  4007f4:	67206172 	.word	0x67206172
  4007f8:	67630000 	.word	0x67630000
  4007fc:	48656c6c 	mfhc2	a1,0x6c6c
  400800:	6f000000 	.word	0x6f000000
  400804:	476f6f64 	bz.d	$w15,41c598 <__FRAME_END__+0x1bd78>
  400808:	62796521 	.word	0x62796521
  40080c:	00000000 	nop
  400810:	77726f6e 	jalx	dc9bdb8 <_gp+0xd873da8>
  400814:	67206b65 	.word	0x67206b65
  400818:	79000000 	ori.b	$w0,$w0,0x0
  40081c:	00000000 	nop

Disassembly of section .eh_frame:

00400820 <__FRAME_END__>:
  400820:	00000000 	nop

Disassembly of section .init_array:

0041fff8 <__frame_dummy_init_array_entry>:
  41fff8:	00400660 	.word	0x400660

Disassembly of section .fini_array:

0041fffc <__do_global_dtors_aux_fini_array_entry>:
  41fffc:	00400624 	.word	0x400624

Disassembly of section .data:

00420000 <__data_start>:
	...

Disassembly of section .rld_map:

00420010 <__RLD_MAP>:
  420010:	00000000 	nop

Disassembly of section .got:

00420020 <_GLOBAL_OFFSET_TABLE_>:
  420020:	00000000 	nop
  420024:	80000000 	lb	zero,0(zero)
  420028:	00400670 	tge	v0,zero,0x19
	...
  420034:	00400790 	.word	0x400790
  420038:	00000000 	nop
  42003c:	00400780 	.word	0x400780
  420040:	00400770 	tge	v0,zero,0x1d

Disassembly of section .sdata:

00420044 <__dso_handle>:
  420044:	00000000 	nop

Disassembly of section .comment:

00000000 <.comment>:
   0:	4743433a 	bz.w	$w3,10cec <__abi_tag-0x3ef510>
   4:	20285562 	addi	t0,at,21858
   8:	756e7475 	jalx	5b9d1d4 <_gp+0x57751c4>
   c:	2031322e 	addi	s1,at,12846
  10:	332e302d 	andi	t6,t9,0x302d
  14:	31377562 	andi	s7,t1,0x7562
  18:	756e7475 	jalx	5b9d1d4 <_gp+0x57751c4>
  1c:	31292031 	andi	t1,t1,0x2031
  20:	322e332e 	andi	t6,s1,0x332e
  24:	Address 0x24 is out of bounds.


Disassembly of section .pdr:

00000000 <.pdr>:
   0:	00400670 	tge	v0,zero,0x19
   4:	c0000000 	ll	zero,0(zero)
   8:	fffffffc 	.word	0xfffffffc
	...
  14:	00000020 	add	zero,zero,zero
  18:	0000001e 	.word	0x1e
  1c:	0000001f 	.word	0x1f

Disassembly of section .gnu.attributes:

00000000 <.gnu.attributes>:
   0:	41000000 	mftc0	zero,c0_index
   4:	0f676e75 	jal	d9db9d4 <_gp+0xd5b39c4>
   8:	00010000 	sll	zero,at,0x0
   c:	00070405 	.word	0x70405
