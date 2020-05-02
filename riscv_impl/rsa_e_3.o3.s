	.text
	.file	"rsa_e_3.c"
	.globl	RSA_e_3_verify          # -- Begin function RSA_e_3_verify
	.p2align	1
	.type	RSA_e_3_verify,@function
RSA_e_3_verify:                         # @RSA_e_3_verify
# %bb.0:
	addi	sp, sp, -1088
	sd	ra, 1080(sp)
	sd	s0, 1072(sp)
	sd	s1, 1064(sp)
	sd	s2, 1056(sp)
	sd	s3, 1048(sp)
	sd	s4, 1040(sp)
	sd	s5, 1032(sp)
	addi	a4, zero, 256
	add	s3, zero, a0
	mv	a0, zero
	bne	a2, a4, .LBB0_39
# %bb.1:
	add	s2, zero, a3
	lwu	a2, 0(s3)
	addi	a3, zero, 64
	bne	a2, a3, .LBB0_39
# %bb.2:
	lw	a0, 520(s3)
	addi	a2, zero, 3
	bne	a0, a2, .LBB0_38
# %bb.3:
	addi	s1, sp, 8
	addi	a2, zero, 256
	addi	s4, zero, 256
	add	a0, zero, s1
	call	memcpy
	mv	a0, zero
	mv	a1, zero
	addi	a6, zero, 252
	addi	a7, zero, 253
	addi	t0, zero, 254
	addi	t1, zero, 255
	addi	s0, sp, 776
.LBB0_4:                                # =>This Inner Loop Header: Depth=1
	slli	a2, a1, 2
	subw	a3, a6, a2
	add	a3, a3, s1
	lb	a3, 0(a3)
	subw	a4, a7, a2
	add	a4, a4, s1
	lbu	a4, 0(a4)
	slli	a3, a3, 24
	slli	a4, a4, 16
	subw	a5, t0, a2
	add	a5, a5, s1
	lbu	a5, 0(a5)
	subw	a2, t1, a2
	add	a2, a2, s1
	lbu	a2, 0(a2)
	or	a3, a3, a4
	slli	a4, a5, 8
	or	a3, a3, a4
	or	a2, a2, a3
	add	a3, s0, a0
	sw	a2, 0(a3)
	addi	a0, a0, 4
	addi	a1, a1, 1
	bne	a0, s4, .LBB0_4
# %bb.5:
	addi	a3, s3, 264
	addi	s0, sp, 520
	addi	s4, sp, 776
	add	a0, zero, s3
	add	a1, zero, s0
	add	a2, zero, s4
	call	montMul
	addi	s5, sp, 264
	add	a0, zero, s3
	add	a1, zero, s5
	add	a2, zero, s0
	add	a3, zero, s0
	call	montMul
	add	a0, zero, s3
	add	a1, zero, s0
	add	a2, zero, s5
	add	a3, zero, s4
	call	montMul
	lw	a0, 0(s3)
	slli	a1, a0, 2
	add	a2, a1, s3
	addi	a2, a2, 4
	add	a6, a1, s0
	addi	a3, a6, -4
	addi	a4, a0, 1
.LBB0_6:                                # =>This Inner Loop Header: Depth=1
	addi	a4, a4, -1
	beqz	a4, .LBB0_9
# %bb.7:                                #   in Loop: Header=BB0_6 Depth=1
	lw	a1, 0(a3)
	lw	a5, 0(a2)
	bltu	a1, a5, .LBB0_12
# %bb.8:                                #   in Loop: Header=BB0_6 Depth=1
	addi	a2, a2, -4
	slli	a1, a1, 32
	srli	a1, a1, 32
	slli	a5, a5, 32
	srli	a5, a5, 32
	sext.w	a1, a1
	sext.w	a5, a5
	addi	a3, a3, -4
	bgeu	a5, a1, .LBB0_6
.LBB0_9:
	addi	a1, zero, 1
	blt	a0, a1, .LBB0_15
# %bb.10:
	mv	a4, zero
	addi	a2, s3, 8
	add	a3, zero, a0
.LBB0_11:                               # =>This Inner Loop Header: Depth=1
	lwu	a1, 0(s0)
	lwu	a5, 0(a2)
	sub	a1, a1, a5
	add	a1, a1, a4
	sw	a1, 0(s0)
	srai	a4, a1, 32
	addi	a3, a3, -1
	addi	a2, a2, 4
	addi	s0, s0, 4
	bnez	a3, .LBB0_11
.LBB0_12:
	addi	a2, zero, 1
	blt	a0, a2, .LBB0_15
# %bb.13:
	addi	a0, a0, 1
	addi	a1, a6, -4
	add	a3, zero, s1
.LBB0_14:                               # =>This Inner Loop Header: Depth=1
	lw	a4, 0(a1)
	srli	a5, a4, 24
	sb	a5, 0(a3)
	srli	a5, a4, 16
	sb	a5, 1(a3)
	srli	a5, a4, 8
	sb	a5, 2(a3)
	sb	a4, 3(a3)
	addi	a0, a0, -1
	addi	a1, a1, -4
	addi	a3, a3, 4
	blt	a2, a0, .LBB0_14
.LBB0_15:
	mv	a0, zero
	lui	a1, %hi(padding)
	addi	a1, a1, %lo(padding)
	addi	a2, zero, 236
.LBB0_16:                               # =>This Inner Loop Header: Depth=1
	add	a3, s1, a0
	lbu	a3, 0(a3)
	add	a4, a0, a1
	lbu	a4, 0(a4)
	bne	a3, a4, .LBB0_38
# %bb.17:                               #   in Loop: Header=BB0_16 Depth=1
	addi	a0, a0, 1
	bne	a0, a2, .LBB0_16
# %bb.18:
	lbu	a0, 244(sp)
	lbu	a1, 0(s2)
	bne	a0, a1, .LBB0_38
# %bb.19:
	lbu	a0, 245(sp)
	lbu	a1, 1(s2)
	bne	a0, a1, .LBB0_38
# %bb.20:
	lbu	a0, 246(sp)
	lbu	a1, 2(s2)
	bne	a0, a1, .LBB0_38
# %bb.21:
	lbu	a0, 247(sp)
	lbu	a1, 3(s2)
	bne	a0, a1, .LBB0_38
# %bb.22:
	lbu	a0, 248(sp)
	lbu	a1, 4(s2)
	bne	a0, a1, .LBB0_38
# %bb.23:
	lbu	a0, 249(sp)
	lbu	a1, 5(s2)
	bne	a0, a1, .LBB0_38
# %bb.24:
	lbu	a0, 250(sp)
	lbu	a1, 6(s2)
	bne	a0, a1, .LBB0_38
# %bb.25:
	lbu	a0, 251(sp)
	lbu	a1, 7(s2)
	bne	a0, a1, .LBB0_38
# %bb.26:
	lbu	a0, 252(sp)
	lbu	a1, 8(s2)
	bne	a0, a1, .LBB0_38
# %bb.27:
	lbu	a0, 253(sp)
	lbu	a1, 9(s2)
	bne	a0, a1, .LBB0_38
# %bb.28:
	lbu	a0, 254(sp)
	lbu	a1, 10(s2)
	bne	a0, a1, .LBB0_38
# %bb.29:
	lbu	a0, 255(sp)
	lbu	a1, 11(s2)
	bne	a0, a1, .LBB0_38
# %bb.30:
	lbu	a0, 256(sp)
	lbu	a1, 12(s2)
	bne	a0, a1, .LBB0_38
# %bb.31:
	lbu	a0, 257(sp)
	lbu	a1, 13(s2)
	bne	a0, a1, .LBB0_38
# %bb.32:
	lbu	a0, 258(sp)
	lbu	a1, 14(s2)
	bne	a0, a1, .LBB0_38
# %bb.33:
	lbu	a0, 259(sp)
	lbu	a1, 15(s2)
	bne	a0, a1, .LBB0_38
# %bb.34:
	lbu	a0, 260(sp)
	lbu	a1, 16(s2)
	bne	a0, a1, .LBB0_38
# %bb.35:
	lbu	a0, 261(sp)
	lbu	a1, 17(s2)
	bne	a0, a1, .LBB0_38
# %bb.36:
	lbu	a0, 262(sp)
	lbu	a1, 18(s2)
	bne	a0, a1, .LBB0_38
# %bb.37:
	lbu	a0, 263(sp)
	lbu	a1, 19(s2)
	xor	a0, a0, a1
	seqz	a0, a0
	j	.LBB0_39
.LBB0_38:
	mv	a0, zero
.LBB0_39:
	ld	s5, 1032(sp)
	ld	s4, 1040(sp)
	ld	s3, 1048(sp)
	ld	s2, 1056(sp)
	ld	s1, 1064(sp)
	ld	s0, 1072(sp)
	ld	ra, 1080(sp)
	addi	sp, sp, 1088
	ret
.Lfunc_end0:
	.size	RSA_e_3_verify, .Lfunc_end0-RSA_e_3_verify
                                        # -- End function
	.p2align	1               # -- Begin function montMul
	.type	montMul,@function
montMul:                                # @montMul
# %bb.0:
	addi	sp, sp, -80
	sd	s0, 72(sp)
	sd	s1, 64(sp)
	sd	s2, 56(sp)
	sd	s3, 48(sp)
	sd	s4, 40(sp)
	sd	s5, 32(sp)
	sd	s6, 24(sp)
	sd	s7, 16(sp)
	sd	s8, 8(sp)
	sd	s9, 0(sp)
	lw	a4, 0(a0)
	addi	a5, zero, 1
	blt	a4, a5, .LBB1_16
# %bb.1:
	mv	a4, zero
	add	a5, zero, a1
.LBB1_2:                                # =>This Inner Loop Header: Depth=1
	sw	zero, 0(a5)
	lw	t6, 0(a0)
	addi	a4, a4, 1
	addi	a5, a5, 4
	blt	a4, t6, .LBB1_2
# %bb.3:
	addi	a6, zero, 1
	blt	t6, a6, .LBB1_16
# %bb.4:
	mv	t4, zero
	slli	a4, a6, 32
	addi	t5, a4, -1
	addi	a7, a1, 4
	addi	t0, a0, 12
	addi	t1, a0, 8
	addi	t2, a3, 4
	addi	t3, zero, 2
	j	.LBB1_6
.LBB1_5:                                #   in Loop: Header=BB1_6 Depth=1
	addi	t4, t4, 1
	sext.w	a4, t6
	bge	t4, a4, .LBB1_16
.LBB1_6:                                # =>This Loop Header: Depth=1
                                        #     Child Loop BB1_8 Depth 2
                                        #     Child Loop BB1_14 Depth 2
	slli	a4, t4, 2
	add	a4, a4, a2
	lwu	s2, 0(a4)
	lwu	a4, 0(a3)
	lwu	a5, 0(a1)
	lw	s0, 4(a0)
	mul	a4, a4, s2
	add	a4, a4, a5
	lwu	a5, 8(a0)
	mul	s0, s0, a4
	slli	s0, s0, 32
	srli	s3, s0, 32
	mul	a5, s3, a5
	and	s0, a4, t5
	add	s4, a5, s0
	sext.w	a5, t6
	srli	t6, a4, 32
	blt	a5, t3, .LBB1_10
# %bb.7:                                #   in Loop: Header=BB1_6 Depth=1
	mv	s5, zero
	addi	s9, zero, 1
	add	a4, zero, t2
	add	a5, zero, t0
	add	s0, zero, a7
.LBB1_8:                                #   Parent Loop BB1_6 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	lwu	s6, 0(a4)
	lwu	s7, 0(s0)
	mul	s6, s6, s2
	lwu	s8, 0(a5)
	add	s1, s6, t6
	add	s6, s1, s7
	srli	t6, s4, 32
	mul	s1, s8, s3
	add	t6, t6, s1
	and	s1, s6, t5
	add	s4, t6, s1
	sw	s4, -4(s0)
	addi	s9, s9, 1
	lw	s7, 0(a0)
	srli	t6, s6, 32
	add	s1, t5, s5
	addi	s5, s1, 1
	addi	s0, s0, 4
	addi	a5, a5, 4
	addi	a4, a4, 4
	blt	s9, s7, .LBB1_8
# %bb.9:                                #   in Loop: Header=BB1_6 Depth=1
	srai	a4, s5, 32
	j	.LBB1_11
.LBB1_10:                               #   in Loop: Header=BB1_6 Depth=1
	mv	a4, zero
.LBB1_11:                               #   in Loop: Header=BB1_6 Depth=1
	srli	a5, s4, 32
	add	a5, a5, t6
	slli	a4, a4, 2
	add	a4, a4, a1
	sw	a5, 0(a4)
	lw	t6, 0(a0)
	addi	a4, t5, 1
	and	a4, a4, a5
	beqz	a4, .LBB1_5
# %bb.12:                               #   in Loop: Header=BB1_6 Depth=1
	blt	t6, a6, .LBB1_5
# %bb.13:                               #   in Loop: Header=BB1_6 Depth=1
	mv	a4, zero
	mv	t6, zero
	add	a5, zero, a1
	add	s1, zero, t1
.LBB1_14:                               #   Parent Loop BB1_6 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	lwu	s2, 0(a5)
	lwu	s0, 0(s1)
	sub	s0, s2, s0
	add	t6, t6, s0
	sw	t6, 0(a5)
	lw	s0, 0(a0)
	srai	t6, t6, 32
	addi	a4, a4, 1
	addi	s1, s1, 4
	addi	a5, a5, 4
	blt	a4, s0, .LBB1_14
# %bb.15:                               #   in Loop: Header=BB1_6 Depth=1
	slli	a4, s0, 32
	srli	t6, a4, 32
	j	.LBB1_5
.LBB1_16:
	ld	s9, 0(sp)
	ld	s8, 8(sp)
	ld	s7, 16(sp)
	ld	s6, 24(sp)
	ld	s5, 32(sp)
	ld	s4, 40(sp)
	ld	s3, 48(sp)
	ld	s2, 56(sp)
	ld	s1, 64(sp)
	ld	s0, 72(sp)
	addi	sp, sp, 80
	ret
.Lfunc_end1:
	.size	montMul, .Lfunc_end1-montMul
                                        # -- End function
	.type	padding,@object         # @padding
	.section	.rodata,"a",@progbits
padding:
	.ascii	"\000\001\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\0000!0\t\006\005+\016\003\002\032\005\000\004\024"
	.size	padding, 236

	.ident	"clang version 10.0.0 "
	.section	".note.GNU-stack","",@progbits
	.addrsig
