	.text
	.file	"rsa_e_3.c"
	.globl	RSA_e_3_verify          # -- Begin function RSA_e_3_verify
	.p2align	1
	.type	RSA_e_3_verify,@function
RSA_e_3_verify:                         # @RSA_e_3_verify
# %bb.0:
	addi	sp, sp, -304
	sd	ra, 296(sp)
	sd	s0, 288(sp)
	sd	s1, 280(sp)
	sd	s2, 272(sp)
	sd	s3, 264(sp)
	addi	a4, zero, 256
	add	s1, zero, a0
	mv	a0, zero
	bne	a2, a4, .LBB0_13
# %bb.1:
	add	s0, zero, a3
	add	s2, zero, a2
	lwu	a2, 0(s1)
	addi	a3, zero, 64
	bne	a2, a3, .LBB0_13
# %bb.2:
	lw	a0, 520(s1)
	addi	a2, zero, 3
	bne	a0, a2, .LBB0_12
# %bb.3:
	addi	a0, zero, 1
	blt	s2, a0, .LBB0_5
# %bb.4:
	slli	a0, s2, 32
	srli	a2, a0, 32
	addi	a0, sp, 8
	call	memcpy
.LBB0_5:
	addi	s3, sp, 8
	add	a0, zero, s1
	add	a1, zero, s3
	call	modpow3
	mv	a0, zero
	lui	a1, %hi(padding)
	addi	a1, a1, %lo(padding)
	addi	a2, zero, 236
.LBB0_6:                                # =>This Inner Loop Header: Depth=1
	add	a3, s3, a0
	lbu	a3, 0(a3)
	add	a4, a0, a1
	lbu	a4, 0(a4)
	bne	a3, a4, .LBB0_12
# %bb.7:                                #   in Loop: Header=BB0_6 Depth=1
	addi	a0, a0, 1
	bne	a0, a2, .LBB0_6
# %bb.8:
	addi	a1, zero, 237
	addi	a0, zero, 1
	blt	s2, a1, .LBB0_13
# %bb.9:
	slli	a1, s2, 32
	srli	a2, a1, 32
	addi	a1, s3, 236
	addi	a2, a2, -236
.LBB0_10:                               # =>This Inner Loop Header: Depth=1
	lbu	a3, 0(a1)
	lbu	a4, 0(s0)
	bne	a3, a4, .LBB0_12
# %bb.11:                               #   in Loop: Header=BB0_10 Depth=1
	addi	s0, s0, 1
	addi	a2, a2, -1
	addi	a1, a1, 1
	bnez	a2, .LBB0_10
	j	.LBB0_13
.LBB0_12:
	mv	a0, zero
.LBB0_13:
	ld	s3, 264(sp)
	ld	s2, 272(sp)
	ld	s1, 280(sp)
	ld	s0, 288(sp)
	ld	ra, 296(sp)
	addi	sp, sp, 304
	ret
.Lfunc_end0:
	.size	RSA_e_3_verify, .Lfunc_end0-RSA_e_3_verify
                                        # -- End function
	.p2align	1               # -- Begin function modpow3
	.type	modpow3,@function
modpow3:                                # @modpow3
# %bb.0:
	addi	sp, sp, -832
	sd	ra, 824(sp)
	sd	s0, 816(sp)
	sd	s1, 808(sp)
	sd	s2, 800(sp)
	sd	s3, 792(sp)
	sd	s4, 784(sp)
	sd	s5, 776(sp)
	add	s5, zero, a0
	lw	a5, 0(a0)
	addi	a0, zero, 1
	add	s0, zero, a1
	blt	a5, a0, .LBB1_3
# %bb.1:
	lw	a6, 0(s5)
	mv	a1, zero
	mv	a2, zero
	slli	a3, a6, 32
	srli	a7, a3, 32
	addi	a4, sp, 520
.LBB1_2:                                # =>This Inner Loop Header: Depth=1
	not	s1, a2
	addw	a5, a5, s1
	slli	s1, a5, 2
	slliw	a5, a5, 2
	add	a5, a5, s0
	lb	a5, 0(a5)
	ori	a0, s1, 1
	sext.w	a0, a0
	add	a0, a0, s0
	lbu	a0, 0(a0)
	slli	a5, a5, 24
	slli	a0, a0, 16
	ori	a3, s1, 2
	sext.w	a3, a3
	add	a3, a3, s0
	lbu	a3, 0(a3)
	ori	s1, s1, 3
	sext.w	s1, s1
	add	s1, s1, s0
	lbu	s1, 0(s1)
	or	a0, a0, a5
	slli	a3, a3, 8
	or	a0, a0, a3
	or	a0, a0, s1
	sw	a0, 0(a4)
	addi	a1, a1, 1
	addi	a2, a2, 1
	addi	a4, a4, 4
	add	a5, zero, a7
	blt	a1, a6, .LBB1_2
.LBB1_3:
	addi	a3, s5, 264
	addi	s2, sp, 264
	addi	s3, sp, 520
	add	a0, zero, s5
	add	a1, zero, s2
	add	a2, zero, s3
	call	montMul
	addi	s4, sp, 8
	add	a0, zero, s5
	add	a1, zero, s4
	add	a2, zero, s2
	add	a3, zero, s2
	call	montMul
	add	a0, zero, s5
	add	a1, zero, s2
	add	a2, zero, s4
	add	a3, zero, s3
	call	montMul
	add	a0, zero, s5
	add	a1, zero, s2
	call	geM
	beqz	a0, .LBB1_5
# %bb.4:
	addi	a1, sp, 264
	add	a0, zero, s5
	call	subM
.LBB1_5:
	lw	a2, 0(s5)
	addi	a0, zero, 1
	blt	a2, a0, .LBB1_8
# %bb.6:
	addi	a1, a2, 1
	slli	a2, a2, 2
	add	a2, a2, s2
	addi	a2, a2, -4
.LBB1_7:                                # =>This Inner Loop Header: Depth=1
	lw	a3, 0(a2)
	srli	a4, a3, 24
	sb	a4, 0(s0)
	srli	a4, a3, 16
	sb	a4, 1(s0)
	srli	a4, a3, 8
	sb	a4, 2(s0)
	sb	a3, 3(s0)
	addi	a1, a1, -1
	addi	a2, a2, -4
	addi	s0, s0, 4
	blt	a0, a1, .LBB1_7
.LBB1_8:
	ld	s5, 776(sp)
	ld	s4, 784(sp)
	ld	s3, 792(sp)
	ld	s2, 800(sp)
	ld	s1, 808(sp)
	ld	s0, 816(sp)
	ld	ra, 824(sp)
	addi	sp, sp, 832
	ret
.Lfunc_end1:
	.size	modpow3, .Lfunc_end1-modpow3
                                        # -- End function
	.p2align	1               # -- Begin function montMul
	.type	montMul,@function
montMul:                                # @montMul
# %bb.0:
	addi	sp, sp, -48
	sd	ra, 40(sp)
	sd	s0, 32(sp)
	sd	s1, 24(sp)
	sd	s2, 16(sp)
	sd	s3, 8(sp)
	sd	s4, 0(sp)
	add	s4, zero, a0
	lw	a4, 0(a0)
	addi	a0, zero, 1
	add	s2, zero, a3
	add	s1, zero, a2
	add	s3, zero, a1
	blt	a4, a0, .LBB2_3
# %bb.1:
	mv	a1, zero
	add	a2, zero, s3
.LBB2_2:                                # =>This Inner Loop Header: Depth=1
	sw	zero, 0(a2)
	lw	a3, 0(s4)
	addi	a1, a1, 1
	addi	a2, a2, 4
	blt	a1, a3, .LBB2_2
.LBB2_3:
	lw	a1, 0(s4)
	blt	a1, a0, .LBB2_6
# %bb.4:
	mv	s0, zero
.LBB2_5:                                # =>This Inner Loop Header: Depth=1
	lw	a2, 0(s1)
	add	a0, zero, s4
	add	a1, zero, s3
	add	a3, zero, s2
	call	montMulAdd
	lw	a0, 0(s4)
	addi	s0, s0, 1
	addi	s1, s1, 4
	blt	s0, a0, .LBB2_5
.LBB2_6:
	ld	s4, 0(sp)
	ld	s3, 8(sp)
	ld	s2, 16(sp)
	ld	s1, 24(sp)
	ld	s0, 32(sp)
	ld	ra, 40(sp)
	addi	sp, sp, 48
	ret
.Lfunc_end2:
	.size	montMul, .Lfunc_end2-montMul
                                        # -- End function
	.p2align	1               # -- Begin function geM
	.type	geM,@function
geM:                                    # @geM
# %bb.0:
	lw	a3, 0(a0)
	addi	a2, a3, 1
	slli	a3, a3, 2
	add	a1, a1, a3
	addi	a1, a1, -4
	add	a0, a0, a3
	addi	a3, a0, 4
	addi	a0, zero, 1
.LBB3_1:                                # =>This Inner Loop Header: Depth=1
	addi	a2, a2, -1
	beqz	a2, .LBB3_4
# %bb.2:                                #   in Loop: Header=BB3_1 Depth=1
	lw	a5, 0(a1)
	lw	a4, 0(a3)
	bltu	a5, a4, .LBB3_5
# %bb.3:                                #   in Loop: Header=BB3_1 Depth=1
	addi	a1, a1, -4
	slli	a5, a5, 32
	srli	a5, a5, 32
	slli	a4, a4, 32
	srli	a4, a4, 32
	sext.w	a5, a5
	sext.w	a4, a4
	addi	a3, a3, -4
	bgeu	a4, a5, .LBB3_1
.LBB3_4:
	ret
.LBB3_5:
	mv	a0, zero
	ret
.Lfunc_end3:
	.size	geM, .Lfunc_end3-geM
                                        # -- End function
	.p2align	1               # -- Begin function subM
	.type	subM,@function
subM:                                   # @subM
# %bb.0:
	lw	a2, 0(a0)
	addi	a3, zero, 1
	blt	a2, a3, .LBB4_3
# %bb.1:
	mv	a2, zero
	mv	a4, zero
	addi	a3, a0, 8
.LBB4_2:                                # =>This Inner Loop Header: Depth=1
	lwu	a6, 0(a1)
	lwu	a5, 0(a3)
	sub	a5, a6, a5
	add	a4, a4, a5
	sw	a4, 0(a1)
	lw	a5, 0(a0)
	srai	a4, a4, 32
	addi	a2, a2, 1
	addi	a1, a1, 4
	addi	a3, a3, 4
	blt	a2, a5, .LBB4_2
.LBB4_3:
	ret
.Lfunc_end4:
	.size	subM, .Lfunc_end4-subM
                                        # -- End function
	.p2align	1               # -- Begin function montMulAdd
	.type	montMulAdd,@function
montMulAdd:                             # @montMulAdd
# %bb.0:
	addi	sp, sp, -32
	sd	ra, 24(sp)
	sd	s0, 16(sp)
	sd	s1, 8(sp)
	addi	t6, zero, 1
	slli	a4, t6, 32
	addi	a7, a4, -1
	slli	a6, a2, 32
	lwu	a4, 0(a3)
	lwu	a2, 0(a1)
	srli	a6, a6, 32
	lw	t0, 4(a0)
	mul	a4, a4, a6
	add	a2, a2, a4
	lwu	t1, 8(a0)
	mul	a4, t0, a2
	slli	a4, a4, 32
	srli	t0, a4, 32
	mul	t1, t0, t1
	slli	a4, a2, 32
	lw	t3, 0(a0)
	srli	a4, a4, 32
	add	t2, t1, a4
	addi	a4, zero, 2
	srli	t1, a2, 32
	blt	t3, a4, .LBB5_4
# %bb.1:
	mv	t3, zero
	addi	a2, a1, 4
	addi	a3, a3, 4
	addi	a4, a0, 12
.LBB5_2:                                # =>This Inner Loop Header: Depth=1
	lwu	t4, 0(a3)
	lwu	t5, 0(a2)
	mul	t4, t4, a6
	lwu	s1, 0(a4)
	add	a5, t4, t1
	add	a5, a5, t5
	srli	s0, t2, 32
	mul	s1, s1, t0
	add	s1, s1, s0
	and	s0, a5, a7
	add	t2, s1, s0
	sw	t2, -4(a2)
	addi	t6, t6, 1
	lw	s1, 0(a0)
	srli	t1, a5, 32
	addi	a2, a2, 4
	addi	a3, a3, 4
	addi	a4, a4, 4
	add	a5, a7, t3
	addi	t3, a5, 1
	blt	t6, s1, .LBB5_2
# %bb.3:
	srai	a2, t3, 32
	j	.LBB5_5
.LBB5_4:
	mv	a2, zero
.LBB5_5:
	srli	a3, t2, 32
	add	a3, a3, t1
	slli	a2, a2, 2
	add	a2, a2, a1
	addi	a4, a7, 1
	and	a4, a4, a3
	sw	a3, 0(a2)
	beqz	a4, .LBB5_7
# %bb.6:
	call	subM
.LBB5_7:
	ld	s1, 8(sp)
	ld	s0, 16(sp)
	ld	ra, 24(sp)
	addi	sp, sp, 32
	ret
.Lfunc_end5:
	.size	montMulAdd, .Lfunc_end5-montMulAdd
                                        # -- End function
	.type	padding,@object         # @padding
	.section	.rodata,"a",@progbits
padding:
	.ascii	"\000\001\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\0000!0\t\006\005+\016\003\002\032\005\000\004\024"
	.size	padding, 236

	.ident	"clang version 10.0.0 "
	.section	".note.GNU-stack","",@progbits
	.addrsig
