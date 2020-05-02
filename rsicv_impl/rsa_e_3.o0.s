	.text
	.file	"rsa_e_3.c"
	.globl	RSA_e_3_verify          # -- Begin function RSA_e_3_verify
	.p2align	1
	.type	RSA_e_3_verify,@function
RSA_e_3_verify:                         # @RSA_e_3_verify
# %bb.0:
	addi	sp, sp, -320
	sd	ra, 312(sp)
	sd	s0, 304(sp)
	addi	s0, sp, 320
	add	a4, zero, a2
	sd	a0, -32(s0)
	sd	a1, -40(s0)
	sw	a2, -44(s0)
	sd	a3, -56(s0)
	ld	a0, -32(s0)
	lw	a0, 0(a0)
	addi	a1, zero, 64
	beq	a0, a1, .LBB0_2
	j	.LBB0_1
.LBB0_1:
	mv	a0, zero
	sw	a0, -20(s0)
	j	.LBB0_23
.LBB0_2:
	lw	a0, -44(s0)
	addi	a1, zero, 256
	beq	a0, a1, .LBB0_4
	j	.LBB0_3
.LBB0_3:
	mv	a0, zero
	sw	a0, -20(s0)
	j	.LBB0_23
.LBB0_4:
	ld	a0, -32(s0)
	lw	a0, 520(a0)
	addi	a1, zero, 3
	beq	a0, a1, .LBB0_6
	j	.LBB0_5
.LBB0_5:
	mv	a0, zero
	sw	a0, -20(s0)
	j	.LBB0_23
.LBB0_6:
	mv	a0, zero
	sw	a0, -316(s0)
	j	.LBB0_7
.LBB0_7:                                # =>This Inner Loop Header: Depth=1
	lw	a0, -316(s0)
	lw	a1, -44(s0)
	bge	a0, a1, .LBB0_10
	j	.LBB0_8
.LBB0_8:                                #   in Loop: Header=BB0_7 Depth=1
	ld	a0, -40(s0)
	lw	a1, -316(s0)
	add	a0, a0, a1
	lb	a0, 0(a0)
	addi	a2, s0, -312
	add	a1, a1, a2
	sb	a0, 0(a1)
	j	.LBB0_9
.LBB0_9:                                #   in Loop: Header=BB0_7 Depth=1
	lw	a0, -316(s0)
	addi	a0, a0, 1
	sw	a0, -316(s0)
	j	.LBB0_7
.LBB0_10:
	ld	a0, -32(s0)
	addi	a1, s0, -312
	call	modpow3
	mv	a0, zero
	sw	a0, -316(s0)
	j	.LBB0_11
.LBB0_11:                               # =>This Inner Loop Header: Depth=1
	lw	a0, -316(s0)
	addi	a1, zero, 235
	blt	a1, a0, .LBB0_16
	j	.LBB0_12
.LBB0_12:                               #   in Loop: Header=BB0_11 Depth=1
	lw	a0, -316(s0)
	addi	a1, s0, -312
	add	a1, a1, a0
	lbu	a1, 0(a1)
	lui	a2, %hi(padding)
	addi	a2, a2, %lo(padding)
	add	a0, a0, a2
	lbu	a0, 0(a0)
	beq	a1, a0, .LBB0_14
	j	.LBB0_13
.LBB0_13:
	mv	a0, zero
	sw	a0, -20(s0)
	j	.LBB0_23
.LBB0_14:                               #   in Loop: Header=BB0_11 Depth=1
	j	.LBB0_15
.LBB0_15:                               #   in Loop: Header=BB0_11 Depth=1
	lw	a0, -316(s0)
	addi	a0, a0, 1
	sw	a0, -316(s0)
	j	.LBB0_11
.LBB0_16:
	j	.LBB0_17
.LBB0_17:                               # =>This Inner Loop Header: Depth=1
	lw	a0, -316(s0)
	lw	a1, -44(s0)
	bge	a0, a1, .LBB0_22
	j	.LBB0_18
.LBB0_18:                               #   in Loop: Header=BB0_17 Depth=1
	lw	a0, -316(s0)
	addi	a1, s0, -312
	add	a0, a0, a1
	lbu	a0, 0(a0)
	ld	a1, -56(s0)
	addi	a2, a1, 1
	sd	a2, -56(s0)
	lbu	a1, 0(a1)
	beq	a0, a1, .LBB0_20
	j	.LBB0_19
.LBB0_19:
	mv	a0, zero
	sw	a0, -20(s0)
	j	.LBB0_23
.LBB0_20:                               #   in Loop: Header=BB0_17 Depth=1
	j	.LBB0_21
.LBB0_21:                               #   in Loop: Header=BB0_17 Depth=1
	lw	a0, -316(s0)
	addi	a0, a0, 1
	sw	a0, -316(s0)
	j	.LBB0_17
.LBB0_22:
	addi	a0, zero, 1
	sw	a0, -20(s0)
	j	.LBB0_23
.LBB0_23:
	lw	a0, -20(s0)
	ld	s0, 304(sp)
	ld	ra, 312(sp)
	addi	sp, sp, 320
	ret
.Lfunc_end0:
	.size	RSA_e_3_verify, .Lfunc_end0-RSA_e_3_verify
                                        # -- End function
	.p2align	1               # -- Begin function modpow3
	.type	modpow3,@function
modpow3:                                # @modpow3
# %bb.0:
	addi	sp, sp, -848
	sd	ra, 840(sp)
	sd	s0, 832(sp)
	addi	s0, sp, 848
	sd	a0, -24(s0)
	sd	a1, -32(s0)
	addi	a0, s0, -544
	sd	a0, -808(s0)
	mv	a0, zero
	sw	a0, -812(s0)
	j	.LBB1_1
.LBB1_1:                                # =>This Inner Loop Header: Depth=1
	lw	a0, -812(s0)
	ld	a1, -24(s0)
	lw	a1, 0(a1)
	bge	a0, a1, .LBB1_4
	j	.LBB1_2
.LBB1_2:                                #   in Loop: Header=BB1_1 Depth=1
	ld	a0, -32(s0)
	ld	a1, -24(s0)
	lw	a1, 0(a1)
	lw	a2, -812(s0)
	subw	a1, a1, a2
	slli	a1, a1, 2
	addiw	a2, a1, -4
	add	a2, a2, a0
	lb	a2, 0(a2)
	slli	a2, a2, 24
	addiw	a3, a1, -3
	add	a3, a3, a0
	lbu	a3, 0(a3)
	slli	a3, a3, 16
	or	a2, a2, a3
	addiw	a3, a1, -2
	add	a3, a3, a0
	lbu	a3, 0(a3)
	slli	a3, a3, 8
	or	a2, a2, a3
	addiw	a1, a1, -1
	add	a0, a0, a1
	lbu	a0, 0(a0)
	or	a0, a0, a2
	sw	a0, -816(s0)
	lw	a0, -816(s0)
	lw	a1, -812(s0)
	slli	a1, a1, 2
	addi	a2, s0, -288
	add	a1, a1, a2
	sw	a0, 0(a1)
	j	.LBB1_3
.LBB1_3:                                #   in Loop: Header=BB1_1 Depth=1
	lw	a0, -812(s0)
	addi	a0, a0, 1
	sw	a0, -812(s0)
	j	.LBB1_1
.LBB1_4:
	ld	a0, -24(s0)
	addi	a3, a0, 264
	addi	a1, s0, -544
	addi	a2, s0, -288
	sd	a1, -832(s0)
	sd	a2, -840(s0)
	call	montMul
	ld	a0, -24(s0)
	addi	a1, s0, -800
	sd	a1, -848(s0)
	ld	a2, -832(s0)
	ld	a3, -832(s0)
	call	montMul
	ld	a0, -24(s0)
	ld	a1, -808(s0)
	ld	a2, -848(s0)
	ld	a3, -840(s0)
	call	montMul
	ld	a0, -24(s0)
	ld	a1, -808(s0)
	call	geM
	mv	a1, zero
	beq	a0, a1, .LBB1_6
	j	.LBB1_5
.LBB1_5:
	ld	a0, -24(s0)
	ld	a1, -808(s0)
	call	subM
	j	.LBB1_6
.LBB1_6:
	ld	a0, -24(s0)
	lw	a0, 0(a0)
	addi	a0, a0, -1
	sw	a0, -812(s0)
	j	.LBB1_7
.LBB1_7:                                # =>This Inner Loop Header: Depth=1
	lw	a0, -812(s0)
	mv	a1, zero
	blt	a0, a1, .LBB1_10
	j	.LBB1_8
.LBB1_8:                                #   in Loop: Header=BB1_7 Depth=1
	ld	a0, -808(s0)
	lw	a1, -812(s0)
	slli	a1, a1, 2
	add	a0, a0, a1
	lw	a0, 0(a0)
	sw	a0, -820(s0)
	lb	a0, -817(s0)
	ld	a1, -32(s0)
	addi	a2, a1, 1
	sd	a2, -32(s0)
	sb	a0, 0(a1)
	lb	a0, -818(s0)
	ld	a1, -32(s0)
	addi	a2, a1, 1
	sd	a2, -32(s0)
	sb	a0, 0(a1)
	lb	a0, -819(s0)
	ld	a1, -32(s0)
	addi	a2, a1, 1
	sd	a2, -32(s0)
	sb	a0, 0(a1)
	lb	a0, -820(s0)
	ld	a1, -32(s0)
	addi	a2, a1, 1
	sd	a2, -32(s0)
	sb	a0, 0(a1)
	j	.LBB1_9
.LBB1_9:                                #   in Loop: Header=BB1_7 Depth=1
	lw	a0, -812(s0)
	addi	a0, a0, -1
	sw	a0, -812(s0)
	j	.LBB1_7
.LBB1_10:
	ld	s0, 832(sp)
	ld	ra, 840(sp)
	addi	sp, sp, 848
	ret
.Lfunc_end1:
	.size	modpow3, .Lfunc_end1-modpow3
                                        # -- End function
	.p2align	1               # -- Begin function montMul
	.type	montMul,@function
montMul:                                # @montMul
# %bb.0:
	addi	sp, sp, -64
	sd	ra, 56(sp)
	sd	s0, 48(sp)
	addi	s0, sp, 64
	sd	a0, -24(s0)
	sd	a1, -32(s0)
	sd	a2, -40(s0)
	sd	a3, -48(s0)
	mv	a0, zero
	sw	a0, -52(s0)
	j	.LBB2_1
.LBB2_1:                                # =>This Inner Loop Header: Depth=1
	lw	a0, -52(s0)
	ld	a1, -24(s0)
	lw	a1, 0(a1)
	bge	a0, a1, .LBB2_4
	j	.LBB2_2
.LBB2_2:                                #   in Loop: Header=BB2_1 Depth=1
	ld	a0, -32(s0)
	lw	a1, -52(s0)
	slli	a1, a1, 2
	add	a0, a0, a1
	mv	a1, zero
	sw	a1, 0(a0)
	j	.LBB2_3
.LBB2_3:                                #   in Loop: Header=BB2_1 Depth=1
	lw	a0, -52(s0)
	addi	a0, a0, 1
	sw	a0, -52(s0)
	j	.LBB2_1
.LBB2_4:
	mv	a0, zero
	sw	a0, -52(s0)
	j	.LBB2_5
.LBB2_5:                                # =>This Inner Loop Header: Depth=1
	lw	a0, -52(s0)
	ld	a1, -24(s0)
	lw	a1, 0(a1)
	bge	a0, a1, .LBB2_8
	j	.LBB2_6
.LBB2_6:                                #   in Loop: Header=BB2_5 Depth=1
	ld	a0, -24(s0)
	ld	a1, -32(s0)
	ld	a2, -40(s0)
	lw	a3, -52(s0)
	slli	a3, a3, 2
	add	a2, a2, a3
	lw	a2, 0(a2)
	ld	a3, -48(s0)
	call	montMulAdd
	j	.LBB2_7
.LBB2_7:                                #   in Loop: Header=BB2_5 Depth=1
	lw	a0, -52(s0)
	addi	a0, a0, 1
	sw	a0, -52(s0)
	j	.LBB2_5
.LBB2_8:
	ld	s0, 48(sp)
	ld	ra, 56(sp)
	addi	sp, sp, 64
	ret
.Lfunc_end2:
	.size	montMul, .Lfunc_end2-montMul
                                        # -- End function
	.p2align	1               # -- Begin function geM
	.type	geM,@function
geM:                                    # @geM
# %bb.0:
	addi	sp, sp, -48
	sd	ra, 40(sp)
	sd	s0, 32(sp)
	addi	s0, sp, 48
	sd	a0, -32(s0)
	sd	a1, -40(s0)
	ld	a0, -32(s0)
	lw	a0, 0(a0)
	sw	a0, -44(s0)
	j	.LBB3_1
.LBB3_1:                                # =>This Inner Loop Header: Depth=1
	lw	a0, -44(s0)
	mv	a1, zero
	beq	a0, a1, .LBB3_7
	j	.LBB3_2
.LBB3_2:                                #   in Loop: Header=BB3_1 Depth=1
	lw	a0, -44(s0)
	addi	a0, a0, -1
	sw	a0, -44(s0)
	ld	a0, -40(s0)
	lw	a1, -44(s0)
	slli	a1, a1, 2
	add	a0, a0, a1
	lw	a0, 0(a0)
	ld	a2, -32(s0)
	add	a1, a1, a2
	lw	a1, 8(a1)
	bgeu	a0, a1, .LBB3_4
	j	.LBB3_3
.LBB3_3:
	mv	a0, zero
	sw	a0, -20(s0)
	j	.LBB3_8
.LBB3_4:                                #   in Loop: Header=BB3_1 Depth=1
	ld	a0, -40(s0)
	lw	a1, -44(s0)
	slli	a1, a1, 2
	add	a0, a0, a1
	lw	a0, 0(a0)
	ld	a2, -32(s0)
	add	a1, a1, a2
	lw	a1, 8(a1)
	bgeu	a1, a0, .LBB3_6
	j	.LBB3_5
.LBB3_5:
	addi	a0, zero, 1
	sw	a0, -20(s0)
	j	.LBB3_8
.LBB3_6:                                #   in Loop: Header=BB3_1 Depth=1
	j	.LBB3_1
.LBB3_7:
	addi	a0, zero, 1
	sw	a0, -20(s0)
	j	.LBB3_8
.LBB3_8:
	lw	a0, -20(s0)
	ld	s0, 32(sp)
	ld	ra, 40(sp)
	addi	sp, sp, 48
	ret
.Lfunc_end3:
	.size	geM, .Lfunc_end3-geM
                                        # -- End function
	.p2align	1               # -- Begin function subM
	.type	subM,@function
subM:                                   # @subM
# %bb.0:
	addi	sp, sp, -48
	sd	ra, 40(sp)
	sd	s0, 32(sp)
	addi	s0, sp, 48
	sd	a0, -24(s0)
	sd	a1, -32(s0)
	mv	a0, zero
	sd	a0, -40(s0)
	sw	a0, -44(s0)
	j	.LBB4_1
.LBB4_1:                                # =>This Inner Loop Header: Depth=1
	lw	a0, -44(s0)
	ld	a1, -24(s0)
	lw	a1, 0(a1)
	bge	a0, a1, .LBB4_4
	j	.LBB4_2
.LBB4_2:                                #   in Loop: Header=BB4_1 Depth=1
	ld	a0, -32(s0)
	lw	a1, -44(s0)
	slli	a1, a1, 2
	add	a0, a0, a1
	lwu	a0, 0(a0)
	ld	a2, -24(s0)
	add	a1, a1, a2
	lwu	a1, 8(a1)
	sub	a0, a0, a1
	ld	a1, -40(s0)
	add	a0, a0, a1
	sd	a0, -40(s0)
	ld	a0, -40(s0)
	ld	a1, -32(s0)
	lw	a2, -44(s0)
	slli	a2, a2, 2
	add	a1, a1, a2
	sw	a0, 0(a1)
	ld	a0, -40(s0)
	srai	a0, a0, 32
	sd	a0, -40(s0)
	j	.LBB4_3
.LBB4_3:                                #   in Loop: Header=BB4_1 Depth=1
	lw	a0, -44(s0)
	addi	a0, a0, 1
	sw	a0, -44(s0)
	j	.LBB4_1
.LBB4_4:
	ld	s0, 32(sp)
	ld	ra, 40(sp)
	addi	sp, sp, 48
	ret
.Lfunc_end4:
	.size	subM, .Lfunc_end4-subM
                                        # -- End function
	.p2align	1               # -- Begin function montMulAdd
	.type	montMulAdd,@function
montMulAdd:                             # @montMulAdd
# %bb.0:
	addi	sp, sp, -80
	sd	ra, 72(sp)
	sd	s0, 64(sp)
	addi	s0, sp, 80
	add	a4, zero, a2
	sd	a0, -24(s0)
	sd	a1, -32(s0)
	sw	a2, -36(s0)
	sd	a3, -48(s0)
	lwu	a0, -36(s0)
	ld	a1, -48(s0)
	lwu	a1, 0(a1)
	mul	a0, a0, a1
	ld	a1, -32(s0)
	lwu	a1, 0(a1)
	add	a0, a0, a1
	sd	a0, -56(s0)
	lw	a0, -56(s0)
	ld	a1, -24(s0)
	lw	a1, 4(a1)
	mul	a0, a0, a1
	sw	a0, -60(s0)
	lwu	a0, -60(s0)
	ld	a1, -24(s0)
	lwu	a1, 8(a1)
	mul	a0, a0, a1
	lwu	a1, -56(s0)
	add	a0, a0, a1
	sd	a0, -72(s0)
	addi	a0, zero, 1
	sw	a0, -76(s0)
	j	.LBB5_1
.LBB5_1:                                # =>This Inner Loop Header: Depth=1
	lw	a0, -76(s0)
	ld	a1, -24(s0)
	lw	a1, 0(a1)
	bge	a0, a1, .LBB5_4
	j	.LBB5_2
.LBB5_2:                                #   in Loop: Header=BB5_1 Depth=1
	lwu	a0, -52(s0)
	lwu	a1, -36(s0)
	ld	a2, -48(s0)
	lw	a3, -76(s0)
	slli	a3, a3, 2
	add	a2, a2, a3
	lwu	a2, 0(a2)
	mul	a1, a1, a2
	add	a0, a0, a1
	ld	a1, -32(s0)
	add	a1, a1, a3
	lwu	a1, 0(a1)
	add	a0, a0, a1
	sd	a0, -56(s0)
	lwu	a0, -68(s0)
	lwu	a1, -60(s0)
	ld	a2, -24(s0)
	lw	a3, -76(s0)
	slli	a3, a3, 2
	add	a2, a2, a3
	lwu	a2, 8(a2)
	mul	a1, a1, a2
	add	a0, a0, a1
	lwu	a1, -56(s0)
	add	a0, a0, a1
	sd	a0, -72(s0)
	ld	a0, -72(s0)
	ld	a1, -32(s0)
	lw	a2, -76(s0)
	addiw	a2, a2, -1
	slli	a2, a2, 2
	add	a1, a1, a2
	sw	a0, 0(a1)
	j	.LBB5_3
.LBB5_3:                                #   in Loop: Header=BB5_1 Depth=1
	lw	a0, -76(s0)
	addi	a0, a0, 1
	sw	a0, -76(s0)
	j	.LBB5_1
.LBB5_4:
	lwu	a0, -52(s0)
	lwu	a1, -68(s0)
	add	a0, a0, a1
	sd	a0, -56(s0)
	ld	a0, -56(s0)
	ld	a1, -32(s0)
	lw	a2, -76(s0)
	addiw	a2, a2, -1
	slli	a2, a2, 2
	add	a1, a1, a2
	sw	a0, 0(a1)
	lwu	a0, -52(s0)
	mv	a1, zero
	beq	a0, a1, .LBB5_6
	j	.LBB5_5
.LBB5_5:
	ld	a0, -24(s0)
	ld	a1, -32(s0)
	call	subM
	j	.LBB5_6
.LBB5_6:
	ld	s0, 64(sp)
	ld	ra, 72(sp)
	addi	sp, sp, 80
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
	.addrsig_sym modpow3
	.addrsig_sym montMul
	.addrsig_sym geM
	.addrsig_sym subM
	.addrsig_sym montMulAdd
	.addrsig_sym padding
