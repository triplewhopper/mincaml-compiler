
.globl mincaml_floor
mincaml_floor:
        fmv.x.s a4,fa0
        li      a2,22
        srai    a5,a4,23
        andi    a5,a5,255
        addi    a5,a5,-127
        mv      a3,a4
        bgt     a5,a2,.L9
        blt     a5,zero,.L19
        lui     a1,0x00800
        addi    a2,a1,-1
        sra     a2,a2,a5
        and     a0,a2,a4
        beq     a0,zero,.L12
        bge     a4,zero,.L13
        sra     a1,a1,a5
        add     a3,a4,a1
.L13:
        not     a2,a2
        and     a4,a2,a3
.L12:
        fmv.s.x fa0,a4
        ret
.L19:
        mv      a4,zero
        bge     a3,zero,.L12
        slli    a3,a3,1
        beq     a3,zero,.L20
        lui     a4,0xbf800
        j       .L12
.L9:
        li      a3,128
        bne     a5,a3,.L12
        fadd.s  fa5,fa0,fa0
        fmv.x.s a4,fa5
        j       .L12
.L20:
        li      a4,-1
        srli    a4,a4,1
        j       .L12

.globl print_int
print_int:
    mv a3, ra
    bgt a0, zero, print_positive
    beq a0, zero, print_zero
    li a1, 45
    out a1
    lui a2, 0x80000
    beq a0, a2, print_INT_MIN
    neg a0, a0
print_positive:
    call divmod_10
    beq a1, zero, print_leading_zero_2
    fmv.w.x ft1, a0

    mv a0, a1
    call divmod_10
    beq a1, zero, print_leading_zero_1
    fmv.w.x ft2, a0
    
    mv a0, a1
    call divmod_10
    beq a1, zero, print_positive_end_3
    fmv.w.x ft3, a0
    
    mv a0, a1
    call divmod_10
    beq a1, zero, print_positive_end_4
    fmv.w.x ft4, a0

    mv a0, a1
    call divmod_10
    beq a1, zero, print_positive_end_5
    fmv.w.x ft5, a0
    
    mv a0, a1
    call divmod_10
    beq a1, zero, print_positive_end_6
    fmv.w.x ft6, a0
    
    mv a0, a1
    call divmod_10
    beq a1, zero, print_positive_end_7
    fmv.w.x ft7, a0
    
    mv a0, a1
    call divmod_10
    beq a1, zero, print_positive_end_8
    fmv.w.x ft8, a0
    
    mv a0, a1
    call divmod_10
    beq a1, zero, print_positive_end_9
    addi a1, a1, 48
    out a1
print_positive_end_9:
    addi a0, a0, 48
    out a0

    fmv.x.w a0, ft8
print_positive_end_8:
    addi a0, a0, 48
    out a0

    fmv.x.w a0, ft7
print_positive_end_7:
    addi a0, a0, 48
    out a0

    fmv.x.w a0, ft6
print_positive_end_6:
    addi a0, a0, 48
    out a0
    
    fmv.x.w a0, ft5
print_positive_end_5:
    addi a0, a0, 48
    out a0
    
    fmv.x.w a0, ft4
print_positive_end_4:
    addi a0, a0, 48
    out a0

    fmv.x.w a0, ft3
print_positive_end_3:
    addi a0, a0, 48
    out a0

    fmv.x.w a0, ft2
print_positive_end_2:
    addi a0, a0, 48
    out a0

    fmv.x.w a0, ft1
print_positive_end_1:
    addi a0, a0, 48
    out a0
    jr a3

print_leading_zero_2: # "00"
    li a1, 48
    out a1
    out a1
    j print_positive_end_1

print_leading_zero_1: # "0"
    li a1, 48
    out a1
    j print_positive_end_2

print_zero: # "000"
    li a0, 48
    out a0
    out a0
    out a0
    jr a3

print_INT_MIN:
    li a0, 50 # '2'
    out a0
    li a0, 49 # '1'
    out a0
    li a1, 52 # '4'
    out a1
    li a0, 55 # '7'
    out a0
    out a1    # '4'
    li a4, 56 # '8'
    out a4
    li a0, 51 # '3'
    out a0
    li a0, 54 # '6'
    out a0
    out a1    # '4'
    out a4    # '8'
    jr a3
    
divmod_10: # a0: dividend; 0 <= a0 <= 2^31 - 1
    li t0, 10
    li t2, 5
    mv t1, zero
divmod_10_loop:
    bge t0, a0, divmod_10_loop_end
    slli t0, t0, 1
    slli t2, t2, 1
    addi t1, t1, 1
    ble t0, zero, overflow
    j divmod_10_loop
overflow:
    addi t1, t1, -1
    mv t0, t2
divmod_10_loop_end:
    mv a1, zero
divmod_10_loop2:
    blt t1, zero, divmod_10_loop2_end
    blt a0, t0, divmod_10_else
    sub a0, a0, t0
    srli t0, t0, 1
    slli a1, a1, 1
    ori a1, a1, 1
    addi t1, t1, -1
    j divmod_10_loop2
divmod_10_else:
    srli t0, t0, 1
    slli a1, a1, 1
    addi t1, t1, -1
    j divmod_10_loop2
divmod_10_loop2_end:
    # a0: remainder; a1: quotient
    ret


	.text
	.attribute	4, 16
	.attribute	5, "rv32i2p1_f2p2_zicsr2p0"
	.file	"trigonometric.c"
	.section	.sdata,"aw",@progbits
	.p2align	2, 0x0                          # -- Begin function mincaml_atan
.LCPI0_0:
	.word	0xbdb7d66e                      # float -0.0897644609
.LCPI0_1:
	.word	0x3d75e7c5                      # float 0.0600354858
.LCPI0_2:
	.word	0x3de38e38                      # float 0.111111104
.LCPI0_3:
	.word	0xbe124925                      # float -0.142857149
.LCPI0_4:
	.word	0x3e4ccccd                      # float 0.200000003
.LCPI0_5:
	.word	0xbeaaaaaa                      # float -0.333333313
.LCPI0_6:
	.word	0xbfc90fdb                      # float -1.57079637
.LCPI0_7:
	.word	0x3fc90fdb                      # float 1.57079637
.LCPI0_8:
	.word	0xbf490fdb                      # float -0.785398185
.LCPI0_9:
	.word	0x3f490fdb                      # float 0.785398185
	.text
	.globl	mincaml_atan
	.p2align	2
	.type	mincaml_atan,@function
mincaml_atan:                           # @mincaml_atan
# %bb.0:
	fabs.s	fa5, fa0
	fmv.x.w	a1, fa5
	lui	a0, 257536
	addi	a0, a0, -1
	blt	a0, a1, .LBB0_2
# %bb.1:
	lui	a0, %hi(.LCPI0_0)
	flw	fa5, %lo(.LCPI0_0)(a0)
	lui	a0, %hi(.LCPI0_1)
	flw	fa4, %lo(.LCPI0_1)(a0)
	lui	a0, %hi(.LCPI0_2)
	flw	fa3, %lo(.LCPI0_2)(a0)
	fmul.s	fa2, fa0, fa0
	fmadd.s	fa5, fa2, fa4, fa5
	fmadd.s	fa5, fa2, fa5, fa3
	lui	a0, %hi(.LCPI0_3)
	flw	fa4, %lo(.LCPI0_3)(a0)
	lui	a0, %hi(.LCPI0_4)
	flw	fa3, %lo(.LCPI0_4)(a0)
	lui	a0, %hi(.LCPI0_5)
	flw	fa1, %lo(.LCPI0_5)(a0)
	fmadd.s	fa5, fa2, fa5, fa4
	fmadd.s	fa5, fa2, fa5, fa3
	fmul.s	fa4, fa2, fa0
	fmadd.s	fa5, fa2, fa5, fa1
	fmadd.s	fa0, fa4, fa5, fa0
	ret
.LBB0_2:
	lui	a0, 262592
	addi	a2, a0, -1
	fmv.x.w	a0, fa0
	bltu	a2, a1, .LBB0_5
# %bb.3:
	lui	a1, 784384
	fmv.w.x	fa4, a1
	fadd.s	fa4, fa5, fa4
	lui	a1, 260096
	fmv.w.x	fa3, a1
	fadd.s	fa5, fa5, fa3
	lui	a1, %hi(.LCPI0_0)
	flw	fa3, %lo(.LCPI0_0)(a1)
	lui	a1, %hi(.LCPI0_1)
	flw	fa2, %lo(.LCPI0_1)(a1)
	lui	a1, %hi(.LCPI0_2)
	flw	fa1, %lo(.LCPI0_2)(a1)
	fdiv.s	fa5, fa4, fa5
	fmul.s	fa4, fa5, fa5
	fmadd.s	fa3, fa4, fa2, fa3
	fmadd.s	fa3, fa4, fa3, fa1
	lui	a1, %hi(.LCPI0_3)
	flw	fa2, %lo(.LCPI0_3)(a1)
	lui	a1, %hi(.LCPI0_4)
	flw	fa1, %lo(.LCPI0_4)(a1)
	lui	a1, %hi(.LCPI0_5)
	flw	fa0, %lo(.LCPI0_5)(a1)
	fmadd.s	fa3, fa4, fa3, fa2
	fmadd.s	fa3, fa4, fa3, fa1
	fmul.s	fa2, fa5, fa4
	fmadd.s	fa4, fa4, fa3, fa0
	fmadd.s	fa5, fa2, fa4, fa5
	bltz	a0, .LBB0_7
# %bb.4:
	lui	a0, %hi(.LCPI0_9)
	flw	fa4, %lo(.LCPI0_9)(a0)
	fadd.s	fa0, fa5, fa4
	ret
.LBB0_5:
	lui	a1, 260096
	fmv.w.x	fa4, a1
	lui	a1, %hi(.LCPI0_0)
	flw	fa3, %lo(.LCPI0_0)(a1)
	lui	a1, %hi(.LCPI0_1)
	flw	fa2, %lo(.LCPI0_1)(a1)
	lui	a1, %hi(.LCPI0_2)
	flw	fa1, %lo(.LCPI0_2)(a1)
	fdiv.s	fa5, fa4, fa5
	fmul.s	fa4, fa5, fa5
	fmadd.s	fa3, fa4, fa2, fa3
	fmadd.s	fa3, fa4, fa3, fa1
	lui	a1, %hi(.LCPI0_3)
	flw	fa2, %lo(.LCPI0_3)(a1)
	lui	a1, %hi(.LCPI0_4)
	flw	fa1, %lo(.LCPI0_4)(a1)
	lui	a1, %hi(.LCPI0_5)
	flw	fa0, %lo(.LCPI0_5)(a1)
	fmadd.s	fa3, fa4, fa3, fa2
	fmadd.s	fa3, fa4, fa3, fa1
	fmul.s	fa2, fa5, fa4
	fmadd.s	fa4, fa4, fa3, fa0
	fmadd.s	fa5, fa2, fa4, fa5
	bltz	a0, .LBB0_8
# %bb.6:
	lui	a0, %hi(.LCPI0_7)
	flw	fa4, %lo(.LCPI0_7)(a0)
	fsub.s	fa0, fa4, fa5
	ret
.LBB0_7:
	lui	a0, %hi(.LCPI0_8)
	flw	fa4, %lo(.LCPI0_8)(a0)
	fsub.s	fa0, fa4, fa5
	ret
.LBB0_8:
	lui	a0, %hi(.LCPI0_6)
	flw	fa4, %lo(.LCPI0_6)(a0)
	fadd.s	fa0, fa5, fa4
	ret
.Lfunc_end0:
	.size	mincaml_atan, .Lfunc_end0-mincaml_atan
                                        # -- End function
	.section	.sdata,"aw",@progbits
	.p2align	2, 0x0                          # -- Begin function mincaml_sin
.LCPI1_0:
	.word	0x40c90fdb                      # float 6.28318548
.LCPI1_1:
	.word	0x40490fdb                      # float 3.14159274
.LCPI1_2:
	.word	0xc0490fdb                      # float -3.14159274
.LCPI1_3:
	.word	0x3fc90fdb                      # float 1.57079637
.LCPI1_4:
	.word	0x3f490fdb                      # float 0.785398185
.LCPI1_5:
	.word	0x3c088666                      # float 0.00833282433
.LCPI1_6:
	.word	0xb94d64b6                      # float -1.95878412E-4
.LCPI1_7:
	.word	0xbe2aaaac                      # float -0.166666687
.LCPI1_8:
	.word	0x3d2aa789                      # float 0.0416636802
.LCPI1_9:
	.word	0xbab38106                      # float -0.00136950682
	.text
	.globl	mincaml_sin
	.p2align	2
	.type	mincaml_sin,@function
mincaml_sin:                            # @mincaml_sin
# %bb.0:
	lui	a0, %hi(.LCPI1_0)
	flw	fa4, %lo(.LCPI1_0)(a0)
	fabs.s	fa5, fa0
	fle.s	a0, fa4, fa5
	bnez	a0, .LBB1_9
.LBB1_1:
	lui	a0, %hi(.LCPI1_1)
	flw	fa4, %lo(.LCPI1_1)(a0)
	fle.s	a0, fa4, fa5
	fmv.x.w	a1, fa0
	beqz	a0, .LBB1_3
# %bb.2:
	lui	a2, %hi(.LCPI1_2)
	flw	fa3, %lo(.LCPI1_2)(a2)
	fadd.s	fa5, fa5, fa3
.LBB1_3:
	lui	a2, %hi(.LCPI1_3)
	flw	fa3, %lo(.LCPI1_3)(a2)
	fle.s	a2, fa3, fa5
	srai	a1, a1, 31
	beqz	a2, .LBB1_5
# %bb.4:
	fsub.s	fa5, fa4, fa5
.LBB1_5:
	lui	a2, %hi(.LCPI1_4)
	flw	fa4, %lo(.LCPI1_4)(a2)
	fle.s	a2, fa5, fa4
	xor	a0, a1, a0
	bnez	a2, .LBB1_14
# %bb.6:
	lui	a1, %hi(.LCPI1_3)
	flw	fa4, %lo(.LCPI1_3)(a1)
	lui	a1, %hi(.LCPI1_8)
	flw	fa3, %lo(.LCPI1_8)(a1)
	lui	a1, %hi(.LCPI1_9)
	flw	fa2, %lo(.LCPI1_9)(a1)
	fsub.s	fa5, fa4, fa5
	fmul.s	fa5, fa5, fa5
	fmadd.s	fa4, fa5, fa2, fa3
	lui	a1, 782336
	fmv.w.x	fa3, a1
	fmadd.s	fa4, fa5, fa4, fa3
	lui	a1, 260096
	fmv.w.x	fa3, a1
	fmadd.s	fa0, fa5, fa4, fa3
	beqz	a0, .LBB1_8
.LBB1_7:
	fneg.s	fa0, fa0
.LBB1_8:
	ret
.LBB1_9:                                # =>This Inner Loop Header: Depth=1
	fadd.s	fa4, fa4, fa4
	fle.s	a0, fa4, fa5
	bnez	a0, .LBB1_9
# %bb.10:
	lui	a0, %hi(.LCPI1_0)
	flw	fa3, %lo(.LCPI1_0)(a0)
	fmv.w.x	fa2, zero
	lui	a0, 258048
	fmv.w.x	fa1, a0
	j	.LBB1_12
.LBB1_11:                               #   in Loop: Header=BB1_12 Depth=1
	fsub.s	fa5, fa5, ft0
	fle.s	a0, fa3, fa5
	fmul.s	fa4, fa4, fa1
	beqz	a0, .LBB1_1
.LBB1_12:                               # =>This Inner Loop Header: Depth=1
	fle.s	a0, fa4, fa5
	fmv.s	ft0, fa2
	beqz	a0, .LBB1_11
# %bb.13:                               #   in Loop: Header=BB1_12 Depth=1
	fmv.s	ft0, fa4
	j	.LBB1_11
.LBB1_14:
	lui	a1, %hi(.LCPI1_5)
	flw	fa4, %lo(.LCPI1_5)(a1)
	lui	a1, %hi(.LCPI1_6)
	flw	fa3, %lo(.LCPI1_6)(a1)
	lui	a1, %hi(.LCPI1_7)
	flw	fa2, %lo(.LCPI1_7)(a1)
	fmul.s	fa1, fa5, fa5
	fmul.s	fa0, fa5, fa1
	fmadd.s	fa4, fa1, fa3, fa4
	fmadd.s	fa4, fa1, fa4, fa2
	fmadd.s	fa0, fa0, fa4, fa5
	bnez	a0, .LBB1_7
	j	.LBB1_8
.Lfunc_end1:
	.size	mincaml_sin, .Lfunc_end1-mincaml_sin
                                        # -- End function
	.section	.sdata,"aw",@progbits
	.p2align	2, 0x0                          # -- Begin function mincaml_cos
.LCPI2_0:
	.word	0x40c90fdb                      # float 6.28318548
.LCPI2_1:
	.word	0x40490fdb                      # float 3.14159274
.LCPI2_2:
	.word	0xc0490fdb                      # float -3.14159274
.LCPI2_3:
	.word	0x3fc90fdb                      # float 1.57079637
.LCPI2_4:
	.word	0x3f490fdb                      # float 0.785398185
.LCPI2_5:
	.word	0x3d2aa789                      # float 0.0416636802
.LCPI2_6:
	.word	0xbab38106                      # float -0.00136950682
.LCPI2_7:
	.word	0x3c088666                      # float 0.00833282433
.LCPI2_8:
	.word	0xb94d64b6                      # float -1.95878412E-4
.LCPI2_9:
	.word	0xbe2aaaac                      # float -0.166666687
	.text
	.globl	mincaml_cos
	.p2align	2
	.type	mincaml_cos,@function
mincaml_cos:                            # @mincaml_cos
# %bb.0:
	lui	a0, %hi(.LCPI2_0)
	flw	fa4, %lo(.LCPI2_0)(a0)
	fabs.s	fa5, fa0
	fle.s	a0, fa4, fa5
	bnez	a0, .LBB2_5
.LBB2_1:
	lui	a0, %hi(.LCPI2_1)
	flw	fa3, %lo(.LCPI2_1)(a0)
	fle.s	a0, fa3, fa5
	bnez	a0, .LBB2_10
# %bb.2:
	fmv.s	fa4, fa5
	lui	a0, %hi(.LCPI2_3)
	flw	fa2, %lo(.LCPI2_3)(a0)
	fle.s	a0, fa2, fa5
	beqz	a0, .LBB2_11
.LBB2_3:
	fsub.s	fa3, fa3, fa4
	lui	a0, %hi(.LCPI2_4)
	flw	fa2, %lo(.LCPI2_4)(a0)
	fle.s	a0, fa3, fa2
	beqz	a0, .LBB2_12
.LBB2_4:
	lui	a0, %hi(.LCPI2_5)
	flw	fa2, %lo(.LCPI2_5)(a0)
	lui	a0, %hi(.LCPI2_6)
	flw	fa1, %lo(.LCPI2_6)(a0)
	fmul.s	fa3, fa3, fa3
	fmadd.s	fa2, fa3, fa1, fa2
	lui	a0, 782336
	fmv.w.x	fa1, a0
	fmadd.s	fa2, fa3, fa2, fa1
	lui	a0, 260096
	fmv.w.x	fa1, a0
	fmadd.s	fa0, fa3, fa2, fa1
	j	.LBB2_13
.LBB2_5:                                # =>This Inner Loop Header: Depth=1
	fadd.s	fa4, fa4, fa4
	fle.s	a0, fa4, fa5
	bnez	a0, .LBB2_5
# %bb.6:
	lui	a0, %hi(.LCPI2_0)
	flw	fa3, %lo(.LCPI2_0)(a0)
	fmv.w.x	fa2, zero
	lui	a0, 258048
	fmv.w.x	fa1, a0
	j	.LBB2_8
.LBB2_7:                                #   in Loop: Header=BB2_8 Depth=1
	fsub.s	fa5, fa5, fa0
	fle.s	a0, fa3, fa5
	fmul.s	fa4, fa4, fa1
	beqz	a0, .LBB2_1
.LBB2_8:                                # =>This Inner Loop Header: Depth=1
	fle.s	a0, fa4, fa5
	fmv.s	fa0, fa2
	beqz	a0, .LBB2_7
# %bb.9:                                #   in Loop: Header=BB2_8 Depth=1
	fmv.s	fa0, fa4
	j	.LBB2_7
.LBB2_10:
	lui	a0, %hi(.LCPI2_2)
	flw	fa4, %lo(.LCPI2_2)(a0)
	fadd.s	fa4, fa5, fa4
	lui	a0, %hi(.LCPI2_3)
	flw	fa2, %lo(.LCPI2_3)(a0)
	fle.s	a0, fa2, fa4
	bnez	a0, .LBB2_3
.LBB2_11:
	fmv.s	fa3, fa4
	lui	a0, %hi(.LCPI2_4)
	flw	fa2, %lo(.LCPI2_4)(a0)
	fle.s	a0, fa4, fa2
	bnez	a0, .LBB2_4
.LBB2_12:
	lui	a0, %hi(.LCPI2_3)
	flw	fa2, %lo(.LCPI2_3)(a0)
	fsub.s	fa3, fa2, fa3
	lui	a0, %hi(.LCPI2_7)
	flw	fa2, %lo(.LCPI2_7)(a0)
	lui	a0, %hi(.LCPI2_8)
	flw	fa1, %lo(.LCPI2_8)(a0)
	lui	a0, %hi(.LCPI2_9)
	flw	fa0, %lo(.LCPI2_9)(a0)
	fmul.s	ft0, fa3, fa3
	fmul.s	ft1, fa3, ft0
	fmadd.s	fa2, ft0, fa1, fa2
	fmadd.s	fa2, ft0, fa2, fa0
	fmadd.s	fa0, ft1, fa2, fa3
.LBB2_13:
	lui	a0, %hi(.LCPI2_3)
	flw	fa3, %lo(.LCPI2_3)(a0)
	lui	a0, %hi(.LCPI2_1)
	flw	fa2, %lo(.LCPI2_1)(a0)
	fle.s	a0, fa3, fa4
	fle.s	a1, fa2, fa5
	beq	a1, a0, .LBB2_15
# %bb.14:
	fneg.s	fa0, fa0
.LBB2_15:
	ret
