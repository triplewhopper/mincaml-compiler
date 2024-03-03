.section .text
.type create_array_0_0, @function
.globl create_array_0_0
create_array_0_0:
    mv t0, tp
.5643_Lloop_J:
    beqz a0, .9703_Lelse0_J
    j .9705_Lthen_J
.9703_Lelse0_J:
    j .9704_Lelse_J
.9705_Lthen_J:
    sw a1, 0(tp)
    addi tp, tp, 4
    addi a0, a0, -1
    j .5643_Lloop_J
.9704_Lelse_J:
.9706_Lendif_J:
    mv a0, t0
    ret

.section .text
.type create_array_1_0, @function
.globl create_array_1_0
create_array_1_0:
    mv t0, tp
.5646_Lloop_J:
    beqz a0, .9707_Lelse0_J
    j .9709_Lthen_J
.9707_Lelse0_J:
    j .9708_Lelse_J
.9709_Lthen_J:
    fsw fa0, 0(tp)
    addi tp, tp, 4
    addi a0, a0, -1
    j .5646_Lloop_J
.9708_Lelse_J:
.9710_Lendif_J:
    mv a0, t0
    ret

.section .text
.type create_array_0000000_4, @function
.globl create_array_0000000_4
create_array_0000000_4:
    addi sp, sp, -16
    mv t0, tp
    lw t1, 0(sp)
    lw t2, 4(sp)
    lw t3, 8(sp)
    lw t4, 12(sp)
.5649_Lloop_J:
    beqz a0, .9711_Lelse0_J
    j .9713_Lthen_J
.9711_Lelse0_J:
    j .9712_Lelse_J
.9713_Lthen_J:
    sw a1, 0(tp)
    sw a2, 4(tp)
    sw a3, 8(tp)
    sw a4, 12(tp)
    sw a5, 16(tp)
    sw a6, 20(tp)
    sw a7, 24(tp)
    sw t1, 28(tp)
    sw t2, 32(tp)
    sw t3, 36(tp)
    sw t4, 40(tp)
    addi tp, tp, 44
    addi a0, a0, -1
    j .5649_Lloop_J
.9712_Lelse_J:
.9714_Lendif_J:
    mv a0, t0
    addi sp, sp, 16
    ret

.section .text
.type create_array_00_0, @function
.globl create_array_00_0
create_array_00_0:
    mv t0, tp
.5652_Lloop_J:
    beqz a0, .9715_Lelse0_J
    j .9717_Lthen_J
.9715_Lelse0_J:
    j .9716_Lelse_J
.9717_Lthen_J:
    sw a1, 0(tp)
    sw a2, 4(tp)
    addi tp, tp, 8
    addi a0, a0, -1
    j .5652_Lloop_J
.9716_Lelse_J:
.9718_Lendif_J:
    mv a0, t0
    ret

.section .text
.type create_array_0001_0, @function
.globl create_array_0001_0
create_array_0001_0:
    mv t0, tp
.5655_Lloop_J:
    beqz a0, .9719_Lelse0_J
    j .9721_Lthen_J
.9719_Lelse0_J:
    j .9720_Lelse_J
.9721_Lthen_J:
    sw a1, 0(tp)
    sw a2, 4(tp)
    sw a3, 8(tp)
    fsw fa0, 12(tp)
    addi tp, tp, 16
    addi a0, a0, -1
    j .5655_Lloop_J
.9720_Lelse_J:
.9722_Lendif_J:
    mv a0, t0
    ret

.section .text
.type create_array_0000000_1, @function
.globl create_array_0000000_1
create_array_0000000_1:
    addi sp, sp, -16
    mv t0, tp
    lw t1, 12(sp)
.5658_Lloop_J:
    beqz a0, .9723_Lelse0_J
    j .9725_Lthen_J
.9723_Lelse0_J:
    j .9724_Lelse_J
.9725_Lthen_J:
    sw a1, 0(tp)
    sw a2, 4(tp)
    sw a3, 8(tp)
    sw a4, 12(tp)
    sw a5, 16(tp)
    sw a6, 20(tp)
    sw a7, 24(tp)
    sw t1, 28(tp)
    addi tp, tp, 32
    addi a0, a0, -1
    j .5658_Lloop_J
.9724_Lelse_J:
.9726_Lendif_J:
    mv a0, t0
    addi sp, sp, 16
    ret
