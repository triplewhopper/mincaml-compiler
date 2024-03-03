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

.data
n_objects:
    .zero 4
objects:
    .zero 4
screen:
    .zero 4
viewpoint:
    .zero 4
light:
    .zero 4
beam:
    .zero 4
and_net:
    .zero 4
or_net:
    .zero 4
solver_dist:
    .zero 4
intsec_rectside:
    .zero 4
tmin:
    .zero 4
intersection_point:
    .zero 4
intersected_object_id:
    .zero 4
nvector:
    .zero 4
texture_color:
    .zero 4
diffuse_ray:
    .zero 4
rgb:
    .zero 4
image_size:
    .zero 4
image_center:
    .zero 4
scan_pitch:
    .zero 4
startp:
    .zero 4
startp_fast:
    .zero 4
screenx_dir:
    .zero 4
screeny_dir:
    .zero 4
screenz_dir:
    .zero 4
ptrace_dirvec:
    .zero 4
dirvecs:
    .zero 4
light_dirvec:
    .zero 8
reflections:
    .zero 4
n_reflections:
    .zero 4

.globl .LC_0
.LC_0: 
    .float 255.0
.globl .LC_1
.LC_1: 
    .float 1000000000.0
.globl .LC_2
.LC_2: 
    .float 128.0
.globl .LC_3
.LC_3: 
    .float 0.017453293
.globl .LC_4
.LC_4: 
    .float 200.0
.globl .LC_5
.LC_5: 
    .float -200.0
.globl .LC_6
.LC_6: 
    .float 2.0
.globl .LC_7
.LC_7: 
    .float 0.5
.globl .LC_8
.LC_8: 
    .float -0.2
.globl .LC_9
.LC_9: 
    .float 0.01
.globl .LC_10
.LC_10: 
    .float -0.1
.globl .LC_11
.LC_11: 
    .float 100000000.0
.globl .LC_12
.LC_12: 
    .float 0.05
.globl .LC_13
.LC_13: 
    .float 20.0
.globl .LC_14
.LC_14: 
    .float 10.0
.globl .LC_15
.LC_15: 
    .float 0.25
.globl .LC_16
.LC_16: 
    .float 3.1415927
.globl .LC_17
.LC_17: 
    .float 0.0001
.globl .LC_18
.LC_18: 
    .float 15.0
.globl .LC_19
.LC_19: 
    .float 0.15
.globl .LC_20
.LC_20: 
    .float 0.3
.globl .LC_21
.LC_21: 
    .float 30.0
.globl .LC_22
.LC_22: 
    .float -2.0
.globl .LC_23
.LC_23: 
    .float 0.1
.globl .LC_24
.LC_24: 
    .float 256.0
.globl .LC_25
.LC_25: 
    .float -150.0
.globl .LC_26
.LC_26: 
    .float 150.0
.globl .LC_27
.LC_27: 
    .float 0.2
.globl .LC_28
.LC_28: 
    .float 0.9
