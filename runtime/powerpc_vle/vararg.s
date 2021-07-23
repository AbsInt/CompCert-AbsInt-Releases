# *****************************************************************
#
#               The Compcert verified compiler
#
#           Xavier Leroy, INRIA Paris-Rocquencourt
#
# Copyright (c) 2013 Institut National de Recherche en Informatique et
#  en Automatique.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice, this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#     * Neither the name of the <organization> nor the
#       names of its contributors may be used to endorse or promote products
#       derived from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
# HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
# EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
# PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
# PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
# LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
# NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
# *********************************************************************

# Helper functions for variadic functions <stdarg.h>.  PowerPC VLE version

# typedef struct {
#   unsigned char ireg;    // index of next integer register
#   unsigned char freg;    // index of next FP register
#   char * stk;            // pointer to next argument in stack
#   struct {
#     int iregs[8];
#     double fregs[8];
#   } * regs;              // pointer to saved register area
# } va_list[1];
#
# unsigned int __compcert_va_int32(va_list ap);
# unsigned long long __compcert_va_int64(va_list ap);
# double __compcert_va_float64(va_list ap);

        .text

        .balign 16
        .globl __compcert_va_int32
__compcert_va_int32:
	                            # r3 = ap = address of va_list structure
        se_lbz     r4, 0(r3)        # r4 = ap->ireg = next integer register
        e_cmpl16i  r4, 8
        e_bge      1f
  # Next argument was passed in an integer register
        se_lwz     r5, 8(r3)        # r5 = ap->regs = base of saved register area
        e_rlwinm   r6, r4, 2, 0, 29 # r6 = r4 * 4
        se_addi    r4,  1           # increment ap->ireg
        se_stb     r4, 0(r3)
        lwzx       r3, r5, r6       # load argument in r3
        se_blr
  # Next argument was passed on stack
1:      se_lwz     r5, 4(r3)        # r5 = ap->stk = next argument passed on stack
        se_addi    r5, 4            # advance ap->stk by 4
        se_stw     r5, 4(r3)
        e_lwz      r3, -4(r5)       # load argument in r3
        se_blr
        .type   __compcert_va_int32, @function
        .size   __compcert_va_int32, .-__compcert_va_int32

        .balign 16
        .globl __compcert_va_int64
__compcert_va_int64:
                                    # r3 = ap = address of va_list structure
        se_lbz     r4, 0(r3)        # r4 = ap->ireg = next integer register
        e_cmpl16i  r4, 7
        e_bge     1f
  # Next argument was passed in two consecutive integer register
        se_lwz     r5, 8(r3)        # r5 = ap->regs = base of saved register area
        se_addi    r4, 3            # round r4 up to an even number and add 2
        e_rlwinm   r4, r4, 0, 0, 30
        e_rlwinm   r6, r4, 2, 0, 29 # r6 = r4 * 4
        se_add     r5, r6           # r5 = address of argument + 8
        se_stb     r4, 0(r3)        # update ap->ireg
        e_lwz      r3, -8(r5)       # load argument in r3:r4
        e_lwz      r4, -4(r5)
        se_blr
  # Next argument was passed on stack
1:      se_lwz     r5, 4(r3)        # r5 = ap->stk = next argument passed on stack
        se_li      r4, 8
        se_stb     r4, 0(r3)        # set ap->ireg = 8 so that no ireg is left
        se_addi    r5, 15           # round r5 to a multiple of 8 and add 8
        e_rlwinm   r5, r5, 0, 0, 28
        se_stw     r5, 4(r3)        # update ap->stk
        e_lwz      r3, -8(r5)       # load argument in r3:r4
        e_lwz      r4, -4(r5)
        se_blr
        .type   __compcert_va_int64, @function
        .size   __compcert_va_int64, .-__compcert_va_int64

        .balign 16
        .globl __compcert_va_composite
__compcert_va_composite:
	b       __compcert_va_int32
	.type   __compcert_va_composite, @function
	.size   __compcert_va_composite, .-__compcert_va_composite

	.balign 16
	.globl __compcert_va_float32
__compcert_va_float32:
	b       __compcert_va_int32
	.type   __compcert_va_float32, @function
	.size   __compcert_va_float32, .-__compcert_va_float32


# Save integer registers at beginning of vararg function

        .balign 16
        .globl  __compcert_va_saveregs
__compcert_va_saveregs:
        e_lwz      r11, 0(r1)       # r11 point to top of our frame
        e_stwu     r3, -96(r11)     # register save area is 96 bytes below
        e_stw      r4, 4(r11)
        e_stw      r5, 8(r11)
        e_stw      r6, 12(r11)
        e_stw      r7, 16(r11)
        e_stw      r8, 20(r11)
        e_stw      r9, 24(r11)
        e_stw      r10, 28(r11)
1:      se_blr
        .type   __compcert_va_saveregs, @function
        .size   __compcert_va_saveregs, .-__compcert_va_saveregs
