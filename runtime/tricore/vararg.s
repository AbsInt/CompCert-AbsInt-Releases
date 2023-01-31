// *****************************************************************
//
//               The Compcert verified compiler
//
//           Xavier Leroy, Collège de France and INRIA Paris
//
// Copyright (c) Institut National de Recherche en Informatique et
//  en Automatique.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the <organization> nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
// HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
// EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
// LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// *********************************************************************

// Helper functions for variadic functions <stdarg.h>. TriCore version.

	.text
	.balign 1
	.globl __compcert_va_int32
__compcert_va_int32:
	ld.a	%a14, [%a4]
	add.a	%a14, 4
	st.a	[%a4], %a14
	ld.w	%d2, [%a14], -4
	ret
	.type	__compcert_va_int32, @function
	.size	__compcert_va_int32, . - __compcert_va_int32

	.balign 1
	.globl __compcert_va_float32
__compcert_va_float32:
	ld.a	%a14, [%a4]
	add.a	%a14, 4
	st.a	[%a4], %a14
	ld.w	%d2, [%a14], -4
	ret
 	.type	__compcert_va_float32, @function
 	.size	__compcert_va_float32, . - __compcert_va_float32

# The helper function for composites returns a pointer to the start of the composite.
# There are two different cases, either the argument is passed as 32/64 bit on the stack
# or the composite is passed via pointer.
	.balign 1
	.globl __compcert_va_composite
__compcert_va_composite:
# Load the address of the argument
	ld.a	%a14, [%a4]
	jge.u	%d4, 9, .L2 # Test wether the argument is passed directly or via pointer
	mov.aa	%a2, %a14 # Move the address to the return register
	add.a	%a14, 4 # Increase the address of the next argument position by 4
	jlt.u	%d4, 5, .L1 # If the size is >= 4 we additionally must increase the size by an additional 4
	add.a	%a14, 4
.L1:
	st.a	[%a4], %a14 # Write the pointer back
	ret
.L2:
	add.a	%a14, 4
	st.a	[%a4], %a14
	ld.a	%a2, [%a14], -4 # Load the pointer from the stack
	ret
	.type	__compcert_va_composite, @function
	.size	__compcert_va_composite, . - __compcert_va_composite

    .balign 1
	.globl __compcert_va_int64
__compcert_va_int64:
	ld.a	%a14, [%a4]
	lea		%a14, [%a14],8
	st.a	[%a4], %a14
	ld.d	%e2, [%a14], (-8)
	ret
	.type	__compcert_va_int64, @function
	.size	__compcert_va_int64, . - __compcert_va_int64
