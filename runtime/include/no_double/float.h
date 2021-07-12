/* This file is part of the Compcert verified compiler.
 *
 * Copyright (c) 2015 Institut National de Recherche en Informatique et
 *  en Automatique.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the <organization> nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
 * HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/* <float.h> -- characteristics of floating types (ISO C99 7.7) */

/* This file should be used if the target architecture does not support
 * IEEE binary64 */

#ifndef _FLOAT_H
#define _FLOAT_H

/* FP numbers are in binary */
#define FLT_RADIX 2

/* No excess precision is used during FP arithmetic */
#define FLT_EVAL_METHOD 0

/* FP operations round to nearest even */
#define FLT_ROUNDS 1

/* Number of decimal digits sufficient to represent FP numbers */
#define DECIMAL_DIG 17

/* The "float" type is IEEE binary32 */
#define FLT_MANT_DIG 24
#define FLT_DIG 6
#define FLT_ROUNDS 1
#define FLT_EPSILON 0x1p-23F
#define FLT_MIN_EXP (-125)
#define FLT_MIN 0x1p-126F
#define FLT_MIN_10_EXP (-37)
#define FLT_MAX_EXP 128
#define FLT_MAX 0x1.fffffep+127F
#define FLT_MAX_10_EXP 38

/* The "double" type is IEEE binary32 */
#define DBL_MANT_DIG 24
#define DBL_DIG 6
#define DBL_ROUNDS 1
#define DBL_EPSILON 0x1p-23
#define DBL_MIN_EXP (-125)
#define DBL_MIN 0x1p-126
#define DBL_MIN_10_EXP (-37)
#define DBL_MAX_EXP 128
#define DBL_MAX 0x1.fffffep+127
#define DBL_MAX_10_EXP 38

/* The "long double" type, when supported, is IEEE binary32 */
#define LDBL_MANT_DIG 24
#define LDBL_DIG 6
#define LDBL_ROUNDS 1
#define LDBL_EPSILON 0x1p-23L
#define LDBL_MIN_EXP (-125)
#define LDBL_MIN 0x1p-126L
#define LDBL_MIN_10_EXP (-37)
#define LDBL_MAX_EXP 128
#define LDBL_MAX 0x1.fffffep+127L
#define LDBL_MAX_10_EXP 38

#endif

