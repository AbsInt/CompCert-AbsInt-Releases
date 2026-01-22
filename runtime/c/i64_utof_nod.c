/*****************************************************************
 *
 *               The Compcert verified compiler
 *
 *           Xavier Leroy, INRIA Paris-Rocquencourt
 *
 * Copyright (c) 2013 Institut National de Recherche en Informatique et
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
 *
 **********************************************************************/

/* Helper functions for 64-bit integer arithmetic. Reference C implementation */

#include "i64.h"

/* Conversion from unsigned int64 to float32 without double */

/* We can not go through double so we need to construct the float by hand */

float i64_utof(unsigned long long x) {

  /* If x can be casted to an unsigned integer we
     abuse the integer to float casts */
  if ((x >> 32) == 0) {
    return (float)((unsigned int)x);
  } else {
    /* We extract the 23 bit mantissa by shifting x by
       64 minus the number of leading zeros and 23.
    */
    int shift_amount = 40 - __builtin_clzll(x);
    union {
      float f;
      unsigned int d;
    } conv;
    conv.d = (unsigned int)(i64_shr(x,shift_amount));
    /* Mask the bit 24 which we no longer need */
    conv.d = conv.d & 0x7FFFFF;
    /* Construct the exponent and set the bits of the exponent */
    conv.d = conv.d | ((127 + shift_amount + 23) << 23);
    /* We need to account for rounding if either the mb of the part shifted
       away and the lsb are one or the msb of part shifted away and the
       other bits shifted away are non zero */
    unsigned long long shifted_mask = i64_shl(1, (shift_amount - 1));
    int lb = (x & shifted_mask) != 0;
    int fb = (x & i64_shl(1,shift_amount)) != 0;
    int llb = (x & (shifted_mask - 1ULL)) != 0;
    if (lb && (fb || llb)) {
      conv.d = conv.d + 1;
    }
    return conv.f;
  }
}
