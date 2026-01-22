/*****************************************************************
 *
 *               The Compcert verified compiler
 *
 *           Bernhard Schommer, AbsInt Angewandte Informatik GmbH
 *
 * Copyright (c) 2020 AbsInt Angewandte Informatik GmbH.
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

/* Conversion float32 -> signed int64 */

long long i64_ftos(float f)
{
  /* Extract bits of d's representation */
  union { float f; unsigned int i; } buf;
  buf.f = f;
  unsigned int h = buf.i;
  /* Extract unbiased exponent */
  int e = ((h & 0x7F800000) >> 23) - (127 + 23);
  /* Check range of exponent */
  if (e < -23) {
    /* d is less than 1.0 */
    return 0ULL;
  }
  if (e >= 63 - 23) {
    /* |d| is greater or equal to 2^63 */
    if ((int) h < 0)
      return -0x8000000000000000LL; /* min signed long long */
    else
      return  0x7FFFFFFFFFFFFFFFLL; /* max signed long long */
  }
  /* Extract true mantissa */
  unsigned long long m = (buf.i & ~0xFF800000) | 0x800000;
  /* Shift it appropriately */
  if (e >= 0)
    m = i64_shl(m, e);
  else
    m = i64_shr(m, -e);
  /* Apply sign to result */
  if ((int) h < 0)
    return -m;
  else
    return m;
}
