-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-!
BLAKE2b's compression function `compress` on machine words, with what it needs: the chaining value
`ChainingValue`, the message block `MessageBlock`, the constants `IV`, the rotation `rotr64`, `G` and `ROUND`, and the
state `State`.

`IV`, `rotr64`, `G`, `ROUND`, `State` and `compress` are adapted from blake2b-ref.c, blake2.h and
blake2-impl.h of the BLAKE2 reference source code package (reference C implementations), Copyright
2012, Samuel Neves. Their head offers "the CC0, the OpenSSL Licence, or the Apache Public License
2.0, at your option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0). Their own head
lines, the same in each of the three:

/*
   BLAKE2 reference source code package - reference C implementations

   Copyright 2012, Samuel Neves <sneves@dei.uc.pt>.  You may use this under the
   terms of the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at
   your option.  The terms of these licenses can be found at:

   - CC0 1.0 Universal : http://creativecommons.org/publicdomain/zero/1.0
   - OpenSSL license   : https://www.openssl.org/source/license.html
   - Apache 2.0        : http://www.apache.org/licenses/LICENSE-2.0

   More information about the BLAKE2 hash function can be found at
   https://blake2.net.
*/

There is no array and no loop. A compiled verifier calls `compress` millions of times and Lean's
kernel evaluates it inside proofs, so the sixteen words of `v` and of `m` are structure fields and
function arguments, and each round names its message words in the order of its row of
`blake2b_sigma`.

RFC 7693 is named here as the specification of BLAKE2b: the parameters of section 2.1 (w = 64, r =
12, rotations 32, 24, 16, 63), the initialization vector of section 2.6, the message schedule of
section 2.7, the mixing function G of section 3.1 and the compression function F of section 3.2.

The C++ verifier's text of the compression function is verifier/src/vf_earlier_hash_f.h, outside
this library's directory. No theorem of this library is about that file.
-/

namespace Run.Blake2b

/-- The chaining value: `h[8]` of `blake2b_state` in blake2.h, one field for each word. `State`
below adds `t` and `f`. -/
structure ChainingValue where
  h0 : UInt64
  h1 : UInt64
  h2 : UInt64
  h3 : UInt64
  h4 : UInt64
  h5 : UInt64
  h6 : UInt64
  h7 : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- One message block as sixteen words: `m[16]` in `blake2b_compress`, one field for each word.
The caller has already done that function's first loop: `m0` is `load64` of the block's first eight
bytes, `m1` of the next eight, and so on. -/
structure MessageBlock where
  m0 : UInt64
  m1 : UInt64
  m2 : UInt64
  m3 : UInt64
  m4 : UInt64
  m5 : UInt64
  m6 : UInt64
  m7 : UInt64
  m8 : UInt64
  m9 : UInt64
  m10 : UInt64
  m11 : UInt64
  m12 : UInt64
  m13 : UInt64
  m14 : UInt64
  m15 : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- The work vector: `v[16]` in `blake2b_compress`, one field for each word. -/
structure WorkVector where
  v0 : UInt64
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64
  v4 : UInt64
  v5 : UInt64
  v6 : UInt64
  v7 : UInt64
  v8 : UInt64
  v9 : UInt64
  v10 : UInt64
  v11 : UInt64
  v12 : UInt64
  v13 : UInt64
  v14 : UInt64
  v15 : UInt64

/-- The four words that `G` changes, under the names of its parameters `a`, `b`, `c`, `d`. The
reference assigns to them in place; here `G` returns them. -/
structure Quad where
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64

/-- `blake2b_IV` in blake2b-ref.c, the same eight constants in the same order, as the fields of an
`ChainingValue` instead of an array. -/
@[inline] def IV : ChainingValue :=
  { h0 := 0x6a09e667f3bcc908, h1 := 0xbb67ae8584caa73b,
    h2 := 0x3c6ef372fe94f82b, h3 := 0xa54ff53a5f1d36f1,
    h4 := 0x510e527fade682d1, h5 := 0x9b05688c2b3e6c1f,
    h6 := 0x1f83d9abfb41bd6b, h7 := 0x5be0cd19137e2179 }

/-- `rotr64` in blake2-impl.h: `w` rotated right by `c` bits. The count is a `UInt64`, as Lean's
shifts ask, where the reference has `unsigned`. Meant for `0 < c < 64`; `G` uses 32, 24, 16, 63. -/
@[inline] def rotr64 (w c : UInt64) : UInt64 :=
  (w >>> c) ||| (w <<< (64 - c))

/-- `G(r,i,a,b,c,d)` in blake2b-ref.c, the same eight steps in the same order. In place of `r` and
`i` it takes the two words of `m` that the reference's G reads: `s0` is
`m[blake2b_sigma[r][2*i+0]]` and `s1` is `m[blake2b_sigma[r][2*i+1]]`. It returns the new `a`, `b`,
`c`, `d`. -/
@[inline] def G (s0 s1 a b c d : UInt64) : Quad :=
  let a := a + b + s0
  let d := rotr64 (d ^^^ a) 32
  let c := c + d
  let b := rotr64 (b ^^^ c) 24
  let a := a + b + s1
  let d := rotr64 (d ^^^ a) 16
  let c := c + d
  let b := rotr64 (b ^^^ c) 63
  ⟨a, b, c, d⟩

/-- `ROUND(r)` in blake2b-ref.c, the same eight calls of `G` on the same words of `v` in the same
order. In place of `r` it takes the round's sixteen message words: `s0` is `m[blake2b_sigma[r][0]]`,
`s1` is `m[blake2b_sigma[r][1]]`, up to `s15`. After them it takes `v`, which the reference changes
in place without a parameter for it, and it returns the new `v`. -/
@[inline] def ROUND (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : UInt64) (v : WorkVector) : WorkVector :=
  let ⟨v0, v4, v8, v12⟩ := G s0 s1 v.v0 v.v4 v.v8 v.v12
  let ⟨v1, v5, v9, v13⟩ := G s2 s3 v.v1 v.v5 v.v9 v.v13
  let ⟨v2, v6, v10, v14⟩ := G s4 s5 v.v2 v.v6 v.v10 v.v14
  let ⟨v3, v7, v11, v15⟩ := G s6 s7 v.v3 v.v7 v.v11 v.v15
  let ⟨v0, v5, v10, v15⟩ := G s8 s9 v0 v5 v10 v15
  let ⟨v1, v6, v11, v12⟩ := G s10 s11 v1 v6 v11 v12
  let ⟨v2, v7, v8, v13⟩ := G s12 s13 v2 v7 v8 v13
  let ⟨v3, v4, v9, v14⟩ := G s14 s15 v3 v4 v9 v14
  ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩

/-- The hashing state: the members `h`, `t` and `f` of `blake2b_state` in `blake2.h` of the BLAKE2
reference source code package. `t0` and `t1` are `t[0]` and `t[1]`, the low and the high word of the
count of bytes taken in, with 128 for a key block. `f0` and `f1` are `f[0]` and `f[1]`: `f0` marks
the last block; `f1` is 0 in every state that the definitions of `Hash.lean` and `Salted.lean` make
from `init0` (`Hash.lean`). `buf`, `buflen`, `outlen` and `last_node` are left out: blocks are read
from the message in place, callers pass the output length, and `last_node` would be 0. -/
structure State where
  h : ChainingValue
  t0 : UInt64
  t1 : UInt64
  f0 : UInt64
  f1 : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- The state after the block `m` is compressed into `S`. Adapted from `blake2b_compress` in
`blake2b-ref.c` of the BLAKE2 reference source code package. The block comes as its sixteen words,
so the loop over `load64` is in `MessageBlock.ofBytes` (`Hash.lean`); `v` is a structure in place of an
array; each `ROUND` is given the words of `m` in the order of its row of `blake2b_sigma`. Only `h`
changes: the caller advances the counter, and marks the last block, before the call. -/
def compress (S : State) (m : MessageBlock) : State :=
  let v : WorkVector :=
    { v0 := S.h.h0, v1 := S.h.h1, v2 := S.h.h2, v3 := S.h.h3,
      v4 := S.h.h4, v5 := S.h.h5, v6 := S.h.h6, v7 := S.h.h7,
      v8 := IV.h0,
      v9 := IV.h1,
      v10 := IV.h2,
      v11 := IV.h3,
      v12 := IV.h4 ^^^ S.t0,
      v13 := IV.h5 ^^^ S.t1,
      v14 := IV.h6 ^^^ S.f0,
      v15 := IV.h7 ^^^ S.f1 }
  let v := ROUND m.m0 m.m1 m.m2 m.m3 m.m4 m.m5 m.m6 m.m7
    m.m8 m.m9 m.m10 m.m11 m.m12 m.m13 m.m14 m.m15 v
  let v := ROUND m.m14 m.m10 m.m4 m.m8 m.m9 m.m15 m.m13 m.m6
    m.m1 m.m12 m.m0 m.m2 m.m11 m.m7 m.m5 m.m3 v
  let v := ROUND m.m11 m.m8 m.m12 m.m0 m.m5 m.m2 m.m15 m.m13
    m.m10 m.m14 m.m3 m.m6 m.m7 m.m1 m.m9 m.m4 v
  let v := ROUND m.m7 m.m9 m.m3 m.m1 m.m13 m.m12 m.m11 m.m14
    m.m2 m.m6 m.m5 m.m10 m.m4 m.m0 m.m15 m.m8 v
  let v := ROUND m.m9 m.m0 m.m5 m.m7 m.m2 m.m4 m.m10 m.m15
    m.m14 m.m1 m.m11 m.m12 m.m6 m.m8 m.m3 m.m13 v
  let v := ROUND m.m2 m.m12 m.m6 m.m10 m.m0 m.m11 m.m8 m.m3
    m.m4 m.m13 m.m7 m.m5 m.m15 m.m14 m.m1 m.m9 v
  let v := ROUND m.m12 m.m5 m.m1 m.m15 m.m14 m.m13 m.m4 m.m10
    m.m0 m.m7 m.m6 m.m3 m.m9 m.m2 m.m8 m.m11 v
  let v := ROUND m.m13 m.m11 m.m7 m.m14 m.m12 m.m1 m.m3 m.m9
    m.m5 m.m0 m.m15 m.m4 m.m8 m.m6 m.m2 m.m10 v
  let v := ROUND m.m6 m.m15 m.m14 m.m9 m.m11 m.m3 m.m0 m.m8
    m.m12 m.m2 m.m13 m.m7 m.m1 m.m4 m.m10 m.m5 v
  let v := ROUND m.m10 m.m2 m.m8 m.m4 m.m7 m.m6 m.m1 m.m5
    m.m15 m.m11 m.m9 m.m14 m.m3 m.m12 m.m13 m.m0 v
  let v := ROUND m.m0 m.m1 m.m2 m.m3 m.m4 m.m5 m.m6 m.m7
    m.m8 m.m9 m.m10 m.m11 m.m12 m.m13 m.m14 m.m15 v
  let v := ROUND m.m14 m.m10 m.m4 m.m8 m.m9 m.m15 m.m13 m.m6
    m.m1 m.m12 m.m0 m.m2 m.m11 m.m7 m.m5 m.m3 v
  { S with
    h :=
      { h0 := S.h.h0 ^^^ v.v0 ^^^ v.v8,
        h1 := S.h.h1 ^^^ v.v1 ^^^ v.v9,
        h2 := S.h.h2 ^^^ v.v2 ^^^ v.v10,
        h3 := S.h.h3 ^^^ v.v3 ^^^ v.v11,
        h4 := S.h.h4 ^^^ v.v4 ^^^ v.v12,
        h5 := S.h.h5 ^^^ v.v5 ^^^ v.v13,
        h6 := S.h.h6 ^^^ v.v6 ^^^ v.v14,
        h7 := S.h.h7 ^^^ v.v7 ^^^ v.v15 } }

end Run.Blake2b
