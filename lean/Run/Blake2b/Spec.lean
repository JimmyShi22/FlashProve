-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-!
The plain definition of BLAKE2b. Theorems on faster functions are stated against `blake2b` below.

Adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the BLAKE2 reference source code package,
Copyright 2012 Samuel Neves, taken under CC0 1.0 Universal. Each comment names the counterpart in
the reference and says what is changed. That this file says what the reference says is not a
theorem: a person compares the two texts, and the tests at the end of the file support it. No test
of this library reaches the carry in `blake2b_increment_counter`: each starts this definition at the
count 0, and none hashes 2^64 bytes. That this step is the reference's rests on the comparison only.
That the reference computes the BLAKE2b of RFC 7693 is not a matter of this library.

How C is written here: a function that changes `*S` returns the new state; `return -1` is `none`; a
pointer is an array with an offset, a pointer with a length is an array; an array that C leaves
uninitialised starts as zeros. Checks for NULL and `secure_zero_memory` have no counterpart.
-/

namespace Run.Blake2b.Spec

/-! ### string.h -/

/-- C's `memcpy( dst + doff, src + soff, n )`: the new contents of `dst`. The size of `dst` is kept
if `doff + n ≤ dst.size` and `soff + n ≤ src.size`, which C requires of the caller. -/
def memcpy (dst : Array UInt8) (doff : Nat) (src : Array UInt8) (soff n : Nat) : Array UInt8 :=
  dst.extract 0 doff ++ src.extract soff (soff + n) ++ dst.extract (doff + n) dst.size

/-- C's `memset( dst + doff, c, n )`: the new contents of `dst`. The size of `dst` is kept if
`doff + n ≤ dst.size`, which C requires of the caller. -/
def memset (dst : Array UInt8) (doff : Nat) (c : UInt8) (n : Nat) : Array UInt8 :=
  dst.extract 0 doff ++ Array.replicate n c ++ dst.extract (doff + n) dst.size

/-! ### blake2.h -/

/-- `BLAKE2B_BLOCKBYTES` of `enum blake2b_constant`. -/
abbrev BLAKE2B_BLOCKBYTES : Nat := 128

/-- `BLAKE2B_OUTBYTES` of `enum blake2b_constant`. -/
abbrev BLAKE2B_OUTBYTES : Nat := 64

/-- `BLAKE2B_KEYBYTES` of `enum blake2b_constant`. -/
abbrev BLAKE2B_KEYBYTES : Nat := 64

/-- `BLAKE2B_SALTBYTES` of `enum blake2b_constant`. -/
abbrev BLAKE2B_SALTBYTES : Nat := 16

/-- `BLAKE2B_PERSONALBYTES` of `enum blake2b_constant`. -/
abbrev BLAKE2B_PERSONALBYTES : Nat := 16

/-- `blake2b_state`. The arrays `t[2]` and `f[2]` are the fields `t0`, `t1`, `f0`, `f1`. `h` holds 8
words and `buf` holds `BLAKE2B_BLOCKBYTES` bytes. The two `size_t` lengths are natural numbers. -/
structure blake2b_state where
  h : Array UInt64
  t0 : UInt64
  t1 : UInt64
  f0 : UInt64
  f1 : UInt64
  buf : Array UInt8
  buflen : Nat
  outlen : Nat
  last_node : UInt8

/-- `blake2b_param`, a packed struct of 64 bytes, as the array of these bytes. A field's name is the
offset of its first byte; the comment after a field in blake2.h gives the offset after its last. -/
abbrev blake2b_param : Type := Array UInt8

namespace blake2b_param

/-- Offset of `uint8_t digest_length`. -/
abbrev digest_length : Nat := 0

/-- Offset of `uint8_t key_length`. -/
abbrev key_length : Nat := 1

/-- Offset of `uint8_t fanout`. -/
abbrev fanout : Nat := 2

/-- Offset of `uint8_t depth`. -/
abbrev depth : Nat := 3

/-- Offset of `uint32_t leaf_length`. -/
abbrev leaf_length : Nat := 4

/-- Offset of `uint32_t node_offset`. -/
abbrev node_offset : Nat := 8

/-- Offset of `uint32_t xof_length`. -/
abbrev xof_length : Nat := 12

/-- Offset of `uint8_t node_depth`. -/
abbrev node_depth : Nat := 16

/-- Offset of `uint8_t inner_length`. -/
abbrev inner_length : Nat := 17

/-- Offset of `uint8_t reserved[14]`. -/
abbrev reserved : Nat := 18

/-- Offset of `uint8_t salt[BLAKE2B_SALTBYTES]`. -/
abbrev salt : Nat := 32

/-- Offset of `uint8_t personal[BLAKE2B_PERSONALBYTES]`. -/
abbrev personal : Nat := 48

end blake2b_param

/-! ### blake2-impl.h -/

/-- `load64`, the branch that does not assume a little-endian machine. `p[k]` is `src[off + k]`. -/
def load64 (src : Array UInt8) (off : Nat) : UInt64 :=
  ((src[off + 0]!).toUInt64 <<<  0) |||
  ((src[off + 1]!).toUInt64 <<<  8) |||
  ((src[off + 2]!).toUInt64 <<< 16) |||
  ((src[off + 3]!).toUInt64 <<< 24) |||
  ((src[off + 4]!).toUInt64 <<< 32) |||
  ((src[off + 5]!).toUInt64 <<< 40) |||
  ((src[off + 6]!).toUInt64 <<< 48) |||
  ((src[off + 7]!).toUInt64 <<< 56)

/-- `store32`, the branch that does not assume a little-endian machine: the new contents of `dst`.
`p[k]` is `dst[off + k]`. -/
def store32 (dst : Array UInt8) (off : Nat) (w : UInt32) : Array UInt8 :=
  let dst := dst.set! (off + 0) (w >>>  0).toUInt8
  let dst := dst.set! (off + 1) (w >>>  8).toUInt8
  let dst := dst.set! (off + 2) (w >>> 16).toUInt8
  let dst := dst.set! (off + 3) (w >>> 24).toUInt8
  dst

/-- `store64`, the branch that does not assume a little-endian machine: the new contents of `dst`.
`p[k]` is `dst[off + k]`. -/
def store64 (dst : Array UInt8) (off : Nat) (w : UInt64) : Array UInt8 :=
  let dst := dst.set! (off + 0) (w >>>  0).toUInt8
  let dst := dst.set! (off + 1) (w >>>  8).toUInt8
  let dst := dst.set! (off + 2) (w >>> 16).toUInt8
  let dst := dst.set! (off + 3) (w >>> 24).toUInt8
  let dst := dst.set! (off + 4) (w >>> 32).toUInt8
  let dst := dst.set! (off + 5) (w >>> 40).toUInt8
  let dst := dst.set! (off + 6) (w >>> 48).toUInt8
  let dst := dst.set! (off + 7) (w >>> 56).toUInt8
  dst

/-- `rotr64`. The count `c` has the type of `w`, as Lean's shifts require. This file calls it only
with 32, 24, 16 and 63; for 0 and 64 C leaves the value undefined. -/
def rotr64 (w : UInt64) (c : UInt64) : UInt64 :=
  (w >>> c) ||| (w <<< (64 - c))

/-! ### blake2b-ref.c -/

/-- `blake2b_IV`. -/
def blake2b_IV : Array UInt64 :=
  #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- `blake2b_sigma`. The entries serve only as indices, so they are natural numbers. -/
def blake2b_sigma : Array (Array Nat) :=
  #[#[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
    #[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
    #[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
    #[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
    #[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
    #[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
    #[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
    #[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
    #[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
    #[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0],
    #[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
    #[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3]]

/-- `blake2b_set_lastnode`. `(uint64_t)-1` is written out. -/
def blake2b_set_lastnode (S : blake2b_state) : blake2b_state :=
  { S with f1 := 0xffffffffffffffff }

/-- `blake2b_is_lastblock`. -/
def blake2b_is_lastblock (S : blake2b_state) : Bool :=
  S.f0 != 0

/-- `blake2b_set_lastblock`. `(uint64_t)-1` is written out. No function of this file sets
`last_node` to anything but 0, so on the way through `blake2b` the first line changes nothing. -/
def blake2b_set_lastblock (S : blake2b_state) : blake2b_state :=
  let S := if S.last_node != 0 then blake2b_set_lastnode S else S
  { S with f0 := 0xffffffffffffffff }

/-- `blake2b_increment_counter`. The comparison, which is 1 or 0 in C, is an `if`. -/
def blake2b_increment_counter (S : blake2b_state) (inc : UInt64) : blake2b_state :=
  let S := { S with t0 := S.t0 + inc }
  { S with t1 := S.t1 + (if S.t0 < inc then (1 : UInt64) else (0 : UInt64)) }

/-- `blake2b_init0`. It takes no state, since the `memset` overwrites all of `*S`. -/
def blake2b_init0 : blake2b_state :=
  let S : blake2b_state :=
    { h := Array.replicate 8 0, t0 := 0, t1 := 0, f0 := 0, f1 := 0,
      buf := Array.replicate BLAKE2B_BLOCKBYTES 0, buflen := 0, outlen := 0, last_node := 0 }
  { S with h := (List.range 8).foldl (fun (h : Array UInt64) i => h.set! i blake2b_IV[i]!) S.h }

/-- `blake2b_init_param`. It always returns 0, so the result is the state. The cast of `P` to bytes
changes nothing here. Like the reference, it does not check `digest_length`. -/
def blake2b_init_param (P : blake2b_param) : blake2b_state :=
  let p : Array UInt8 := P
  let S := blake2b_init0
  let h := (List.range 8).foldl
    (fun (h : Array UInt64) i => h.set! i (h[i]! ^^^ load64 p (8 * i))) S.h
  let S := { S with h := h }
  { S with outlen := (P[blake2b_param.digest_length]!).toNat }

/-- `blake2b_init`. -/
def blake2b_init (outlen : Nat) : Option blake2b_state :=
  let P : blake2b_param := Array.replicate 64 0
  if outlen = 0 ∨ outlen > BLAKE2B_OUTBYTES then none else
  let P := P.set! blake2b_param.digest_length outlen.toUInt8
  let P := P.set! blake2b_param.key_length 0
  let P := P.set! blake2b_param.fanout 1
  let P := P.set! blake2b_param.depth 1
  let P := store32 P blake2b_param.leaf_length 0
  let P := store32 P blake2b_param.node_offset 0
  let P := store32 P blake2b_param.xof_length 0
  let P := P.set! blake2b_param.node_depth 0
  let P := P.set! blake2b_param.inner_length 0
  let P := memset P blake2b_param.reserved 0 14
  let P := memset P blake2b_param.salt 0 BLAKE2B_SALTBYTES
  let P := memset P blake2b_param.personal 0 BLAKE2B_PERSONALBYTES
  some (blake2b_init_param P)

/-- The macro `G`. The macro reads `m` and changes entries of `v` in place; here `m` and `v` are
arguments, `a`, `b`, `c`, `d` are the indices of the four entries, and the result is the new `v`. -/
def G (m v : Array UInt64) (r i a b c d : Nat) : Array UInt64 :=
  let v := v.set! a (v[a]! + v[b]! + m[blake2b_sigma[r]![2 * i + 0]!]!)
  let v := v.set! d (rotr64 (v[d]! ^^^ v[a]!) 32)
  let v := v.set! c (v[c]! + v[d]!)
  let v := v.set! b (rotr64 (v[b]! ^^^ v[c]!) 24)
  let v := v.set! a (v[a]! + v[b]! + m[blake2b_sigma[r]![2 * i + 1]!]!)
  let v := v.set! d (rotr64 (v[d]! ^^^ v[a]!) 16)
  let v := v.set! c (v[c]! + v[d]!)
  let v := v.set! b (rotr64 (v[b]! ^^^ v[c]!) 63)
  v

/-- The macro `ROUND`, with `m` and `v` as arguments and the new `v` as the result. -/
def ROUND (m v : Array UInt64) (r : Nat) : Array UInt64 :=
  let v := G m v r 0  0  4  8 12
  let v := G m v r 1  1  5  9 13
  let v := G m v r 2  2  6 10 14
  let v := G m v r 3  3  7 11 15
  let v := G m v r 4  0  5 10 15
  let v := G m v r 5  1  6 11 12
  let v := G m v r 6  2  7  8 13
  let v := G m v r 7  3  4  9 14
  v

/-- `blake2b_compress`. `block` is the array of the `BLAKE2B_BLOCKBYTES` bytes at the pointer. -/
def blake2b_compress (S : blake2b_state) (block : Array UInt8) : blake2b_state :=
  let m : Array UInt64 := Array.replicate 16 0
  let v : Array UInt64 := Array.replicate 16 0
  let m := (List.range 16).foldl (fun (m : Array UInt64) i => m.set! i (load64 block (i * 8))) m
  let v := (List.range 8).foldl (fun (v : Array UInt64) i => v.set! i S.h[i]!) v
  let v := v.set!  8 blake2b_IV[0]!
  let v := v.set!  9 blake2b_IV[1]!
  let v := v.set! 10 blake2b_IV[2]!
  let v := v.set! 11 blake2b_IV[3]!
  let v := v.set! 12 (blake2b_IV[4]! ^^^ S.t0)
  let v := v.set! 13 (blake2b_IV[5]! ^^^ S.t1)
  let v := v.set! 14 (blake2b_IV[6]! ^^^ S.f0)
  let v := v.set! 15 (blake2b_IV[7]! ^^^ S.f1)
  let v := ROUND m v 0
  let v := ROUND m v 1
  let v := ROUND m v 2
  let v := ROUND m v 3
  let v := ROUND m v 4
  let v := ROUND m v 5
  let v := ROUND m v 6
  let v := ROUND m v 7
  let v := ROUND m v 8
  let v := ROUND m v 9
  let v := ROUND m v 10
  let v := ROUND m v 11
  let h := (List.range 8).foldl
    (fun (h : Array UInt64) i => h.set! i (h[i]! ^^^ v[i]! ^^^ v[i + 8]!)) S.h
  { S with h := h }

/-- The `while` loop of `blake2b_update`: the state, `in` and `inlen` after it. The first number
bounds the iterations, so that Lean accepts the recursion. Each iteration takes
`BLAKE2B_BLOCKBYTES` from `inlen`, so a bound of `inlen` or more never ends the loop early. -/
def blake2b_update_while (pin : Array UInt8) :
    Nat → blake2b_state → Nat → Nat → blake2b_state × Nat × Nat
  | 0, S, in_, inlen => (S, in_, inlen)
  | bound + 1, S, in_, inlen =>
    if inlen > BLAKE2B_BLOCKBYTES then
      let S := blake2b_increment_counter S BLAKE2B_BLOCKBYTES.toUInt64
      let S := blake2b_compress S (pin.extract in_ (in_ + BLAKE2B_BLOCKBYTES))
      blake2b_update_while pin bound S (in_ + BLAKE2B_BLOCKBYTES) (inlen - BLAKE2B_BLOCKBYTES)
    else
      (S, in_, inlen)

/-- `blake2b_update`. It always returns 0, so the result is the state. `inlen` starts as the size of
`pin`. The pointer `in` is the offset `in_` into `pin` (`in` is a keyword of Lean). `w` holds the
three variables that the inner `if` changes. -/
def blake2b_update (S : blake2b_state) (pin : Array UInt8) : blake2b_state :=
  let inlen := pin.size
  let in_ : Nat := 0
  if inlen > 0 then
    let left := S.buflen
    let fill := BLAKE2B_BLOCKBYTES - left
    let w : blake2b_state × Nat × Nat :=
      if inlen > fill then
        let S := { S with buflen := 0 }
        let S := { S with buf := memcpy S.buf left pin in_ fill }
        let S := blake2b_increment_counter S BLAKE2B_BLOCKBYTES.toUInt64
        let S := blake2b_compress S S.buf
        let in_ := in_ + fill
        let inlen := inlen - fill
        blake2b_update_while pin inlen S in_ inlen
      else
        (S, in_, inlen)
    let S := w.1
    let in_ := w.2.1
    let inlen := w.2.2
    let S := { S with buf := memcpy S.buf S.buflen pin in_ inlen }
    { S with buflen := S.buflen + inlen }
  else
    S

/-- `blake2b_init_key`. In the reference it comes right after `blake2b_init`; Lean needs it after
`blake2b_update`, which it calls. `keylen` is the size of `key`. `blake2b_init_param` cannot fail,
so the check of its result has no counterpart. -/
def blake2b_init_key (outlen : Nat) (key : Array UInt8) : Option blake2b_state :=
  let keylen := key.size
  let P : blake2b_param := Array.replicate 64 0
  if outlen = 0 ∨ outlen > BLAKE2B_OUTBYTES then none else
  if keylen = 0 ∨ keylen > BLAKE2B_KEYBYTES then none else
  let P := P.set! blake2b_param.digest_length outlen.toUInt8
  let P := P.set! blake2b_param.key_length keylen.toUInt8
  let P := P.set! blake2b_param.fanout 1
  let P := P.set! blake2b_param.depth 1
  let P := store32 P blake2b_param.leaf_length 0
  let P := store32 P blake2b_param.node_offset 0
  let P := store32 P blake2b_param.xof_length 0
  let P := P.set! blake2b_param.node_depth 0
  let P := P.set! blake2b_param.inner_length 0
  let P := memset P blake2b_param.reserved 0 14
  let P := memset P blake2b_param.salt 0 BLAKE2B_SALTBYTES
  let P := memset P blake2b_param.personal 0 BLAKE2B_PERSONALBYTES
  let S := blake2b_init_param P
  let block : Array UInt8 := Array.replicate BLAKE2B_BLOCKBYTES 0
  let block := memset block 0 0 BLAKE2B_BLOCKBYTES
  let block := memcpy block 0 key 0 keylen
  let S := blake2b_update S block
  some S

/-- `blake2b_final`: the `S->outlen` bytes that it copies to `out`. The state after the call is not
returned, since `blake2b` does not use it. -/
def blake2b_final (S : blake2b_state) (outlen : Nat) : Option (Array UInt8) :=
  let buffer : Array UInt8 := Array.replicate BLAKE2B_OUTBYTES 0
  if outlen < S.outlen then none else
  if blake2b_is_lastblock S then none else
  let S := blake2b_increment_counter S S.buflen.toUInt64
  let S := blake2b_set_lastblock S
  let S := { S with buf := memset S.buf S.buflen 0 (BLAKE2B_BLOCKBYTES - S.buflen) }
  let S := blake2b_compress S S.buf
  let buffer :=
    (List.range 8).foldl (fun (buffer : Array UInt8) i => store64 buffer (8 * i) S.h[i]!) buffer
  some (buffer.extract 0 S.outlen)

/-- The one-call function `blake2b` of blake2b-ref.c: the `outlen` bytes written to `out`. `data`
is `in` with `inlen`, `key` is `key` with `keylen`. Where the reference returns -1 the result is
`#[]`. It ignores the result of `blake2b_final`, which is never -1 at this call. -/
def blake2b (key data : Array UInt8) (outlen : Nat) : Array UInt8 :=
  let keylen := key.size
  if outlen = 0 ∨ outlen > BLAKE2B_OUTBYTES then #[] else
  if keylen > BLAKE2B_KEYBYTES then #[] else
  match (if keylen > 0 then blake2b_init_key outlen key else blake2b_init outlen) with
  | none => #[]
  | some S =>
    let S := blake2b_update S data
    (blake2b_final S outlen).getD #[]

/-! ### Tests -/

/-- The bytes as lower-case hexadecimal digits, two for each byte. Used only by the tests. -/
def hex (a : Array UInt8) : String :=
  a.foldl (fun (s : String) x =>
    (s.push (Nat.digitChar (x.toNat / 16))).push (Nat.digitChar (x.toNat % 16))) ""

/-- The bytes `(uint8_t)0, .., (uint8_t)(n - 1)`, with which the self-test at the end of
blake2b-ref.c fills `key` and `buf`. Used only by the tests. -/
def selftest_bytes (n : Nat) : Array UInt8 :=
  (Array.range n).map fun i => i.toUInt8

/-- One case of the part "Test streaming API" of that self-test: the keyed digest of `i` bytes fed
in pieces of `step` bytes. Its `while` loop has `i / step` iterations. Used only by the tests. -/
def selftest_streaming (step i : Nat) : Option (Array UInt8) :=
  let buf := selftest_bytes i
  match blake2b_init_key BLAKE2B_OUTBYTES (selftest_bytes BLAKE2B_KEYBYTES) with
  | none => none
  | some S =>
    let S := (List.range (i / step)).foldl
      (fun (S : blake2b_state) k => blake2b_update S (buf.extract (k * step) (k * step + step))) S
    let S := blake2b_update S (buf.extract (i / step * step) i)
    blake2b_final S BLAKE2B_OUTBYTES

-- Expected values from the arrays blake2b_kat and blake2b_keyed_kat of blake2-kat.h in libb2
-- 0.98.1, written in 2012 by Samuel Neves, CC0 1.0 Universal. Entry i is the digest of the bytes
-- 0, .., i - 1; the key of blake2b_keyed_kat is the bytes 0, .., 63.

-- blake2b_kat, entries 0, 1, 127, 128, 129, 255.
#guard hex (blake2b #[] (selftest_bytes 0) 64) ==
  "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419" ++
  "d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"
#guard hex (blake2b #[] (selftest_bytes 1) 64) ==
  "2fa3f686df876995167e7c2e5d74c4c7b6e48f8068fe0e44208344d480f7904c" ++
  "36963e44115fe3eb2a3ac8694c28bcb4f5a0f3276f2e79487d8219057a506e4b"
#guard hex (blake2b #[] (selftest_bytes 127) 64) ==
  "b6292669ccd38d5f01caae96ba272c76a879a45743afa0725d83b9ebb26665b7" ++
  "31f1848c52f11972b6644f554c064fa90780dbbbf3a89d4fc31f67df3e5857ef"
#guard hex (blake2b #[] (selftest_bytes 128) 64) ==
  "2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e" ++
  "8ccff439ac333b040f19b0c4ddd11a61e24ac1fe0f10a039806c5dcc0da3d115"
#guard hex (blake2b #[] (selftest_bytes 129) 64) ==
  "f59711d44a031d5f97a9413c065d1e614c417ede998590325f49bad2fd444d3e" ++
  "4418be19aec4e11449ac1a57207898bc57d76a1bcf3566292c20c683a5c4648f"
#guard hex (blake2b #[] (selftest_bytes 255) 64) ==
  "5b21c5fd8868367612474fa2e70e9cfa2201ffeee8fafab5797ad58fefa17c9b" ++
  "5b107da4a3db6320baaf2c8617d5a51df914ae88da3867c2d41f0cc14fa67928"

-- blake2b_keyed_kat, entries 0, 1, 127, 128, 129, 255.
#guard hex (blake2b (selftest_bytes 64) (selftest_bytes 0) 64) ==
  "10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786" ++
  "b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568"
#guard hex (blake2b (selftest_bytes 64) (selftest_bytes 1) 64) ==
  "961f6dd1e4dd30f63901690c512e78e4b45e4742ed197c3c5e45c549fd25f2e4" ++
  "187b0bc9fe30492b16b0d0bc4ef9b0f34c7003fac09a5ef1532e69430234cebd"
#guard hex (blake2b (selftest_bytes 64) (selftest_bytes 127) 64) ==
  "76d2d819c92bce55fa8e092ab1bf9b9eab237a25267986cacf2b8ee14d214d73" ++
  "0dc9a5aa2d7b596e86a1fd8fa0804c77402d2fcd45083688b218b1cdfa0dcbcb"
#guard hex (blake2b (selftest_bytes 64) (selftest_bytes 128) 64) ==
  "72065ee4dd91c2d8509fa1fc28a37c7fc9fa7d5b3f8ad3d0d7a25626b57b1b44" ++
  "788d4caf806290425f9890a3a2a35a905ab4b37acfd0da6e4517b2525c9651e4"
#guard hex (blake2b (selftest_bytes 64) (selftest_bytes 129) 64) ==
  "64475dfe7600d7171bea0b394e27c9b00d8e74dd1e416a79473682ad3dfdbb70" ++
  "6631558055cfc8a40e07bd015a4540dcdea15883cbbf31412df1de1cd4152b91"
#guard hex (blake2b (selftest_bytes 64) (selftest_bytes 255) 64) ==
  "142709d62e28fcccd0af97fad0f8465b971e82201dc51070faa0372aa43e9248" ++
  "4be1c1e73ba10906d5d1853db6a4106e0a7bf9800d373d6dee2d46d62ef2a461"

-- The three bytes "abc" without a key: the example of RFC 7693, Appendix A; not from blake2-kat.h.
-- blake2b-ref.c gives the same 64 bytes.
#guard hex (blake2b #[] #[0x61, 0x62, 0x63] 64) ==
  "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
  "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"

-- The bytes 0, .., 255, 0, .. (1000 bytes) without a key: one block through the buffer and six
-- turns of the loop in blake2b_update. The expected value was computed with blake2b-ref.c itself.
#guard hex (blake2b #[] (selftest_bytes 1000) 64) ==
  "9fe687126e6566313081b43167cbfa0b4f721b45a5afd4076af327765d63a616" ++
  "478ffbd1cd5fbe4033e8638b8bcf8de6b3978b54a30f1d9d8d68fbe66c2b74cf"

-- The digest length enters the parameter block: a digest of 32 bytes is not the first half of the
-- digest of 64 bytes.
#guard (blake2b #[] #[0x61, 0x62, 0x63] 32).size == 32
#guard blake2b #[] #[0x61, 0x62, 0x63] 32 != (blake2b #[] #[0x61, 0x62, 0x63] 64).extract 0 32

-- Where the reference returns -1: a digest length of 0 or of 65, a key of 65 bytes.
#guard blake2b #[] #[0x61, 0x62, 0x63] 0 == #[]
#guard blake2b #[] #[0x61, 0x62, 0x63] 65 == #[]
#guard blake2b (selftest_bytes 65) #[0x61, 0x62, 0x63] 64 == #[]

-- Fed in pieces, a message has the digest of the one call. Pieces shorter than a block go through
-- the buffer only; in the one call the 1000 bytes take several iterations of the while loop.
#guard [1, 7, 64, 127].all fun step => [0, 1, 128, 129, 255, 1000].all fun i =>
  selftest_streaming step i ==
    some (blake2b (selftest_bytes BLAKE2B_KEYBYTES) (selftest_bytes i) BLAKE2B_OUTBYTES)

end Run.Blake2b.Spec
