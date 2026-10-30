-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.Compress
/-!
# BLAKE2b, the whole function

The hash of a byte string, with or without a key, with a digest of 1 to 64 bytes. The compression
function is that of Compress.lean.

The definitions of sections 2 to 5 are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the
BLAKE2 reference source code package (reference C implementations), Copyright 2012, Samuel Neves.
The files' head offers "the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at your
option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0). The comment of each names what
it is adapted from and says what is changed; byteOrZero and ugetByte only read one byte for
load64Plain and load64 and have no counterpart in the reference.

The plan is the reference's: a state with the chaining value, the two words of the counter and the
two flags; the counter's step with its carry; the mark on the last block; the first state from the
parameter block; the loop of blake2b_update; blake2b_final. A message is read in place, so there is
no buffer.

Every definition is total, and none indexes with "!". No input makes the compiled code stop with an
error. A read with a machine-word index (uget) carries a proof that the index is inside the array.
-/
namespace Run.Blake2b

/-! ## 1. Indices in machine words

The compiled code reads arrays fastest with an index of type USize. Lean cannot prove that an
array's size fits a USize (it always does in a running program), so each fast read is guarded by a
test n.toUSize.toNat = n on the size n, and the other branch reads with natural numbers. The two
branches are proved equal (load64_eq_plain in WordsThm.lean). -/

/-- An index below a size that fits a machine word is itself unchanged by the passage to a machine
word. -/
theorem toNat_toUSize_add {n k : Nat} (j : Nat) (hn : n.toUSize.toNat = n) (h : k + j < n) :
    (k.toUSize + USize.ofNat j).toNat = k + j := by
  have hN : n < USize.size := by rw [← hn]; exact USize.toNat_lt_size _
  have hk : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  have hj : (USize.ofNat j).toNat = j := USize.toNat_ofNat_of_lt' (by omega)
  rw [USize.toNat_add, hk, hj]
  exact Nat.mod_eq_of_lt (by unfold USize.size at hN; omega)

/-- Such an index, as a machine word, is inside an array of that size. -/
theorem idx_lt {n k : Nat} (j : Nat) (hn : n.toUSize.toNat = n) (h : k + j < n) :
    (k.toUSize + USize.ofNat j).toNat < n := by
  rw [toNat_toUSize_add j hn h]; exact h

/-! ## 2. A block from bytes -/

/-- Byte `i` of `a` as a 64-bit word, or 0 if `i` is at or beyond the end of `a`. -/
@[inline] def byteOrZero (a : ByteArray) (i : Nat) : UInt64 :=
  if h : i < a.size then a[i].toUInt64 else 0

/-- The 64-bit word with the little-endian bytes `a[k]`, .., `a[k + 7]`. Adapted from the portable
branch of `load64` in `blake2-impl.h` of the BLAKE2 reference source code package, with an array and
an offset in place of the pointer. A byte at or beyond the end of `a` reads as 0; that gives a short
last block the zero padding that `blake2b_final` writes into `S->buf`. All indices are natural
numbers, so this form suits proofs and evaluation by Lean's kernel. -/
def load64Plain (a : ByteArray) (k : Nat) : UInt64 :=
  (byteOrZero a (k + 0) <<< 0) |||
  (byteOrZero a (k + 1) <<< 8) |||
  (byteOrZero a (k + 2) <<< 16) |||
  (byteOrZero a (k + 3) <<< 24) |||
  (byteOrZero a (k + 4) <<< 32) |||
  (byteOrZero a (k + 5) <<< 40) |||
  (byteOrZero a (k + 6) <<< 48) |||
  (byteOrZero a (k + 7) <<< 56)

/-- Byte `k + j` of `a` as a 64-bit word, read with a machine-word index. `hn` says that the size of
`a` fits in a machine word, and `h` that the byte is inside `a`. -/
@[inline] def ugetByte (a : ByteArray) (k j : Nat) (hn : a.size.toUSize.toNat = a.size)
    (h : k + j < a.size) : UInt64 :=
  (a.uget (k.toUSize + USize.ofNat j) (idx_lt j hn h)).toUInt64

/-- The same value as `load64Plain a k`, in the form that compiled code runs. Adapted from the
portable branch of `load64` in `blake2-impl.h` of the BLAKE2 reference source code package. If the
size of `a` fits in a machine word and all eight bytes are inside `a`, the bytes are read with
machine-word indices; in every other case the value is `load64Plain a k`. -/
@[inline] def load64 (a : ByteArray) (k : Nat) : UInt64 :=
  if hn : a.size.toUSize.toNat = a.size then
    if h : k + 7 < a.size then
      (ugetByte a k 0 hn (by omega) <<< 0) |||
      (ugetByte a k 1 hn (by omega) <<< 8) |||
      (ugetByte a k 2 hn (by omega) <<< 16) |||
      (ugetByte a k 3 hn (by omega) <<< 24) |||
      (ugetByte a k 4 hn (by omega) <<< 32) |||
      (ugetByte a k 5 hn (by omega) <<< 40) |||
      (ugetByte a k 6 hn (by omega) <<< 48) |||
      (ugetByte a k 7 hn h <<< 56)
    else load64Plain a k
  else load64Plain a k

/-- The block of 128 bytes of `a` that begins at byte `off`, as sixteen words. Adapted from the
first loop of `blake2b_compress` in `blake2b-ref.c` of the BLAKE2 reference source code package,
written out, with an array and an offset in place of the pointer. Bytes at or beyond the end of `a`
read as 0. -/
@[inline] def MessageBlock.ofBytes (a : ByteArray) (off : Nat) : MessageBlock :=
  { m0 := load64 a (off + 8 * 0),
    m1 := load64 a (off + 8 * 1),
    m2 := load64 a (off + 8 * 2),
    m3 := load64 a (off + 8 * 3),
    m4 := load64 a (off + 8 * 4),
    m5 := load64 a (off + 8 * 5),
    m6 := load64 a (off + 8 * 6),
    m7 := load64 a (off + 8 * 7),
    m8 := load64 a (off + 8 * 8),
    m9 := load64 a (off + 8 * 9),
    m10 := load64 a (off + 8 * 10),
    m11 := load64 a (off + 8 * 11),
    m12 := load64 a (off + 8 * 12),
    m13 := load64 a (off + 8 * 13),
    m14 := load64 a (off + 8 * 14),
    m15 := load64 a (off + 8 * 15) }

/-! ## 3. The state's small functions -/

/-- `S` with `inc` added to its two-word counter: `t0` wraps around modulo 2^64, and `t1` takes the
carry. Adapted from `blake2b_increment_counter` in `blake2b-ref.c` of the BLAKE2 reference source
code package. -/
@[inline] def incrementCounter (S : State) (inc : UInt64) : State :=
  let t0 := S.t0 + inc
  { S with t0 := t0, t1 := S.t1 + (if t0 < inc then (1 : UInt64) else 0) }

/-- `S` with the next block marked as the last one: `f0` becomes all ones, the reference's
`(uint64_t)-1`. Adapted from `blake2b_set_lastblock` in `blake2b-ref.c` of the BLAKE2 reference
source code package, for `S->last_node` = 0, so `f1` does not change. -/
@[inline] def setLastblock (S : State) : State :=
  { S with f0 := 0xffffffffffffffff }

/-- The state with `h` = `IV` and every other word 0. Adapted from `blake2b_init0` in
`blake2b-ref.c` of the BLAKE2 reference source code package. -/
@[inline] def init0 : State :=
  { h := IV, t0 := 0, t1 := 0, f0 := 0, f1 := 0 }

/-- The first state for a parameter block whose eight words `load64 (p + 8 * i)` are `p0`, .., `p7`.
Adapted from `blake2b_init_param` in `blake2b-ref.c` of the BLAKE2 reference source code package,
with the loop written out. As there, the parameter block is not checked: a caller that produces a
digest checks that its length is from 1 to 64. -/
@[inline] def initParam (p0 p1 p2 p3 p4 p5 p6 p7 : UInt64) : State :=
  let S := init0
  { S with
    h :=
      { h0 := S.h.h0 ^^^ p0,
        h1 := S.h.h1 ^^^ p1,
        h2 := S.h.h2 ^^^ p2,
        h3 := S.h.h3 ^^^ p3,
        h4 := S.h.h4 ^^^ p4,
        h5 := S.h.h5 ^^^ p5,
        h6 := S.h.h6 ^^^ p6,
        h7 := S.h.h7 ^^^ p7 } }

/-- `load64` of the first eight bytes of the `blake2b_param` (`blake2.h` of the BLAKE2 reference
source code package) that `blake2b_init` and `blake2b_init_key` in `blake2b-ref.c` fill in:
`digest_length` = `outlen`, `key_length` = `keylen`, `fanout` = 1, `depth` = 1, and the four zero
bytes of `leaf_length`. Each argument must be below 256 to fit its byte, and is not cut down to one.
The functions that return a digest (`blake2b`, `blake2bSalted`, `Fmt.finish`) return the empty array
for an `outlen` above 64 or a key of more than 64 bytes. -/
@[inline] def parameterBlockFirstWord (keylen outlen : Nat) : UInt64 :=
  (outlen.toUInt64 <<< 0) |||
  (keylen.toUInt64 <<< 8) |||
  ((1 : UInt64) <<< 16) |||
  ((1 : UInt64) <<< 24)

/-- The state after `blake2b_init_param` on the `blake2b_param` that `blake2b_init` (for
`keylen` = 0) or `blake2b_init_key` in `blake2b-ref.c` of the BLAKE2 reference source code package
fills in. All bytes of that parameter block after the first eight are 0. The lengths are not
checked, and the key block that `blake2b_init_key` goes on to pass to `blake2b_update` is left to
the caller. -/
@[inline] def firstState (keylen outlen : Nat) : State :=
  initParam (parameterBlockFirstWord keylen outlen) 0 0 0 0 0 0 0

/-! ## 4. A whole message -/

/-- The state after the `n` blocks `blk i`, .., `blk (i + n - 1)` are compressed into `S`. Before
each block the counter moves by 128, the reference's `BLAKE2B_BLOCKBYTES`. Adapted from the two
steps `blake2b_increment_counter` and `blake2b_compress` in the loop of `blake2b_update` in
`blake2b-ref.c` of the BLAKE2 reference source code package, with a block number in place of the
pointer. None of these blocks may be the last block of the message. -/
@[specialize] def updateBlocks (blk : Nat → MessageBlock) : (n i : Nat) → State → State
  | 0, _, S => S
  | n + 1, i, S => updateBlocks blk n (i + 1) (compress (incrementCounter S 128) (blk i))

/-- The state after the last block is compressed. Adapted from `blake2b_final` in `blake2b-ref.c` of
the BLAKE2 reference source code package, from its call of `blake2b_increment_counter` up to and
including that of `blake2b_compress`. `buflen`, at most 128, is `S->buflen`, and `buf` is `S->buf`
as words, with zero bytes from `buflen` on. `S.f0` must be 0: the reference returns -1 for any other
state; that test is left out. -/
@[inline] def finalBlock (S : State) (buf : MessageBlock) (buflen : Nat) : State :=
  compress (setLastblock (incrementCounter S buflen.toUInt64)) buf

/-- The state after a whole message of `inlen` bytes, from `S` with an empty buffer and `S.f0` = 0.
Adapted from `blake2b_update`, and from `blake2b_final` up to and including its `blake2b_compress`,
in `blake2b-ref.c` of the BLAKE2 reference source code package. `blk j` is block `j` of the message,
the last one zero-filled; `blk 0` is all zero if `inlen` = 0. `blake2b_update` tests before each
block that more than 128 bytes remain; here the number of blocks that pass, `(inlen - 1) / 128`, is
worked out beforehand. The other 1 to 128 bytes (none if `inlen` = 0) are the last block. -/
@[specialize] def message (blk : Nat → MessageBlock) (inlen : Nat) (S : State) : State :=
  let n := (inlen - 1) / 128
  finalBlock (updateBlocks blk n 0 S) (blk n) (inlen - 128 * n)

/-- The state at the end of the one-call function `blake2b`, up to and including the compression in
`blake2b_final`. Adapted from `blake2b` and `blake2b_init_key` in `blake2b-ref.c` of the BLAKE2
reference source code package, without their checks: meant for a `key` of at most 64 bytes (empty
means no key) and `outlen` from 1 to 64. There is no buffer. The zero-filled key block, which waits
in `S->buf` there, is compressed as `blake2b_update` does it if `data` has bytes, and as
`blake2b_final` does it, as the last block, if it has none. -/
def state (key data : ByteArray) (outlen : Nat) : State :=
  let S := firstState key.size outlen
  if key.size > 0 then
    if data.size > 0 then
      message (fun j => MessageBlock.ofBytes data (128 * j)) data.size
        (updateBlocks (fun _ => MessageBlock.ofBytes key 0) 1 0 S)
    else
      finalBlock S (MessageBlock.ofBytes key 0) 128
  else
    message (fun j => MessageBlock.ofBytes data (128 * j)) data.size S

/-! ## 5. The digest -/

/-- `o` with the eight little-endian bytes of `x` added at its end. Adapted from the portable branch
of `store64` in `blake2-impl.h` of the BLAKE2 reference source code package, with a growing array in
place of the pointer. -/
@[inline] def store64 (o : ByteArray) (x : UInt64) : ByteArray :=
  let o := o.push (x >>> 0).toUInt8
  let o := o.push (x >>> 8).toUInt8
  let o := o.push (x >>> 16).toUInt8
  let o := o.push (x >>> 24).toUInt8
  let o := o.push (x >>> 32).toUInt8
  let o := o.push (x >>> 40).toUInt8
  let o := o.push (x >>> 48).toUInt8
  o.push (x >>> 56).toUInt8

/-- The 64 bytes of the eight words of `s`, each word little-endian. Adapted from the loop over
`store64` in `blake2b_final` in `blake2b-ref.c` of the BLAKE2 reference source code package, written
out: the result is that function's local `buffer` for `S->h` = `s`. -/
def ChainingValue.bytes64 (s : ChainingValue) : ByteArray :=
  let buffer := ByteArray.emptyWithCapacity 64
  let buffer := store64 buffer s.h0
  let buffer := store64 buffer s.h1
  let buffer := store64 buffer s.h2
  let buffer := store64 buffer s.h3
  let buffer := store64 buffer s.h4
  let buffer := store64 buffer s.h5
  let buffer := store64 buffer s.h6
  store64 buffer s.h7

/-- The first `outlen` bytes of `s.bytes64`: what `blake2b_final` in `blake2b-ref.c` of the BLAKE2
reference source code package copies to `out`. For `outlen` above 64 the result is the 64 bytes;
nothing beyond the buffer is read. -/
def ChainingValue.bytes (s : ChainingValue) (outlen : Nat) : ByteArray :=
  s.bytes64.extract 0 outlen

/-- The BLAKE2b digest of `data`, `outlen` bytes long, under `key` if `key` is not empty. Adapted
from the one-call function `blake2b` in `blake2b-ref.c` of the BLAKE2 reference source code package.
Where that function returns -1 (`outlen` is 0 or above 64, its `BLAKE2B_OUTBYTES`, or `key` has more
than 64 bytes, its `BLAKE2B_KEYBYTES`) the result is the empty array. Its tests for null pointers
have no counterpart. -/
def blake2b (key data : ByteArray) (outlen : Nat) : ByteArray :=
  if outlen = 0 ∨ outlen > 64 then ByteArray.empty
  else if key.size > 64 then ByteArray.empty
  else (state key data outlen).h.bytes outlen

end Run.Blake2b
