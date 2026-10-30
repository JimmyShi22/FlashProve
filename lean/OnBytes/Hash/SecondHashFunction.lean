-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Hash/SecondHashFunction.lean: the second hash function of the format page (docs/format/FORMAT.md,
R15.3), on lists of 32-bit words.

Some digests are made by this hash and not by the format's hash H (OnBytes/Hash/H.lean). The format
page calls it the earlier hash. It specifies those in the statement's item `request` (R15.3 to
R15.6; OnBytes/Proof/RequestItem.lean) and counts this hash as a second assumption beside that on H.

The hash runs the compression function of BLAKE2b from the first state of BLAKE2b with 64 bytes of
output and no key. It differs from BLAKE2b in the counter: the high word of the counter, which is 0
in BLAKE2b on a message of fewer than 2^64 bytes, holds a number that says what the hash is used
for, and the length of the list. So under a number from 1 to 2^32 - 1 no call of the compression
function here is a call of BLAKE2b on such a message. C++: cp_verify calls earlier_hash_h_state and
earlier_hash_h_digest in verifier/src/vf_earlier_hash.h and TH in vf_common.h; blocks/hash/older.h
has the same hash (Older::list_state, Older::list_digest, Older::tree_hash). Older::list_state stops
the program at a list of 2^32 words or more and at a number whose low 16 bits are 160 or more.

A list of 32-bit words is kept here as its bytes, four for a word, lowest byte first.

Main definitions: `secondHashFunctionState`, `secondHashFunction` (the hash of a list under a number), `secondHashFunctionTree` (the tree
hash of a long list), `textWords`, `word32`.

This file holds no theorem. `secondHashFunctionState` calls the compression function `Run.Blake2b.compress`
(Run/Blake2b/Compress.lean), the one that BLAKE2b itself calls. Around it this file defines the loop
over the blocks, the two counter words, the last call and the tree hash. Fmt/ has no text of the
second hash function, so there is nothing to prove `secondHashFunction` equal to: only the known answers in
OnBytes/Hash/TestSecondHashFunction.lean tie them to the format page.
-/
import Fmt.Rules1
import Run.Blake2b.Hash

namespace OnBytes

/-- The last state of the second hash function on a list of words under the number num. w holds the
words' bytes, and n = w.size / 4 is the number of words. The list is cut into blocks of 32 words, at
least one, the last filled up with zeros. The counter's low word is the number of bytes up to the
block's end, and 4 n in the last call, which alone sets the last-block flag. Its high word is always
num + 2^32 n modulo 2^64. R15.3 wants num and n below 2^32: this is not tested. If w.size is not a
multiple of 4, n is rounded down, and the bytes left over still enter the last block. -/
def secondHashFunctionState (num : Nat) (w : ByteArray) : Run.Blake2b.ChainingValue :=
  let n := w.size / 4
  let full := (w.size + 127) / 128 - 1
  let t1 := UInt64.ofNat (num + 4294967296 * n)
  let S := Nat.fold full
    (fun i _ S => Run.Blake2b.compress { S with t0 := UInt64.ofNat (128 * (i + 1)), t1 := t1 }
      (Run.Blake2b.MessageBlock.ofBytes w (128 * i)))
    (Run.Blake2b.firstState 0 64)
  (Run.Blake2b.compress
    (Run.Blake2b.setLastblock { S with t0 := UInt64.ofNat (4 * n), t1 := t1 })
    (Run.Blake2b.MessageBlock.ofBytes w (128 * full))).h

/-- K(num; w) of R15.3 (docs/format/FORMAT.md): the second hash function on a list of words under a
number. The digest is the first eight 32-bit words of the last state: 32 bytes. -/
def secondHashFunction (num : Nat) (w : ByteArray) : ByteArray := (secondHashFunctionState num w).bytes 32

/-- One level of the tree hash: the digests under num of the pieces of 128 words, one after the
other. The last piece can be shorter. -/
def secondHashFunctionTreeLevel (num : Nat) (w : ByteArray) : ByteArray :=
  Nat.fold ((w.size + 511) / 512)
    (fun i _ acc => acc ++ secondHashFunction num (w.extract (512 * i) (512 * (i + 1)))) ByteArray.empty

/-- Levels of the tree hash until one digest is left: the first level under num, the later ones
under 11. The first argument bounds the number of levels; the result is none if it runs out. -/
def secondHashFunctionTreeLevels : Nat → Nat → ByteArray → Option ByteArray
  | 0, _, _ => none
  | k + 1, num, w =>
    let d := secondHashFunctionTreeLevel num w
    if d.size == 32 then some d else secondHashFunctionTreeLevels k 11 d

/-- TK(w) of R15.3: the tree hash of a list of at least eight words. The first level is hashed
under the number 10, the others under 11. So every list is hashed at least once, and the number
tells a piece of the list from a piece of digests. A level has a sixteenth of the bytes of the
level before, rounded up to a whole digest, so sixteen levels are enough for every list of fewer
than 2^64 bytes. The result is nothing if w is not made of whole words or has fewer than eight. -/
def secondHashFunctionTree (w : ByteArray) : Option ByteArray :=
  if w.size % 4 != 0 || w.size < 32 then none else secondHashFunctionTreeLevels 16 10 w

/-- The words of a text (R15.4): its bytes, filled up with zero bytes to a whole word. -/
def textWords (t : ByteArray) : ByteArray := t ++ Fmt.zeroBytes ((4 - t.size % 4) % 4)

/-- A word of 32 bits as four bytes, lowest byte first. x is taken modulo 2^32. -/
def word32 (x : Nat) : ByteArray := (Fmt.u64n x).extract 0 4

end OnBytes
