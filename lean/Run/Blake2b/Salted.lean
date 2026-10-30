-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.Hash
/-!
# BLAKE2b with a salt and a personalization, and a message of bytes in two parts

blake2bSalted is the hash of a byte string without a key, with the fields salt and personal of the
parameter block, and with a digest of 1 to 64 bytes. absorbBytes and resumeBytes hash a message in
two parts: the state after a beginning of whole blocks can be kept and used for many messages with
that beginning.
SaltedThm.lean has the theorems, SaltedPlain.lean a form for Lean's kernel, Test/Salted.lean known
answers.

All five definitions are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the BLAKE2
reference source code package (reference C implementations), Copyright 2012, Samuel Neves, used here
under CC0 1.0 Universal (SPDX: CC0-1.0) as the head of Hash.lean says. The comment of each names
what it is adapted from and says what is changed. The functions of Hash.lean that they call have the
sources that its head names.

Every definition is total, and none indexes with "!".
-/
namespace Run.Blake2b

/-- The state after `blake2b_init_param` (`blake2b-ref.c` of the BLAKE2 reference source code
package) on the `blake2b_param` that `blake2b_init` fills in for `outlen`, but with `salt` in its
field `salt` (bytes 32 to 47) and `personal` in its field `personal` (bytes 48 to 63). A byte of a
field at or beyond the end of its array is 0, and bytes of an array after the sixteenth are not
read. `outlen` is not checked. -/
@[inline] def firstStateSalted (outlen : Nat) (salt personal : ByteArray) : State :=
  initParam (parameterBlockFirstWord 0 outlen) 0 0 0
    (load64 salt 0) (load64 salt 8) (load64 personal 0) (load64 personal 8)

/-- The state after `blake2b_update` on all of `data` and then `blake2b_final`, up to and including
its `blake2b_compress` (`blake2b-ref.c` of the BLAKE2 reference source code package), from
`firstStateSalted outlen salt personal`. `outlen` is not checked. -/
def stateSalted (salt personal data : ByteArray) (outlen : Nat) : State :=
  message (fun j => MessageBlock.ofBytes data (128 * j)) data.size (firstStateSalted outlen salt personal)

/-- The unkeyed BLAKE2b digest of `data`, `outlen` bytes long, with a salt and a personalization as
`firstStateSalted` reads them. The result is the empty array if `outlen` is 0 or above 64, where
`blake2b_init` in `blake2b-ref.c` of the BLAKE2 reference source code package returns -1. -/
def blake2bSalted (salt personal data : ByteArray) (outlen : Nat) : ByteArray :=
  if outlen = 0 ∨ outlen > 64 then ByteArray.empty
  else (stateSalted salt personal data outlen).h.bytes outlen

/-- The state after the first `nblk` blocks of 128 bytes of `a` are compressed into `S`, as
`blake2b_update` in `blake2b-ref.c` of the BLAKE2 reference source code package compresses blocks
that more of the message follows. Bytes at or beyond the end of `a` read as 0. At least one more
byte of the message must follow these blocks: see `resumeBytes`. -/
def absorbBytes (S : State) (a : ByteArray) (nblk : Nat) : State :=
  updateBlocks (fun j => MessageBlock.ofBytes a (128 * j)) nblk 0 S

/-- The state at the end of a message that has come as far as `S`, with an empty buffer, and ends
with the bytes of `rest`: `blake2b_update` on `rest` and `blake2b_final` up to and including its
`blake2b_compress` (`blake2b-ref.c` of the BLAKE2 reference source code package). `S.f0` must be 0:
see `finalBlock`. If blocks were compressed into `S` and `rest` is empty, the last block is an
all-zero block of length 0, and the result is not the BLAKE2b state for the bytes compressed. -/
def resumeBytes (S : State) (rest : ByteArray) : State :=
  message (fun j => MessageBlock.ofBytes rest (128 * j)) rest.size S

end Run.Blake2b
