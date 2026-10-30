-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Hash/H.lean: the format's hash, in the form for compiled code.

The hash H of the format (format page docs/format/FORMAT.md, R2.x and R3.x) is BLAKE2b on a
label of 16 bytes followed by the bytes to be hashed, with 32 further bytes, the hash's start, as
salt and personalization.
Every hash of the format is H, except the digests of R15.3: their hash is in
OnBytes/Hash/SecondHashFunction.lean. `Fmt.formatHash` states H with the form of BLAKE2b that Lean's kernel can compute.
`formatHashFastForm` is `Fmt.HF` (Fmt/Rules5Fast.lean): the same definition with the form for compiled code
(`Fmt.blake2bF`, Fmt/Blake2bFast.lean). It has the type of `Fmt.formatHash`, so it can be given to the strict
reader (`Fmt.readChainX`) in its place. The C++ counterpart is blocks/hash/hash.h.

Main definitions: `formatHashFastForm`.

This file holds no theorem. That `formatHashFastForm` equals `Fmt.formatHash` is proved in OnBytes/Hash/HEq.lean. Tests:
OnBytes/Hash/TestBlake2b.lean.
-/
import Fmt.Rules5Fast

namespace OnBytes

/-- The format's hash H (format page, R2.1 and R2.2). `number` is the number of the use (R3.1).
`tree` is all that the label's first word holds above its low 16 bits (R2.1), and `index` is the
label's second word. `start` is BLAKE2b's salt (bytes 0 to 15) and personalization (bytes 16 to
31). The digest has 64 bytes under the number 162 and 32 bytes otherwise. No bound of R2.3 is
tested here: each word of the label is taken modulo 2^64, and a start is cut or filled up with
zeros to 32 bytes. The C++ (blocks/hash/hash.h) stops the program on a call out of bounds and cuts
no argument. -/
def formatHashFastForm (number tree index : Nat) (start bytes : ByteArray) : ByteArray :=
  Fmt.HF number tree index start bytes

end OnBytes
