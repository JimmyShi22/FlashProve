-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.SaltedPlain
/-!
# BLAKE2b as the format calls it

`blake2b dlen salt pers msg` is BLAKE2b without a key, with a digest of `dlen` bytes, a salt and a
personalization: `Run.Blake2b.blake2bSaltedPlain` (Run/Blake2b/SaltedPlain.lean) with the arguments
in the format's order. It is the form that Lean's kernel can compute; compiled code should call
`blake2bF` (Fmt/Blake2bFast.lean), which is equal to it. Nothing of BLAKE2b is defined here.

At the borders. For `dlen = 0` and `dlen > 64` the digest is empty. A salt or a personalization of
fewer than 16 bytes is filled up with zeros, and bytes after the sixteenth are not read.
-/
namespace Fmt

/-- BLAKE2b of `msg` without a key: a digest of `dlen` bytes (1 to 64), with the salt `salt` and the
personalization `pers` (16 bytes each). It is marked irreducible so that Lean, when it compares two
calls, compares their arguments and does not unfold the hash. `unfold blake2b` still opens it, and
the kernel still computes it; a proof by `rfl` or by `decide` without `+kernel` does not see through
it. -/
@[irreducible] def blake2b (dlen : Nat) (salt pers msg : ByteArray) : ByteArray :=
  Run.Blake2b.blake2bSaltedPlain salt pers msg dlen

end Fmt
