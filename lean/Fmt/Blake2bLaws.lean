-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Fmt.Blake2b
import Run.Blake2b.SaltedThm
/-!
# BLAKE2b: the digest's length

`size_blake2b`: a digest of `dlen ≤ 64` bytes has `dlen` bytes.
-/
namespace Fmt

namespace Spec

/-- The statement of `Fmt.size_blake2b`. -/
def size_blake2b : Prop :=
  ∀ (dlen : Nat) (salt pers msg : ByteArray), dlen ≤ 64 → (blake2b dlen salt pers msg).size = dlen

end Spec

/-- A digest of `dlen ≤ 64` bytes has `dlen` bytes. -/
theorem size_blake2b : Spec.size_blake2b := by
  intro dlen salt pers msg h
  unfold blake2b
  rw [Run.Blake2b.blake2bSaltedPlain_eq]
  exact Run.Blake2b.size_blake2bSalted salt pers msg dlen h

end Fmt

#print axioms Fmt.size_blake2b
