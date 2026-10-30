-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/TheCfg.lean: the one constant that stands in the place of the public files' digest
wherever a description or the plan is made of the public files alone.
`fixedConfigurationDigest`: 32 bytes of 1. `theCfg_size`: it has 32 bytes. `theCfg_ne_zero`: it is not 32 zero bytes.
Why. A description is a function of the public files and is handed no digest; the digest that the
verifier asks of the hash function reaches the compiler's side alone. Not 32 zero bytes: the reader
of proof files of the program `verify-on-bytes` and the key file's test on its file refuse that one
value by name. It imports nothing.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- The constant in the digest's place: 32 bytes of 1. -/
def fixedConfigurationDigest : ByteArray := ⟨Array.replicate 32 1⟩

theorem theCfg_size : fixedConfigurationDigest.size = 32 := rfl

theorem theCfg_ne_zero : fixedConfigurationDigest ≠ ⟨Array.replicate 32 0⟩ := by decide

end VerifiableInference.Desc
