-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Hash/HEq.lean: the hash of OnBytes/Hash/H.lean is the format's hash of Fmt/Rules23.lean.

`Fmt.formatHash` states the format's hash, BLAKE2b on a label and the bytes, in a form that Lean's kernel can
compute. `formatHashFastForm` is the form for compiled code. The program calls `formatHashFastForm`; Fmt/ states the format
with `Fmt.formatHash`.

Main theorems: `hashH_eq` (for all arguments), `formatHashFastForm_eq_formatHash` (as functions). Both rest on
`Fmt.HF_eq` (Fmt/Rules5Fast.lean).

What is not claimed. The equality is thin. The two sides have the same label and call two forms of
BLAKE2b (Run/Blake2b/Salted.lean, SaltedPlain.lean) that differ only in how eight bytes are read
into a word. They share the compression function, the loop over the blocks and the parameter block,
so a fault in one of these, or in the label, would stand on both sides. Nothing is claimed here on
whether `Fmt.formatHash` is BLAKE2b, or on the strength of the hash. The second hash of this directory
(OnBytes/Hash/SecondHashFunction.lean) has no theorem: only known answers are tested.
-/
import OnBytes.Hash.H

namespace OnBytes

/-- `formatHashFastForm` and `Fmt.formatHash` are the same function. -/
theorem formatHashFastForm_eq_formatHash : formatHashFastForm = Fmt.formatHash := Fmt.HF_eq

/-- `formatHashFastForm` gives what `Fmt.formatHash` gives, for all arguments. -/
theorem hashH_eq (number tree index : Nat) (start bytes : ByteArray) :
    formatHashFastForm number tree index start bytes = Fmt.formatHash number tree index start bytes := by
  rw [formatHashFastForm_eq_formatHash]

end OnBytes

#print axioms OnBytes.formatHashFastForm_eq_formatHash
