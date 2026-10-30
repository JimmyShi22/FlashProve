-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/RecIs.lean: a test "is this record the fixed record?", as a program, on the records in
plain letters (`RecP`, OnBytes/Slice/KeyOfRec.lean), with its two laws.

Why. The test on a proof file's first typed query lets one fixed record alone through
(`FrontSet.isR`, Johnson/Top/FrontSet.lean). That test stands inside the test of fitness of the
proof file's cut, and so inside every program that hashes what the cut writes: it has to be a
program too.

A record is a pair of functions on finite index types into the field and into its elements other
than 0. Equality of such functions is decided by going through the index types: s points of lg
coordinates and a factor, and 2 ^ v times s answers. At the two sizes (v, lg, s) = (8, 19, 1) and
(11, 29, 1): 276 and 2,078 comparisons in the field (`srS_v`, `frS_v`,
OnBytes/Flat/TableNumbers.lean). By reading; nothing is measured.

  `recIs r₀ r`   the test.
  `recIs_one`    what passes is r₀.
  `recIs_self`   r₀ passes.

What is not claimed. Anything on time. Nothing on soundness.


-/
import OnBytes.Slice.KeyOfRec
import OnBytes.Slice.RecordRead

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Slice

variable {v lg s : ℕ}

/-- **"Is the fixed record."** -/
def recIs (r₀ r : RecP NZ v lg s) : Bool := decide (r = r₀)

/-- What passes is the fixed record. -/
theorem recIs_one (r₀ r : RecP NZ v lg s) (h : recIs r₀ r = true) : r = r₀ :=
  of_decide_eq_true h

/-- The fixed record passes. -/
theorem recIs_self (r₀ : RecP NZ v lg s) : recIs r₀ r₀ = true := decide_eq_true rfl

end OnBytes.Flat

#print axioms OnBytes.Flat.recIs
#print axioms OnBytes.Flat.recIs_one
#print axioms OnBytes.Flat.recIs_self
