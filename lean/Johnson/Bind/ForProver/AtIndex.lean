-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/AtIndex.lean: the encoded index's column at the full size, with the index
read through the library's reader of an index's digits (`OnBytes.HonestTrace.entryOf`). A definition
and one equation.

`encIdx Z i` is `encW` (Johnson/Bind/ForProver/Enc.lean) at the index's matrix of digits in the
field as `OnBytes.HonestTrace.entryOf i` reads it (Johnson/HonestTrace/IndexReaders.lean).
   `encIdx_eq_enc`: it is `enc`, which reads the casts of the matrix's integers: by unfolding.
Limits. It means something at the full size's shape alone, as `enc` does. One committed table; which
of the protocol's tables it is, the first or a copy, is not said here. This file writes no honest
prover: the frame's prover has fields that no text of this file fills. Nothing on completeness, on
index privacy or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Enc
import Johnson.HonestTrace.IndexReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open ProofFile.Honest (TableRand Weights)

/-- **The encoded index's column, the index read through `OnBytes.HonestTrace.entryOf`.** -/
def encIdx (Z : ProofFile.Pub) (i : Cm.Idx) : (ℕ → TableRand) → ℕ → ℕ → Option (List Cb.Gl.F) :=
  encW Z ⟨OnBytes.HonestTrace.entryOf i⟩

/-- It is `enc`. -/
theorem encIdx_eq_enc : encIdx = enc := rfl

end Bind.ForProver

#print axioms Bind.ForProver.encIdx_eq_enc
#print axioms Bind.ForProver.encIdx
