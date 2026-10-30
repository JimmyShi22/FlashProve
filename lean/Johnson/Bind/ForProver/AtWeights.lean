-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/AtWeights.lean: THE PACKING FOR AN HONEST PROVER, AT THE DIGITS OF GIVEN
WEIGHTS AND THE FULL SIZE'S NUMBERS, IS THE TABLE'S PLAIN ENTRIES OF WHAT STANDS IN THE COMMIT
FIELD. A statement and its proof.

Why. What stands in the commit field (`Bind.Cpp.cppCommit T`, at every T,
Johnson/Bind/Cpp/Defs.lean) lays its table's plain entries by `Bind.Cpp.entryOf s w`: words of
integers. An honest prover's encoded index lays them by `entryAtF`
(Johnson/Bind/ForProver/Rows.lean): words of field elements. At the casts of the same integers the
two are one function.

Main name (namespace `Bind.ForProver`).
  **`entryOf_eq`**: `Bind.Cpp.entryOf s w` is `entryAtF` at the full size's numbers (numsRef's kLo
    and rows; 11 row variables) and the casts of the matrix of `Bind.Cpp.idxOf s w`.

Limits. The full size's numbers alone, and at no public part: that the numbers off a public part are
these is `ShapeAtFull` (Johnson/Bind/ForProver/LawsSizes.lean): a premise in
Johnson/Bind/ForProver/JoinsSizes.lean, a theorem at files in the goals' scope where the maker of
the public part (`ProofFile.pubPlain`) returned (Johnson/Bind/ForProver/InScope.lean). Nothing on pads,
tails or salts. Nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Rows
import Johnson.Bind.Digits
import Johnson.Bind.Cpp.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Bind.ForProver
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **The two texts of the plain entries are one function.** -/
theorem entryOf_eq (s : IntegerTransformer.Settings) (w : ModelWeights s) :
    Bind.Cpp.entryOf s w =
      entryAtF numsRef.kLo numsRef.rows 11
        (fun y c => (((Bind.Cpp.idxOf s w).mat y c : ℤ) : Cb.Gl.F)) := by
  funext b e
  unfold Bind.Cpp.entryOf entryAtF Bind.Cpp.wordOfInt
  rw [Bind.Column.ofF_intCast]

end Bind.ForProver

#print axioms Bind.ForProver.entryOf_eq
