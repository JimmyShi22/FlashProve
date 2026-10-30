-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PileMasksIff.lean: the test "every row on the table names mask entries of the
index masks' message alone" (`pileMasksC`, Johnson/Desc/K13/PubK13.lean) in the word of kind K13's
laws (`OnLedger`, Johnson/Desc/K13/Law/Agree.lean). One statement with its proof.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.PubK13
import Johnson.Desc.K13.Law.Agree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (S)

/-- The test on the rows' mask entries, in the laws' word. -/
theorem pileMasksC_iff (s : S) :
    pileMasksC s = true ↔ ∀ r ∈ s.rows, OnLedger s.out.indexMasks r := by
  unfold pileMasksC OnLedger
  simp only [List.all_eq_true, beq_iff_eq]

end VerifiableInference.Desc.K13.Law
