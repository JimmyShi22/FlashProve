-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/JoinsRows.lean: a joining (`Joins`, Johnson/Desc/K1/Law/GroupAtRecord.lean)
leaves every group's open rows.

Main name: `Joins.rowsKept`.

What is not claimed. Nothing on a group's members. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.GroupAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes

/-- Every group in front stands behind, with its open rows. -/
theorem Joins.rowsKept {st st' : Statement} {g : Nat} {ids : List Nat} (h : Joins st st' g ids)
    (j : Nat) (G : Group) (hG : st.groups[j]? = some G) :
    ∃ G' : Group, st'.groups[j]? = some G' ∧ G'.rows = G.rows := by
  by_cases e : j = g
  · subst e
    obtain ⟨G', h1, _, h2, _⟩ := h.here G hG
    exact ⟨G', h1, h2⟩
  · exact ⟨G, (h.other j e).trans hG, rfl⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.Joins.rowsKept
