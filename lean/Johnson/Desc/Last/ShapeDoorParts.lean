-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorParts.lean: THE SHARED CHAIN'S TEXT AT THE DOOR (`doorSharedB`,
Johnson/Desc/Last/DoorTexts.lean) FROM THREE FACTS ON THE CHAIN'S OWN RECORD, in the shapes in which
other hands have them. One statement and its proof; no definition.

Main name (namespace `VerifiableInference.Desc.Last`).
  **`doorSharedB_of_parts`**: `doorSharedB p d = true` from: h1: `Means.inOrderB d.st` · h23: at
    every ψ: `bookFitsB d.book` and `tenantB ⟨d.st, d.book, ψ, d.loc.oOmega⟩` (the conclusion of a
    sister file's `door_two_three`, Johnson/Desc/Sound/BookFitsCarried.lean) · h45: the message at
    `d.loc.oOmega` is there, has the plan's shape of Omega, and has one sample row.

Every "there is": y in h45: tied by `oracles[…]? = some y`.
Limits. A joining: none of the three is shown here. It reads `Desc.K14.ended`'s text: what that
hands of a record d is d's own statement, book, ψ and Omega's number. It is what the shared chain's
last block owes where `doorX` is laid beside the table's `shape`
(Johnson/Desc/Last/ShapeDoorBeside.lean). NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.DoorTexts

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.Sound (bookFitsB tenantB)
open _root_.Desc.K14 (St)

/-- **The shared chain's text from three facts on the record.** -/
theorem doorSharedB_of_parts {p : P₁₄} {d : St} (h1 : Means.inOrderB d.st = true)
    (h23 : ∀ ψ, bookFitsB d.book = true ∧ tenantB ⟨d.st, d.book, ψ, d.loc.oOmega⟩ = true)
    (h45 : ∃ y, d.st.oracles[d.loc.oOmega]? = some y ∧ y.shape = p.S.omega ∧
      y.sampleRows.size = 1) : doorSharedB p d = true := by
  unfold doorSharedB
  cases he : _root_.Desc.K14.ended d with
  | none => rfl
  | some e =>
    unfold _root_.Desc.K14.ended at he
    split at he
    · obtain rfl := Option.some.inj he
      obtain ⟨y, hy, hs, h1r⟩ := h45
      show (doorSharedL p ⟨d.st, d.book, d.loc.psiSh, d.loc.oOmega⟩).all (·.2) = true
      simp only [doorSharedL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      refine ⟨h1, (h23 d.loc.psiSh).1, (h23 d.loc.psiSh).2, ?_, ?_⟩
      · show (match d.st.oracles[d.loc.oOmega]? with
          | some y => decide (y.shape = p.S.omega)
          | none => false) = true
        rw [hy]
        exact decide_eq_true hs
      · show (match d.st.oracles[d.loc.oOmega]? with
          | some y => y.sampleRows.size == 1
          | none => false) = true
        rw [hy]
        simp [h1r]
    · cases he

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.doorSharedB_of_parts
