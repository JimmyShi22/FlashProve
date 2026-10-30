-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/DrawNum.lean: K9's OWN DRAW LEAVES THE THREE NUMBERS: what the library's `numOf`
(Johnson/Desc/First/Batch/Law/RowsRide.lean) reads of a state (the smallness test's state with its written fields
blanked · the tables · the plan's number of claims) is the same behind a yes of the draw as in front. A statement and
its proof ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.
  **`draw_num`**   where K9's lens reads a part at s and the draw's decision says yes at the element x with t₁ behind:
      `numOf u t₁ = numOf u s`, at every u. Two calls: our `draw_is` (Honest/K9/LedgerOf.lean: the state behind is the
      state in front with K9's part laid anew) and the library's `K9L.num_set`
FOR WHOM: the house of K8, which walks from the run "K8.equations" inside the gatherer back to the state in front of
the draw (with the field `numRun` of `SealLaw`, Honest/K9/TotalFront.lean). No member; called by
Honest/K9/GoodAttLook.lean.
WHAT IS NOT CLAIMED. That the draw says yes at any state. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.LedgerOf
import Johnson.Desc.First.Batch.Law.RowsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.K9 (atS)

/-- **The draw leaves the three numbers.** -/
theorem draw_num (u : HTailF2) (p : Desc.K9.Where) (s t₁ : S) (x : E) (a : Desc.K9.Part)
    (ha : atS.get? s = some a)
    (h : (Desc.K9.drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁) :
    K9L.numOf u t₁ = K9L.numOf u s := by
  rw [draw_is p s t₁ x a ha h]
  exact K9L.num_set u s a _ ha rfl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.draw_num
