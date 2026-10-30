-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K11Closed.lean: THE SIX CLOSED PREMISES ON THE TABLE OF JOINTS THAT
`mergeFill_at` (Johnson/Desc/Sound/MgAt/K11.lean) LEAVES, AT THE FULL SIZE's WRITTEN LISTS: links :=
`linksFull` (Johnson/Desc/Sound/AtDriver.lean), ps := `flatPlacesOf linksFull true`, border
k := 346, segment m := 24. Statements with their proofs: evaluation by Lean's kernel; two
rewritings.

  `k11_ins`, `k11_outs`, `k11_ctx`: the table's row at sub-protocol number 346: it closes
    "weights" of segment 24, opens "merged" and "wo 24", and reads pinW, pin 24 0, pinI.
  `k11_sub`: segment 24 is the output head's.
  `k11_ledger_closed`, `k11_free_closed`: "ledger 24" and "freeAbove 24" are open at border 346, at
    the composed meaning's closed list of extra public tests with code (`moreAll`,
    Johnson/Desc/Sound/MoreAll.lean).
  **`k11_hoL`, `k11_hoF`**: so they are at `(mgAll D Mg).more`, where Mg.more is empty
    (`mgAll_more_closed`, `mgMore_is`).
  **`k11_six`**: the six in `mergeFill_at`'s own letters, at every D whose field links is the
    written list.
  `linksFull_is`: that list is `P5J.fullLinks` (Johnson/P5J/MeansQ.lean): rfl.
  NEGATIVE TESTS, by the kernel too: the rows at 345 and 347 close something else; "ledger 23" is
    not open at border 346; "ledger 24" is not open at border 0.
Limits. The full size's written list alone. AT THE TABLE's ROWS AND THE LIST OF EXTRA PUBLIC TESTS
AS IMPORTED: any other text of either owes these anew. No soundness is claimed.

-/
import Johnson.Desc.Sound.MoreAll
import Johnson.P5J.MeansQ
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning pubSets flatPlacesOf)

/-- The two names of the full size's written list of the segments' sorts are one. -/
theorem linksFull_is : linksFull = P5J.fullLinks := rfl

/-- The full size's written list of places. -/
abbrev psFull : List Place := flatPlacesOf linksFull true

set_option maxRecDepth 1000000 in
theorem k11_ins : (rowQ linksFull psFull 346).ins = [.forms 24 4 "weights"] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_outs : (rowQ linksFull psFull 346).outs = [.forms 24 9 "merged", .wo 24] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_ctx : (rowQ linksFull psFull 346).ctx = [.pinW, .pin 24 0, .pinI] := by
  decide +kernel

theorem k11_sub : linksFull[24]? = some .head := by decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_ledger_closed : Pub.ledger 24 ∈ (pubSets moreAll linksFull psFull)[346]?.getD [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_free_closed :
    Pub.freeAbove 24 ∈ (pubSets moreAll linksFull psFull)[346]?.getD [] := by
  decide +kernel

/-! ### Negative tests -/

set_option maxRecDepth 1000000 in
theorem k11_ins_not_345 : (rowQ linksFull psFull 345).ins ≠ [.forms 24 4 "weights"] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_ins_not_347 : (rowQ linksFull psFull 347).ins ≠ [.forms 24 4 "weights"] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_ledger23_shut : Pub.ledger 23 ∉ (pubSets moreAll linksFull psFull)[346]?.getD [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_ledger_shut_at_0 : Pub.ledger 24 ∉ (pubSets moreAll linksFull psFull)[0]?.getD [] := by
  decide +kernel

/-! ### At the composed meaning -/

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

theorem k11_hoL (hM : Mg.more = {}) :
    Pub.ledger 24 ∈ (pubSets (mgAll D Mg).more linksFull psFull)[346]?.getD [] := by
  rw [mgAll_more_closed D Mg hM, mgMore_is]
  exact k11_ledger_closed

theorem k11_hoF (hM : Mg.more = {}) :
    Pub.freeAbove 24 ∈ (pubSets (mgAll D Mg).more linksFull psFull)[346]?.getD [] := by
  rw [mgAll_more_closed D Mg hM, mgMore_is]
  exact k11_free_closed

/-- **The six, in `mergeFill_at`'s own letters.** -/
theorem k11_six (hl : D.links = linksFull) (hM : Mg.more = {}) :
    (rowQ D.links psFull 346).ins = [.forms 24 4 "weights"] ∧
    (rowQ D.links psFull 346).outs = [.forms 24 9 "merged", .wo 24] ∧
    (rowQ D.links psFull 346).ctx = [.pinW, .pin 24 0, .pinI] ∧
    Pub.ledger 24 ∈ (pubSets (mgAll D Mg).more D.links psFull)[346]?.getD [] ∧
    Pub.freeAbove 24 ∈ (pubSets (mgAll D Mg).more D.links psFull)[346]?.getD [] ∧
    D.links[24]? = some .head := by
  rw [hl]
  exact ⟨k11_ins, k11_outs, k11_ctx, k11_hoL D Mg hM, k11_hoF D Mg hM, k11_sub⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.linksFull_is
#print axioms VerifiableInference.Desc.Sound.k11_ins
#print axioms VerifiableInference.Desc.Sound.k11_outs
#print axioms VerifiableInference.Desc.Sound.k11_ctx
#print axioms VerifiableInference.Desc.Sound.k11_sub
#print axioms VerifiableInference.Desc.Sound.k11_ledger_closed
#print axioms VerifiableInference.Desc.Sound.k11_free_closed
#print axioms VerifiableInference.Desc.Sound.k11_ins_not_345
#print axioms VerifiableInference.Desc.Sound.k11_ins_not_347
#print axioms VerifiableInference.Desc.Sound.k11_ledger23_shut
#print axioms VerifiableInference.Desc.Sound.k11_ledger_shut_at_0
#print axioms VerifiableInference.Desc.Sound.k11_six
