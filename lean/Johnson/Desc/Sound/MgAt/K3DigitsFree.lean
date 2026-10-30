-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/K3DigitsFree.lean: the lookup on the digits of a segment's approximate range
proof: THE PREMISE pubFree OF digMaskR_of_facts AND OF THE BUILDERS digOwed_mgAll, digOwed_forms, AT
THE COMPOSED MEANING mgAll Dm Mg: the term's public test at freeAbove l says attention's files'
Bool freeAboveB at the plan's number of slots. Two Bools of one sense
(Johnson/Desc/First/FillKeeper.lean; Johnson/Desc/First/Att/Door/DoorBools.lean): that the first
gives the second is freeAbove_door (Johnson/Desc/Sound/MgAt/K3CallsObjFacts.lean), called here. One
lemma. NO SOUNDNESS IS CLAIMED.

Main name.
  pubFree_mgAll: where the built segment l has n slots (hns), the premise pubFree at n.
WHAT IS LEFT. hns: (Dm.built[l]?).map (·.ns) = some n: a test on the term's built segments.
OBJECT. Two readers of the open segment's ledger; the composed public test.
Used by K3DigitsMaskSeat.lean and K3DigitsOwedSeven.lean (Johnson/Desc/Sound/MgAt/).
LETTERS. Dm, Mg; l, n.
IS IT EMPTY? hns is shown at no term.


Compiled with the whole library.

Limits. One way.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsObjFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning pubAll_freeAbove)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **pubFree.** -/
theorem pubFree_mgAll {l n : ℕ} (hns : (Dm.built[l]?).map (·.ns) = some n) :
    ∀ (z : P) s, (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true →
      H2K5.Door.freeAboveB n s = true := by
  intro z s h
  rw [mgAll_pub, pubAll_freeAbove] at h
  have e : Dm.pubD.nsOf l = some n := hns
  rw [e] at h
  exact freeAbove_door h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.pubFree_mgAll
