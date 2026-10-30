-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/ClosingAtBase.lean: CONDITIONAL: on the head at the return and on the maker's return
at the base filling. THE FULL SIZE ALONE.

What is here. The code switch's closing test says yes at each of its places, at the return's public
part and ground: `closing_at_head` (Honest/K2/Law/ClosingAtHead.lean, of the code switch's writers;
beneath it 25 closed tests by Lean's kernel) carried over the seam from the description's ground to
the return's (`atPure_at_laid_ground`, Honest/AtHeadGround.lean). It is the one named hypothesis of
`lays_cells` (AtFullSide/K4/LaysCellsAtTheFirstScript.lean), `own_mask_row_switch`
(AtFullSide/K4/SignsAtSwitches.lean) and `column_hX_at_first_thread`
(AtFullSide/K4/ColumnAtTheFirstThread.lean).

Not shown here. A test with code on public data: nothing on a run. Beneath `closing_at_head` lie 25
closed facts by Lean's kernel, replayed by no independent checker; in these writers' rides the code
switch's seven files on the closing lay compiled and were built in none. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import AtFullSide.K4.SignsLetters
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead
import Johnson.Desc.ProofFile.Honest.AtHeadGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K4.Signs
open ProofFile ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles (FullSizeMatrix)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- CONDITIONAL: on h and hA. **The code switch's closing test says yes at each of its places**, at
the return's public part and ground. -/
theorem closing_returns_at_base (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A) :
    ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true := by
  obtain ⟨Bs, base₀, O⟩ := h.head.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.head.laid O.blank hA
  rw [eG]
  exact K2.Law.closing_at_head h.head.toAtMg O

end AtFullSide.K4.Signs

#print axioms AtFullSide.K4.Signs.closing_returns_at_base
