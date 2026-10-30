-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K13CapInScope.lean: IN THE GOALS' SCOPE
the three comparisons with the cap of the kind K13's law's top (capB: the binder hCapB) accept at
the seated numbers K13.whereOf Z; and the three shapes of the linear claims are one there (the
binders hS and hp of the last chain's row 0). Calls alone: capB_of_written
(K13CapAtWritten.lean), lin_last_of_written (Johnson/Goal/Numbers/WrittenShapes.lean),
written_in_scope (Johnson/Goal/Numbers/WrittenInScope.lean) and k14_real (the typed
value is there). A law file; no running text imports it.
  capB_in_scope: InScope W → the pure road's public part is Z → the two pins accept → the value is
      laid → capB (K13.whereOf Z) = true
  lin_last_in_scope: the like: (K13.whereOf Z).lin = (P2Third.lastPar Z).S

PREMISES THAT STAY, written_in_scope's own: hs, hf: the two law forms of the door's pin
(sizedPinnedAt, firstPinnedAt) accept at Z; hl: proofDataAndDecisionOfPublicFiles returns. What is not claimed. That these
premises hold at a seat: the door's row gives the pins. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K13CapAtWritten
import Johnson.Goal.Numbers.WrittenShapes
import Johnson.Goal.Numbers.WrittenInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Params
open Desc.K14.Law (written_in_scope k14_real lin_last_of_written)
open VerifiableInference.PlanWritten (sizedPinnedAt firstPinnedAt)
open VerifiableInference.Desc.K13.Law (capB capB_of_written)
open LPFD.Full (proofDataAndDecisionOfPublicFiles RunPF)

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD} {r : RunPF}

/-- **The binder hCapB, in scope.** -/
theorem capB_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : firstPinnedAt Z.p.X.P Z.first = true)
    (hl : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    capB (VerifiableInference.Desc.K13.whereOf Z) = true := by
  obtain ⟨x, hx, -, -⟩ := k14_real
  exact capB_of_written (written_in_scope hW h hs hf hl hx)

/-- **The binder hS of the last chain's row 0, in scope.** -/
theorem lin_last_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : firstPinnedAt Z.p.X.P Z.first = true)
    (hl : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    (VerifiableInference.Desc.K13.whereOf Z).lin = (P2Third.lastPar Z).S := by
  obtain ⟨x, hx, -, -⟩ := k14_real
  exact lin_last_of_written (written_in_scope hW h hs hf hl hx)

end HashBuild

#print axioms HashBuild.capB_in_scope
#print axioms HashBuild.lin_last_in_scope
