-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/EveryOf.lean: THE PROOF FILE's DESCRIPTION's fileOk (ProofFile.fileDescBy,
Johnson/Desc/ProofFile/Frames1.lean), FROM ITS PARTS: JOININGS: no evaluation. In the ledger for
"the head has a member" this is PlanWordOwed.hF.

  `fiveOk_of`: Johnson.Bridge.OkNat.fiveOk M from its sixteen conjuncts, with its two letters (the
    stored tables' radius, the largest list) as numbers R and L: hr : tableRads M.sized = [R, R] ·
    ht : listTop M = L. So each conjunct can be asked of Lean's kernel alone, at numerals.
  `everyOk_of`: Johnson.Desc.Ok.everyOk M from its four.
  `everyOk_at`: everyOk does not hang on the eight strings of a joined term: rfl.
  `proofOk_at`: Desc.proofOk (writtenMade.at h) = true: a call of `made_ok`
    (Johnson/Goal/Written/MadeFacts.lean).
  `fileOk_text`: fileDescBy's fileOk is its four conjuncts: rfl.
  **`hF_of_four`**: A.fileOk · B.fileOk · Z.p.chains.made = writtenMade.at h · hE : everyOk at the
    written term with eight empty strings ⟹ (fileDescBy o mk Z A B get start c).fileOk = true.
Limits. hE is a hypothesis here; it is paid in EveryWritten.lean. A.fileOk and B.fileOk are the two
later chains' own. That the planner's «made» is the written term at any public files is not said.
Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.Ok.FormRules
import Johnson.Goal.Written.MadeFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan

open OnBytes.Params Johnson.Bridge.OkNat Johnson.Desc.Ok
open VerifiableInference.PlanWritten.Joined (writtenMade made_ok)
open Johnson.G.MadeFree (Free Hung)

/-- fiveOk, from its sixteen conjuncts at two numbers. -/
theorem fiveOk_of {M : Configured} {R L : Nat}
    (hr : tableRads M.sized = [R, R]) (ht : listTop M = L)
    (c1 : workOk M = true) (c2 : testsOk M = true) (c3 : locsOk R M = true)
    (c4 : tablesOk R M = true) (c5 : pointsOk R M = true) (c6 : sendsOk L M = true)
    (c7 : batsOk M = true) (c8 : censusOk M = true) (c9 : roundsOk M = true)
    (d0 : (linkPoint R M).good = true)
    (d1 : rowsOk (entriesAt M.proof 1) (sharedSlots R L M) = true)
    (d2 : rowsOk (entriesAt M.proof 2) (proofSecondSlots M) = true)
    (d3 : rowsOk (entriesAt M.key 1) (keySharedSlots R L M) = true)
    (d4 : rowsOk (entriesAt M.key 2) (keySecondSlots M) = true)
    (d5 : rowsOk M.entry.plan.entries (entrySlots R L M) = true)
    (b : bearsAt R M = true) : fiveOk M = true := by
  have eR : tableRad M = R := by
    unfold tableRad
    rw [hr]
    rfl
  unfold fiveOk planOk allOk fiveAt
  rw [eR, ht, hr, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, d5, b]
  simp [Nat.beq_refl]

/-- everyOk, from its four. -/
theorem everyOk_of {M : Configured} (h7 : sevenOk M = true) (h5 : fiveOk M = true)
    (hf : firstPlansOk M = true) (hw : setWorkOk M = true) : everyOk M = true := by
  unfold everyOk
  rw [h7, h5, hf, hw]
  rfl

/-- everyOk does not hang on the eight strings. -/
theorem everyOk_at (W : Free) (h h' : Hung) : everyOk (W.at h) = everyOk (W.at h') := rfl

/-- The test on the prices of the proof file's three chains, at the written term. -/
theorem proofOk_at (h : Hung) : VerifiableInference.Desc.proofOk (writtenMade.at h) = true :=
  ((VerifiableInference.Desc.madeOk_iff _).1 (made_ok h)).2.2

section File

variable {σ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (A : ProofFile.SharedSeat)
  (B : ProofFile.SecondSeat) (get : σ → VerifiableInference.Desc.First.S) (start : ProofFile.InstPub → σ)
  (c : VerifiableInference.Desc.Chain σ ProofFile.Cl)

/-- The text. -/
theorem fileOk_text : (ProofFile.fileDescBy o mk Z A B get start c).fileOk =
    (A.fileOk && B.fileOk && VerifiableInference.Desc.proofOk Z.p.chains.made &&
      everyOk Z.p.chains.made) := rfl

/-- **PlanWordOwed.hF, from four.** -/
theorem hF_of_four {h : Hung} (hA : A.fileOk = true) (hB : B.fileOk = true)
    (hm : Z.p.chains.made = writtenMade.at h)
    (hE : everyOk (writtenMade.at Hung.none) = true) :
    (ProofFile.fileDescBy o mk Z A B get start c).fileOk = true := by
  rw [fileOk_text, hA, hB, hm, proofOk_at, everyOk_at writtenMade h Hung.none, hE]
  rfl

end File

end Johnson.AtFull.ProofPlan

#print axioms Johnson.AtFull.ProofPlan.fiveOk_of
#print axioms Johnson.AtFull.ProofPlan.everyOk_of
#print axioms Johnson.AtFull.ProofPlan.everyOk_at
#print axioms Johnson.AtFull.ProofPlan.proofOk_at
#print axioms Johnson.AtFull.ProofPlan.fileOk_text
#print axioms Johnson.AtFull.ProofPlan.hF_of_four
