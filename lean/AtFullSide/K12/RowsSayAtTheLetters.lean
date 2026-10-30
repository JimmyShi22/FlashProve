-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the one sentence that is left at the request's own test, at the letters' names.
/-
AtFullSide/K12/RowsSayAtTheLetters.lean: CONDITIONAL: at a stand of a thread: whether any stand is
there is not said; P : `OpenLast` h O is a premise here; `openLast`
(Honest/K12/AtFile/WAtTheLetters.lean, beneath this file) is a value of it, from the head at the
return and the maker's return.

What is here. THE ONE SENTENCE THAT OUR FILES LEAVE AT THE REQUEST's OWN TEST, the field rowsSay of
`OwnTestDebts` (AtFullSide/K12/SecondShareK12.lean), AT THE LETTERS' NAMES, FROM ANOTHER HOUSE's
TOP: one call. It pays nothing of its own. No definition; one statement.

  `rowsSay_at_the_letters`   the sentence, in the text in which
      AtFullSide/K12/ShareK12AtTheThreads.lean and AtFullSide/K12/SecondShareAtTheLetters.lean ask
      it.

By what. `saysAt_named` (AtFullSide/K12/WSaysNamed.lean): `SaysAt` at every stand at these names,
general in P, from the head, the maker's return and one premise on the sample rows · that premise:
`hsam_at_letters` (AtFullSide/K12/WSamplesAtLetters.lean), which is one call of a third house's law
· the one difference between that end and our field: there the frame lends at the job's own place,
here at `placeW`: `PublicFourteen`.place (AtFullSide/K12/WPublicFourteen.lean).

THE PREMISES: h · hA · P. No premise on values, on a book or on public numbers. It stands under ∀ R,
∀ k: at every return and every coin at which a stand is there: no run and no coin is fixed.

Limits. All limits of the three files' heads: the full size and the format's second hash function alone;
that a stand is reached is not said. They bear "NOT IN FRONT OF A LAW OVER COINS": here the sentence
is closed over its own coins. Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import AtFullSide.K12.WSaysNamed
import AtFullSide.K12.WSamplesAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.K12.Light (SaysAt)
open ProofFile.Honest.Term (matrixInput)
open AtFullSide.Honest.TheLetters

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- CONDITIONAL: on the head at the return, the maker's return and P. **THE FIELD rowsSay OF
`OwnTestDebts` AT THE LETTERS' NAMES**: `SaysAt` at every stand of `thread₃` with `said₃` at border
2, at every return R, all coins, and whatever the frame lends the unguarded pair at the test's
place. Another file's `saysAt_named` with its one premise paid by `hsam_at_letters`; the place at
which the frame lends is the job's own there and `placeW` here: that file's `PublicFourteen`.place.
-/
theorem rowsSay_at_the_letters (h : HeadAtReturn Z A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    {O : OpenShared A} (P : OpenLast h O) :
    ∀ (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit) (k : Coins A.B)
      (st : h.description.S₃) (m₀ : Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit) (E₀ : Env)
      (c : RowCoins [(firstPart P.ownMany.toRun.toTest : Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
          (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart P.ownMany.toRun.toTest]),
      ThrS (thread₃ h P R) (said₃ h P R) 2 k st m₀ E₀ →
      lendRow A.B (A.B.rowsOf 2) (k.look 2) placeW
        [(firstPart P.ownMany.toRun.toTest : Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins
                              ProofFile.Inst Cells) Unit),
          restPart P.ownMany.toRun.toTest] 0 = .ok c →
      SaysAt P.ownMany m₀.st.input (frontOf m₀) (restCoins P.ownMany.toRun.toTest c.2.1) := by
  intro R k st m₀ E₀ c u hl
  obtain ⟨layO, Q⟩ := publicFourteen_at_head h matrixInput OnBytes.HonestTrace.Sz.ref openHonest hA
    P.ownIsTheFilling
  rw [← Q.place] at hl
  exact (saysAt_named h hA P R (hsam_at_letters h P R) k st m₀ E₀ c u hl).2

end AtFullSide.K12

#print axioms AtFullSide.K12.rowsSay_at_the_letters
