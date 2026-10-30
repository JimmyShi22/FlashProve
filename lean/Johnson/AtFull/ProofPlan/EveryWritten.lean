-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/EveryWritten.lean: THE TEST «NO ENTRY OF THE SEVEN PLANS IS WITHOUT A TEST»
(Johnson.Desc.Ok.everyOk, Johnson/Desc/Ok/FormRules.lean) ACCEPTS THE JOINED WRITTEN TERM: the join
of the twenty-one closed facts of the folder Every/ by the two joinings of EveryOf.lean. No
evaluation here: the facts are imported compiled.
  `five_written` : fiveOk MW = true. **`every_written`** : everyOk MW = true.
  `every_no`: a bent twin of the join: without the proof file's last plan it is false. The tests'
    own controls, one a test, and four counts of lists that are not empty (planSeeds AND THE TESTS'
    OTHER LISTS UNDER AN «all» ARE NOT COUNTED): Every/Controls.lean.
  **`hF_written`**: A.fileOk · B.fileOk · Z.p.chains.made = writtenMade.at h ⟹ the proof file's
    description's fileOk is true: `hF_of_four` with its last hypothesis paid.
  `hF_of_free`: the same from freeOf Z.p.chains.made = writtenMade. Who pays hm or that: e.g.
    Johnson.AtFull.Made.configure_eq_written_at (Johnson/AtFull/Made/MadeIsWritten.lean).
Limits. A.fileOk and B.fileOk are the two later chains' own. That the planner's «made» is the
written term at any public files is not said. What a yes of everyOk gives is said in FormRules.lean
and the files that use it. By a reading of the tests' texts: testsOk HAS NO NEGATIVE TEST THAT
REACHES ITS ARITHMETIC (tests_no repeats workOk's bound); every_no repeats seven_no.
Nothing on soundness.
-/
import Johnson.AtFull.ProofPlan.EveryOf
import Johnson.AtFull.ProofPlan.Every.Seven
import Johnson.AtFull.ProofPlan.Every.SetWork
import Johnson.AtFull.ProofPlan.Every.FirstPlans
import Johnson.AtFull.ProofPlan.Every.Rads
import Johnson.AtFull.ProofPlan.Every.Top
import Johnson.AtFull.ProofPlan.Every.Work
import Johnson.AtFull.ProofPlan.Every.Tests
import Johnson.AtFull.ProofPlan.Every.Locs
import Johnson.AtFull.ProofPlan.Every.Tables
import Johnson.AtFull.ProofPlan.Every.Points
import Johnson.AtFull.ProofPlan.Every.Sends
import Johnson.AtFull.ProofPlan.Every.Bats
import Johnson.AtFull.ProofPlan.Every.Census
import Johnson.AtFull.ProofPlan.Every.Rounds
import Johnson.AtFull.ProofPlan.Every.LinkGood
import Johnson.AtFull.ProofPlan.Every.RowsP1
import Johnson.AtFull.ProofPlan.Every.RowsP2
import Johnson.AtFull.ProofPlan.Every.RowsK1
import Johnson.AtFull.ProofPlan.Every.RowsK2
import Johnson.AtFull.ProofPlan.Every.RowsE
import Johnson.AtFull.ProofPlan.Every.Bears

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan

open Johnson.Bridge.OkNat Johnson.Desc.Ok
open VerifiableInference.PlanWritten.Joined (writtenMade)
open Johnson.G.MadeFree (Hung freeOf hungOf at_free)
open Every

/-- fiveOk at the written term. -/
theorem five_written : fiveOk MW = true :=
  fiveOk_of rads top work tests locs tables points sends bats census rounds linkGood rowsP1 rowsP2
    rowsK1 rowsK2 rowsE bears

/-- **everyOk at the written term.** -/
theorem every_written : everyOk MW = true := everyOk_of seven five_written firstPlans setWork

/-- A bent twin: without the proof file's last plan. -/
theorem every_no :
    everyOk ({ writtenMade with proof := writtenMade.proof.dropLast }.at Hung.none) = false := by
  decide +kernel

/-- **PlanWordOwed.hF, from three.** -/
theorem hF_written {σ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (get : σ → VerifiableInference.Desc.First.S)
    (start : ProofFile.InstPub → σ) (c : VerifiableInference.Desc.Chain σ ProofFile.Cl) {h : Hung}
    (hA : A.fileOk = true) (hB : B.fileOk = true) (hm : Z.p.chains.made = writtenMade.at h) :
    (ProofFile.fileDescBy o mk Z A B get start c).fileOk = true :=
  hF_of_four o mk Z A B get start c hA hB hm every_written

/-- The same, from the four fields that do not hang on the eight strings. -/
theorem hF_of_free {σ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (get : σ → VerifiableInference.Desc.First.S)
    (start : ProofFile.InstPub → σ) (c : VerifiableInference.Desc.Chain σ ProofFile.Cl)
    (hA : A.fileOk = true) (hB : B.fileOk = true) (hf : freeOf Z.p.chains.made = writtenMade) :
    (ProofFile.fileDescBy o mk Z A B get start c).fileOk = true :=
  hF_written o mk Z A B get start c (h := hungOf Z.p.chains.made) hA hB
    (by rw [← hf]; exact (at_free _).symm)

end Johnson.AtFull.ProofPlan

#print axioms Johnson.AtFull.ProofPlan.five_written
#print axioms Johnson.AtFull.ProofPlan.every_written
#print axioms Johnson.AtFull.ProofPlan.every_no
#print axioms Johnson.AtFull.ProofPlan.hF_written
#print axioms Johnson.AtFull.ProofPlan.hF_of_free
