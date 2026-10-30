--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Honest/Shape/TestSeatAsksAtKeyRanges.lean: `seat_returns`
(Johnson/Desc/K12/Honest/Shape/TestSeatAsks.lean) AT THE KEY FILE's RANGES' TEST, AT THE FULL SIZE:
its one test with code on the shape in front and the plan (`guardK12`) is TRUE at the closed place
`piKRFull` (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean) and the written shape `shKRFull`
(TestAtKeyRangesShape.lean); and the law applied there.

  ★ `guard_KR`   all eight clauses of the guard are true there. By an evaluation in Lean's kernel.
  `guard_KR_no`   NEGATIVE TESTS, by the kernel, each with one thing turned: at a group's number
      that the shape does not have (it has one group: so no clause behind "the group is there" is
      tried by this one); with no mask named; with another message as the mask; at the shape with
      one place fewer in the book. NONE TURNS THE PLAN.
  `pass_of_sh`   a structure whose shape passes nothing passes nothing.
  ★★ `seat_returns_at_KR`   at every structure whose shape in front is the written one: the three
      marks on the structure in front, the library's own test on the view (`Block.Fits`) and the
      test on values with code (`valsK12`, TestValsB.lean): then the seat's asking returns, the
      test's sub-protocol accepts, and "the test has run to its end" holds of what it returns.

By what. Calls: `seat_returns`. The evaluations.

Limits. All limits of TestSeatAsks.lean, PlaceKeyRangesFull.lean and TestAtKeyRangesShape.lean
stand: four numbers of the place and the whole shape are a print's word, of a run on shapes over
stand-ins; NO THEOREM SAYS THAT A RUN OF THE DESCRIPTION COMES TO A STRUCTURE OF THIS SHAPE. The
three marks are premises. `valsK12` runs the test's own parts and is, under these premises,
equivalent to the sub-protocol's yes: so no accept is shown here. What the seat asks of the chain's
own state is not here. Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.K12.Honest.Shape.TestSeatAsks
import Johnson.Desc.K12.Honest.Shape.TestAtKeyRangesShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Key (asksOnRecord testEnded)
open H2K.Member (piKRFull)

/-- ★ **The guard is true at the closed place and the written shape.** -/
theorem guard_KR : guardK12 piKRFull shKRFull 0 (some 2) = true := by decide +kernel

/-- NEGATIVE TESTS, each with one thing turned. -/
theorem guard_KR_no :
    guardK12 piKRFull shKRFull 1 (some 2) = false ∧ guardK12 piKRFull shKRFull 0 none = false ∧
      guardK12 piKRFull shKRFull 0 (some 1) = false ∧
      guardK12 piKRFull
        { shKRFull with book := { shKRFull.book with place := shKRFull.book.place.dropLast } }
        0 (some 2) = false := by
  decide +kernel

/-- A structure whose shape passes nothing passes nothing. -/
theorem pass_of_sh {t : T12} (h : (testSh t).pass = .nothing) : t.pass = .nothing := by
  have h' : passSh t.pass = .nothing := h
  cases hp : t.pass with
  | nothing => rfl
  | claim row L =>
    rw [hp] at h'
    cases h'
  | single rows n =>
    rw [hp] at h'
    cases h'
  | switched out θ n =>
    rw [hp] at h'
    cases h'

/-- ★★ **THE LAW AT THIS PLACE.** ft: the number of the chain's first own tree. -/
theorem seat_returns_at_KR (t : T12) (hsh : testSh t = frontSh shKRFull 0 (some 2))
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).Fits ft rs cols)
    (hvals : valsK12 piKRFull t (rs.map noDigest)
      ((proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).shown ft rs cols) = true) :
    asksOnRecord piKRFull t = .ok () ∧
      ∃ t', (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).decide t (rs.map noDigest)
        ((proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).shown ft rs cols) = .ok t' ∧
        testEnded t' = true := by
  have ec : coreSh ⟨t.st, t.book, t.roots⟩ = shKRFull := congrArg TestSh.core hsh
  have eg : t.g = 0 := congrArg TestSh.g hsh
  have em : t.mask = some 2 := congrArg TestSh.mask hsh
  exact seat_returns (pass_of_sh (congrArg TestSh.pass hsh))
    (by rw [ec, eg, em]; exact guard_KR) ht hp hv ft rs cols hF hvals

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.guard_KR
#print axioms ProofFile.Honest.Sh.guard_KR_no
#print axioms ProofFile.Honest.Sh.pass_of_sh
#print axioms ProofFile.Honest.Sh.seat_returns_at_KR
