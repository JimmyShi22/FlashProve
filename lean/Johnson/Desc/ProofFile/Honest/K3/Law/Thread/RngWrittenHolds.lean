-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RngWrittenHolds.lean: the closed test `rngWrittenB`
(Honest/K3/Law/Thread/RngHead.lean) accepts: a theorem without a hypothesis. One definition; one
closed fact and two controls by Lean's kernel, at a written list; theorems.

Terms. Honest/K3/GLOSSARY.md; Honest/K3/Law/Thread/RngHead.lean. In this file: the written table is
`cutWritten` (477 rows); the written list of places is `spotsWritten` (282 places;
Johnson/AtFull/Desc/SpotsWritten.lean).

Why. Lean's kernel does not get through `rngWrittenB` as it stands: the table's places are numbered
by `spotsOf`, whose `headOf` cuts a name with `String.splitOn`, and there the reduction sticks. The
library holds the way round: `spots_written`: `spotsOf cutWritten = some spotsWritten`, by general
laws and one decision of the kernel. Behind it the closed test is a test on a written list, in
which no name is cut.

What is defined. `rngSpotsB ps`: the test at a list of places: `rngIn` (Honest/K3/Lot.lean) returns
a number at each of the 25 links.

What is shown.
  `rngAllB_spots`: `rngAllB cs` is `rngSpotsB` at the places of cs: by `rfl`.
  `rngSpots_written`: by Lean's kernel: the test accepts the written list.
  `rngSpots_miss_place`: a control, by Lean's kernel: without its fifth place, "G0:5", the one place
    of the smallness test's kind in link 0, the written list is refused.
  `rngSpots_miss_link`: a control, by Lean's kernel: at link 25 `rngIn` returns nothing.
  `rngWritten_holds`: the main theorem: rngWrittenB = true. No hypothesis.
  `rng_head_paid`, `site_digits_paid`: `rng_head_of` and `site_digits_of` without their hypothesis
    `hW`; `P5J.AtMgA` (`h`) and l < 25 (`hl`) remain.

Imported. Honest/K3/Law/Thread/RngHead.lean; Johnson/AtFull/Desc/SpotsWritten.lean.

Limits. At the written table alone: that its rows are what the planner makes of any public files is
not said here (`cuts_head` says it under `P5J.AtMgA`). Two controls. On public data alone. At the
full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngHead
import Johnson.AtFull.Desc.SpotsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spotsWritten spots_written)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- At a list of places: `rngIn` returns a number at each of the 25 links. -/
def rngSpotsB (ps : List Spot) : Bool := (List.range 25).all fun l => (rngIn ps l).isSome

/-- `rngAllB` is this test at the table's places. -/
theorem rngAllB_spots (cs : List VerifiableInference.Desc.First.Cut) :
    rngAllB cs = rngSpotsB ((spotsOf cs).getD []) := rfl

set_option maxRecDepth 1000000 in
/-- **The closed fact**, by Lean's kernel: the test accepts the written list of places. -/
theorem rngSpots_written : rngSpotsB spotsWritten = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel: without its fifth place, "G0:5", the written list is refused. -/
theorem rngSpots_miss_place : rngSpotsB (spotsWritten.eraseIdx 4) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel: there is no link 25. -/
theorem rngSpots_miss_link : (rngIn spotsWritten 25).isSome = false := by decide +kernel

/-- **The closed test accepts.** No hypothesis. -/
theorem rngWritten_holds : rngWrittenB = true := by
  have e : (spotsOf cutWritten).getD [] = spotsWritten := by
    rw [spots_written]
    rfl
  unfold rngWrittenB
  rw [rngAllB_spots, e]
  exact rngSpots_written

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- `rng_head_of` without `hW`. Conditional on `P5J.AtMgA`. -/
theorem rng_head_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    (rngIn ((spotsOf Zp.cuts).getD []) l).isSome = true :=
  rng_head_of h rngWritten_holds l hl

/-- `site_digits_of` without `hW`: a site at every link below 25, of either sort. Conditional on
`P5J.AtMgA`. -/
theorem site_digits_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (d : Bool) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = d ∧ s.at_.place = IM.k3Place l d ∧
      s.at_.place ∈ P5J.At.ps :=
  site_digits_of h rngWritten_holds l hl d

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.rngAllB_spots
#print axioms ProofFile.Honest.K3.Law.AtThr.rngSpots_written
#print axioms ProofFile.Honest.K3.Law.AtThr.rngSpots_miss_place
#print axioms ProofFile.Honest.K3.Law.AtThr.rngSpots_miss_link
#print axioms ProofFile.Honest.K3.Law.AtThr.rngWritten_holds
#print axioms ProofFile.Honest.K3.Law.AtThr.rng_head_paid
#print axioms ProofFile.Honest.K3.Law.AtThr.site_digits_paid
