-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/K4Sent/Written.lean: K4's one closed test on the plan, at the written table of steps
and the written rounds of the full size, by Lean's kernel.

What it says.
  `sent_written`      k4SentOn cutWritten ‹the written first chain's entries› = true: an evaluation
                      in Lean's kernel. cutWritten: the 477 rows of
                      Johnson/AtFull/Cut/CutWrittenLit.lean; the entries: `dryProofFull.1`'s
                      (Johnson/G/DryProofLit.lean).
  `k4SentB_written`   k4SentB Z = true at every public part Z whose table of steps is cutWritten and
                      whose first chain's declared rounds have these entries.
  Two negative tests, by the kernel too, each in the form "all twelve steps stand in the table, AND
  the twin rejects", so that a lacking step cannot pass for a rejection; in each the outcome hangs
  on where the written rounds send their roots:
  `sent_shifted_no`    the written entries less their first: every window then begins one round
                      later.
  `sent_longerStep_no` the first step of the table one round longer: every later window then begins
                      one round later.
  Two general laws, no tests of `sent_written`: the twin rejects at EVERY table where there is no
  entry (`k4SentOn_noEntries`), and at every table and all entries where a segment's step
  «‹link›.0.call» lacks (`sentOn_noStep`).

Limits. THAT ANY PUBLIC PART HAS THESE TWO VALUES IS SHOWN NOWHERE HERE: the two equations are
premises. Written values of one set of public files, with synthetic weights. Nothing on soundness.

-/
import Johnson.Road.K4.K4SentAt
import Johnson.G.DryProofLit
import Johnson.AtFull.Cut.CutWrittenLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K4Sent

open OnBytes.Road.K4 (k4SentB k4SentOn k4SentB_eq sentOn)
open VerifiableInference.Desc.First (Cut)
open Johnson.G (dryProofFull)
open Johnson.AtFull.Cut (cutWritten)

/-- The written first chain's entries. -/
def esWritten : List Fmt.Entry := dryProofFull.1.map (·.1.entry)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **K4's closed test accepts at the written values.** -/
theorem sent_written : k4SentOn cutWritten esWritten = true := by decide +kernel

/-- All twelve steps «G‹g›.0.call» stand in a table of steps. -/
def stepsThere (cuts : List Cut) : Bool :=
  (List.range 12).all fun g => cuts.any fun c => c.look == "G" ++ toString g ++ ".0.call"

/-- A table of steps with the step of that name one round longer. -/
def takeUp (look : String) (cuts : List Cut) : List Cut :=
  cuts.map fun c => if c.look == look then { c with take := c.take + 1 } else c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A negative test: the twelve steps stand, and at the written entries less their first the twin
rejects. -/
theorem sent_shifted_no :
    (stepsThere cutWritten && !k4SentOn cutWritten (esWritten.drop 1)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A negative test: with the table's first step one round longer the twelve steps stand, and the
twin rejects. -/
theorem sent_longerStep_no :
    (stepsThere (takeUp "G0.0.call" cutWritten) &&
      !k4SentOn (takeUp "G0.0.call" cutWritten) esWritten) = true := by
  decide +kernel

/-- A general law: where a segment's step lacks in the table, its test rejects, at all entries. -/
theorem sentOn_noStep (cuts : List Cut) (es : List Fmt.Entry) (link : String)
    (h : (cuts.any fun c => c.look == link ++ ".0.call") = false) :
    sentOn cuts es link = false := by
  unfold sentOn
  rw [h]
  rfl

/-- A general law: at no entry the twin rejects, at every table of steps. -/
theorem k4SentOn_noEntries (cuts : List Cut) : k4SentOn cuts [] = false := by
  refine Bool.eq_false_iff.2 fun h => ?_
  unfold k4SentOn at h
  have h0 : sentOn cuts [] ("G" ++ toString 0) = true :=
    List.all_eq_true.1 h 0 (List.mem_range.2 (by decide))
  unfold sentOn at h0
  rw [List.drop_nil, List.take_nil, Bool.and_eq_true] at h0
  exact absurd h0.2 (by decide)

/-- **`k4SentB Z` is true wherever Z's table of steps and entries are the written ones.** -/
theorem k4SentB_written {Z : ProofFile.Pub} (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten) : k4SentB Z = true := by
  rw [k4SentB_eq, hc, he]
  exact sent_written

#print axioms Johnson.AtFull.K4Sent.sent_written
#print axioms Johnson.AtFull.K4Sent.sent_shifted_no
#print axioms Johnson.AtFull.K4Sent.sent_longerStep_no
#print axioms Johnson.AtFull.K4Sent.sentOn_noStep
#print axioms Johnson.AtFull.K4Sent.k4SentOn_noEntries
#print axioms Johnson.AtFull.K4Sent.k4SentB_written

end Johnson.AtFull.K4Sent
