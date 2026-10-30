-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/SizedTest.lean: two tests with code on what the planner sizes for a
proof file: at the full size's key its sizes and codes, and five fields of the first chain's
parameters as read back, are the written ones (`proofSizedFull`,
Johnson/Desc/Ok/PlanWritten/SizedLit.lean). Definitions alone.

What it is for. Laws on the proof file's description read closed facts off the written sizes. That
the planner's sizes at the public files are the written ones is no theorem: Lean's kernel does not
evaluate the planner at the full size. So it is asked at the run, as the written plan's test asks it
of the declared rounds (`seatPinnedProof`, Johnson/Desc/Ok/PlanWritten/Test.lean).

Why the comparison is written out. Four of the records' types (`TestSizes`, `LinLines`, `LinSized`,
`ProofSized`, OnBytes/Params/) bear no decidable equality where they are declared, and a file
beneath the verifier's list of tests is to hold definitions alone. So each record is compared field
by field, by the equality that the field's own type bears where it is declared. That no field is
left out is a theorem: `sameProof_eq` (Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean): a yes gives
the equation of whole records, which could not be proved of a comparison that left a field out.

Definitions.
  `sameTest`, `sameLines`, `sameLin`, `sameProof`: two records of the four types are the same.
  `sizedPinned k z`: at the full size's key (`fullKey`, Test.lean) z is `proofSizedFull`; at every
    other key: yes. k has to be the key of the strict scan of the public parameter file: any other k
    may open the arm that says yes. Do not call this with a k of your own: call `sizedPinnedAt`.
  `sizedPinnedAt P made`: the form to call: P: the strict scan of the parameter file; made: what the
    planner configured at the same public files.
  `firstPinned k f`, `firstPinnedAt P f`: the like for the parameters of a proof file's first chain
    as the reader makes them of the chain's parameter bytes (`First`, OnBytes/Params/Chains.lean).
    That record is another one than the planner's sizes: the blocks follow it. By the text of
    `configure` its fields `codes`, `lin` and `shape` are spelled of three fields of the planner's
    sizes, so the written side is `proofSizedFull`'s own fields; `pendingRows` is held to be 13 and
    `binding` to be a tree of depth 6 with 40 bytes of salt. The fields `given`, `layout`,
    `identifiers` and `more` are not asked: no law is known to read them off a written value.

What of OnBytes/Model/ is used: `PolScan`.

Limits. A yes says nothing of the key file's or the entry file's sizes, nor of the plans. That P and
made are of the same files is the caller's. At a key other than the full size's nothing is asked; at
the parameter file of the goals' scope the scan's three numbers are the full size's (`scan_sizes`,
Johnson/Goal/PlanValues/ScopeAtPlan.lean). Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.Ok.PlanWritten.Test
import OnBytes.Params.Configure
import OnBytes.Params.Chains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes.Params

/-- Two records of a test's sizes are the same. -/
def sameTest (a b : TestSizes) : Bool :=
  decide (a.group = b.group) && decide (a.t = b.t) && decide (a.stages = b.stages)

/-- Two records of what is free in the test on the table are the same. -/
def sameLines (a b : LinLines) : Bool :=
  decide (a.kLo = b.kLo) && decide (a.matrixRows = b.matrixRows) &&
    decide (a.folded = b.folded) && decide (a.omega = b.omega) && decide (a.own = b.own) &&
    decide (a.requests = b.requests) && decide (a.inputMaskRows = b.inputMaskRows) &&
    decide (a.oneTime = b.oneTime)

/-- Two records of the sizes of a test on the table are the same. -/
def sameLin (a b : LinSized) : Bool :=
  sameLines a.lines b.lines && decide (a.shape = b.shape) && decide (a.input = b.input) &&
    decide (a.table = b.table) && sameTest a.folded b.folded && sameTest a.omega b.omega &&
    sameTest a.own b.own && decide (a.batches = b.batches)

/-- Two records of a proof file's sizes and codes are the same. -/
def sameProof (a b : ProofSized) : Bool :=
  decide (a.set = b.set) && decide (a.codes = b.codes) && decide (a.link = b.link) &&
    sameTest a.last b.last && decide (a.request = b.request) && sameLin a.batch b.batch

/-- **At the full size's key**: z is the written value. At every other key: yes. Do not call this
with a k of your own: call `sizedPinnedAt`. -/
def sizedPinned (k : ℕ × ℕ × ℕ) (z : ProofSized) : Bool :=
  if k = fullKey then sameProof z proofSizedFull else true

/-- **The test on what the planner sized for a proof file.** P: the strict scan of the parameter
file; made: what the planner configured at the same public files. -/
def sizedPinnedAt (P : OnBytes.Model.PolScan) (made : Configured) : Bool :=
  sizedPinned (keyOfScan P) made.sized.proof

/-- **At the full size's key**: five fields of the first chain's parameters, as they were read back
from the parameter bytes, are those of the written sizes. At every other key: yes. Do not call this
with a k of your own: call `firstPinnedAt`. -/
def firstPinned (k : ℕ × ℕ × ℕ) (f : First) : Bool :=
  if k = fullKey then
    decide (f.codes = proofSizedFull.codes) && decide (f.lin = proofSizedFull.batch.shape) &&
      decide (f.shape = proofSizedFull.request) && decide (f.pendingRows = 13) &&
      decide (f.binding = ⟨6, 40⟩)
  else true

/-- **The test on the first chain's parameters as read back.** P: the strict scan of the parameter
file; f: what the reader made of the first chain's parameter bytes at the same public files. -/
def firstPinnedAt (P : OnBytes.Model.PolScan) (f : First) : Bool := firstPinned (keyOfScan P) f

end VerifiableInference.PlanWritten
