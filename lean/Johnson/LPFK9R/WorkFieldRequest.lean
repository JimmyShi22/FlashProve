-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/WorkFieldRequest.lean: IN THE GOALS' SCOPE THE PARAMETER FILE's SETTING ASKS NO BITS
OF PROOF OF WORK AT A ROUND WHOSE ERROR IS OF THE KIND "field" IN THE REQUEST's STAGE: (settingOf
X.P.frame).workOf .field .request = 0. Statements and proofs; one closed fact.

WHAT THE SENTENCE MEANS. It is a fact of the written setting (the parameter file's lines in scope
are the written lines `recordLines`): at such a round the format as written adds no grinding.
Nothing is waived here by anybody: the number is read off the setting.

Why. `k5_second_row_written` (Johnson/AtFull/Rounds/K5.lean) has a premise hw : k5Work G.W = w,
with k5Work W := (Params.settingOf W.P.frame).workOf .field .request; that file shows it at no w.
Wanted: w = 0, without an opening of the description.

THE END OF `work_at_blank` IS THIS FILE's OWN TEXT, NOT hw: a HAND COPY of k5Work's body (this
file does not import K5.lean). That the two are one is rfl by reading; until a line over both
files has met Lean nothing shows it.

  `work_written`: the closed fact at recordLines.
  `work_field_request`: **in scope, at publicOf's value.** X.P.frame = recordLines:
    `H2K.Sizes.pubFull_of_steps` (Johnson/Desc/K12/Law/Sizes/PublicOAtScope.lean) over
      `publicSteps_of`.
  `work_at_blank`: **at the blank ground's public part**: `ProofFile.Law.blankBy_W`, `ProofFile.Law.pub_public`.
Limits. At the second hash function alone (work_at_blank). No soundness statement.

-/
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model

/-- The closed fact. -/
theorem work_written :
    (OnBytes.Params.settingOf OnBytes.Params.recordLines).workOf .field .request = 0 := by decide

variable {P : VerifierAndGoals.PublicFiles}

/-- **In scope, at publicOf's value.** -/
theorem work_field_request {lay : Option ByteArray} {X : Verify.Public}
    (hS : VerifierAndGoals.InScope P = true) (hX : Verify.publicOf P.pol P.KL lay = .ok X) :
    (OnBytes.Params.settingOf X.P.frame).workOf .field .request = 0 := by
  rw [(H2K.Sizes.pubFull_of_steps hS (VerifiableInference.PlanWritten.publicSteps_of hX)).frame]
  exact work_written

/-- **At the blank ground's public part.** -/
theorem work_at_blank {ly : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (hS : VerifierAndGoals.InScope P = true)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol ly P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    (OnBytes.Params.settingOf G.W.P.frame).workOf .field .request = 0 := by
  rw [ProofFile.Law.blankBy_W hG]
  exact work_field_request hS
    ((VerifiableInference.PlanWritten.publicOfO_older P.pol P.KL (some ly)).symm.trans
      (ProofFile.Law.pub_public hZ))

end LPFK9

#print axioms LPFK9.work_written
#print axioms LPFK9.work_field_request
#print axioms LPFK9.work_at_blank
