-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanInScope.lean: `WrittenAt Z` (Johnson/Road/K4/K4PlanTied.lean) IN THE GOALS'
SCOPE, FROM TWO PINS OF OTHER FILES. `written_at_in_scope`
(Johnson/P5T/WrittenAtScope.lean) says: in scope, where the plain road returns Z, the pin
`madePinnedAt` accepts and the verifier's own value is laid, five parts of Z are the written values:
`WrittenAt`'s five equations, as a conjunction. Here the projection, and K4PlanTied's three ends.
Four theorems: calls.

  `writtenAt_in_scope`: the structure, from the scope, the road's return, the pin's accept and the
    laid value.
  `seamClosed_in_scope`, `programs_in_scope`, `groups_in_scope`: so K4PlanTied's three ends.

Limits. K04_law IS NOT PROVED BY THIS. That a verifier asks the pin, and that the pin accepts at any
files, is said by nothing here.
-/
import Johnson.Road.K4.K4PlanTied
import Johnson.P5T.WrittenAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.Desc.First (groupsAreMembers)

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF}

/-- **In scope, where the pin accepts, five parts of Z are the written values.** -/
theorem writtenAt_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) : WrittenAt Z :=
  have w := P5T.written_at_in_scope hW h hy hl
  ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2⟩

section
variable (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
  (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
  (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
include hW h hy hl

theorem seamClosed_in_scope {g : ℕ} (h0 : 0 < g) (hg : g < 12) :
    seamClosedB (sentAt Z).layout (numAt Z) (arrAt Z) (numbersAt Z) g = true :=
  seamClosed_at (writtenAt_in_scope hW h hy hl) h0 hg

theorem programs_in_scope :
    (sentAt Z).codes.lengthsOk = true ∧ OnBytes.reqShapeOk (sentAt Z).shape = true ∧
      OnBytes.reqLayoutOk (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout = true :=
  programs_at (writtenAt_in_scope hW h hy hl)

theorem groups_in_scope : groupsAreMembers (numbersAt Z) (lastAt Z) (lists0At Z) = true :=
  groups_at (writtenAt_in_scope hW h hy hl)

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.writtenAt_in_scope
#print axioms OnBytes.Road.K4.seamClosed_in_scope
#print axioms OnBytes.Road.K4.programs_in_scope
#print axioms OnBytes.Road.K4.groups_in_scope
