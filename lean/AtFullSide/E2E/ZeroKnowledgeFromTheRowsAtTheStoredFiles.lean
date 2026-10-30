-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/ZeroKnowledgeFromTheRowsAtTheStoredFiles.lean

This file shows that the three premises of zkOnServedRequests_inScope
(AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean) are met together at the stored full-size public files
VerifierAndGoals.storedPublicFiles, so that its conclusion holds there with no premise. Honest verifier; interactive
oracle proof; served requests.

Main statements
  zkOnServedRequests_atTheStoredFiles
      No premise. Conclusion: the reader returns some parameters pp at storedPublicFiles (hr), and
      ZeroKnowledgeOnServedRequests storedPublicFiles hr holds at the provers HonestProvers.ofThreeProvers
      (honestProvers storedPublicFiles (thePartsAt storedPublicFiles)), with the definition's three bounds offlineStops,
      linkStops and onlineStops at 0, 0 and 2^-174.

Limits
  * This file adds no statement on what a proof hides beyond ZeroKnowledgeOnServedRequests, as
    defined in VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean.
  * Every limit at the head of AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean applies here.
  * The file gives one example of public files that meet the three premises, and no more.
  * storedPublicFiles holds public files only. The library describes the weights of the stored example as
    synthetic; this file neither reads them nor checks that description.
  * That protocolDataWellFormed accepts at storedPublicFiles is the theorem theLive_zFull of AtFullSide/Top/LiveAtFull.lean,
    with the limits of that file. That protocolDataWellFormed accepts does not show that the verifier accepts any
    proof.
  * Some closed facts beneath these proofs are checked by evaluation in Lean's kernel, and no
    independent checker has replayed them.

Built on
  * AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean: zkOnServedRequests_inScope.
  * AtFullSide/Top/LiveAtFull.lean: theLive_zFull.
  * VerifierAndGoals.filesRead.full: storedPublicFiles is in scope and the reader accepts it.
-/
import AtFullSide.E2E.ZeroKnowledgeFromTheRows
import AtFullSide.Top.LiveAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- The default instance for the table of scales is removed, so that a statement that reads such a
table has to name it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open OnBytes.Slice (frS)
open VerifierAndGoals (readFiles storedPublicFiles)

attribute [local instance high] oneAtGPad oneAtGValue oneAtGDefault

/-- The conclusion of zkOnServedRequests_inScope at the stored full-size public files storedPublicFiles: they
are in scope, the reader accepts them, and protocolDataWellFormed accepts them. -/
theorem zkOnServedRequests_atTheStoredFiles :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles storedPublicFiles = .ok pp),
      ZeroKnowledgeOnServedRequests storedPublicFiles hr
        (HonestProvers.ofThreeProvers (honestProvers storedPublicFiles (thePartsAt storedPublicFiles))) 0 0
        (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) :=
  let ⟨scope, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr, zkOnServedRequests_inScope scope AtFullSide.Top.theLive_zFull hr⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.zkOnServedRequests_atTheStoredFiles
