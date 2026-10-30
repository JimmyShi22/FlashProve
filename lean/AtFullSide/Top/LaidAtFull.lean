-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Top/LaidAtFull.lean: a control. Four public premises (scope, the reading, protocolDataWellFormed,
LaidAt) of the implications on the field sessionStops (Johnson/FrontRoad/SessionStopsOfPinned.lean,
SessionStopsOfTrace.lean, ParOwn.lean) and of the statements on the planner's test
(Johnson/FrontRoad/ParOwnChecksSpec.lean) are met together at the stored full-size public files
VerifierAndGoals.storedPublicFiles: the files are in scope, they are read, the test protocolDataWellFormed accepts, and LaidAt holds at
some public part, places and chain. One theorem, premises_met_at_full; its statement is
Spec.premises_met_at_full in that last file.

What it is for. Each of these statements, but for Spec.missed_at_none and this control, has the
four, or three of them, as premises. The implications of the first three files have one public
premise more, on the planner's test: Spec.planner_passes_at_parOwn gives it, at parOwn and the
planner's own four arguments, wherever scope, the reading and LaidAt hold; planner_passes_at_full
(AtFullSide/Top/PlannerAtFiles.lean) applies it at VerifierAndGoals.storedPublicFiles. If no public files met them
together, all would hold idly. Here is one member.

The pieces, and with which grade each comes.
  In scope: VerifierAndGoals.inScope_full (Johnson/Goal/Files/ScopeExample.lean), in the main library: by that
      file's head, from five evaluations in Lean's kernel (decide +kernel) over the stored bytes.
  Read: VerifierAndGoals.read_full_ref (Johnson/Goal/Files/FilesReadAtRef.lean), in the main library: from
      checks that Lean's kernel has evaluated (Johnson/Goal/Files/FilesReadChecks.lean).
  protocolDataWellFormed accepts, and the maker of the proof file's description returns (a function of the three
      public files: no proof is made or read): theLive_zFull and theProofLaid_zFull_returns
      (AtFullSide/Top/LiveAtFull.lean), in this side library. By that file's head: many closed facts
      beneath are proved by evaluation in Lean's kernel, and the two facts on the layout file rest
      on kernel_rfl too; no compiled code; no axiom beyond Lean's three; nothing in the main library
      imports it, so only a build of the side library shows a break in it; no independent checker
      has replayed it.
  From the maker's value to LaidAt: laid_opensK (Johnson/P5J/LaidOpens.lean), in the main library: a
      general theorem, at all files; its own proof evaluates nothing.

Why here. The third piece stands in the side library, and the main library imports nothing of it. So
what that piece's file says of itself holds of this file too: only a build of the side library shows
a break in it, and no independent checker has replayed it.

Limits.
  At VerifierAndGoals.storedPublicFiles alone: one stored set of files. Nothing is said of any other public files in
      scope.
  All limits of AtFullSide/Top/LiveAtFull.lean hold. Among them: VerifierAndGoals.storedPublicFiles is three terms written
      in Ladder/Stored.lean, which no Lean code ties to files in a folder or to files that a program
      writes; the example's weights are synthetic; it is at the earlier hash OnBytes.secondHashFunction and at
      the constant fixedConfigurationDigest in the digest's place.
  The public part, the places and the chain stand under "there are": they are not named.
  Nothing is said of any prover. The premises on a prover (the pin, hR, the premise on the trace)
      are not touched: no parameters are known at which all premises of any of the implications hold
      together.
  Nothing is said on hiding, completeness or soundness. That protocolDataWellFormed accepts is no sign that the
      verifier accepts any proof.
-/
import AtFullSide.Top.LiveAtFull
import Johnson.Goal.Files.ScopeExample
import Johnson.Goal.Files.FilesReadAtRef
import Johnson.P5J.LaidOpens
import Johnson.FrontRoad.ParOwnChecksSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top

/- The three files' bytes are not to be unfolded: the proof below reads no byte of them. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles

/-- A control; it counts as no goal. **The four public premises are met together at the stored
full-size files.** -/
theorem premises_met_at_full : OnBytes.FrontRoad.Spec.premises_met_at_full := by
  obtain ⟨pp, hpp, -⟩ := VerifierAndGoals.read_full_ref
  obtain ⟨⟨D, r⟩, hP⟩ := theProofLaid_zFull_returns
  obtain ⟨Zp, Np, cF, L, -⟩ := P5J.laid_opensK (pol := VerifierAndGoals.storedPublicFiles.pol)
    (lay := VerifierAndGoals.storedPublicFiles.lay) (KL := VerifierAndGoals.storedPublicFiles.KL) (D := D) (r := r) hP
  exact ⟨pp, D, r, Zp, Np, cF, VerifierAndGoals.inScope_full, hpp, theLive_zFull, L⟩

end AtFullSide.Top

#print axioms AtFullSide.Top.premises_met_at_full
