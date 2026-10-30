-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/CompilerPublicAtFiles.lean: the public conditions for index privacy have a
  member at the release's description.

1.  WHAT IS CLAIMED: of the wiring alone, with no prover. Nothing is claimed of completeness or zero
    knowledge.
2.  The public conditions for index privacy are the library's conditions that read no prover, coin
    or simulator, at all seeds.
3.  So the theorem on these conditions at the release's description gives them at each value of the
    two readings, within its bounds
    on copies and sessions, for public files in scope, at any search limits.
4.  This file imports the release's description, so it carries that description's imports. No
    statement imports this file.
-/
import VerifiableInference.Final.CompilerTheorems
import E2E.PremisesAtFiles

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {L : HolographicProtocol I X} {offlineRoundMarks : RoundSplits L.offline.shape} {linkRoundMarks : RoundSplits L.link.shape}

/-- The public conditions are the library's, at all seeds, at the numbers of the statement on zero knowledge. -/
theorem publicForIndexPrivacy_iff (w : HashLayout L offlineRoundMarks linkRoundMarks) (N : Budget) (M sessionsPerCopy : ℕ)
    (capT capL capB : ℕ → ℕ) :
    PublicForIndexPrivacy w N M sessionsPerCopy capT capL capB ↔
      AtPublicFiles.Premises.NoProverSide w.queryLayout w.seedQueries w.answerCode (fun _ => True)
        (numbersOf N sessionsPerCopy) M capT capL capB :=
  ⟨fun h => ⟨h.tableHides, h.firstTableBudget, h.copyBudget, by simp [numbersOf],
      h.readsIgnoreNoncesOffline, h.readsIgnoreNoncesLink, h.readsIgnoreNoncesOnline,
        h.layoutIsLawful,
      h.everyRoundHasAFormat, h.noncesAreReadBackOffline, h.noncesAreReadBackLink,
      h.noncesAreReadBackOnline, h.seedQueriesAreFirstTries, h.marksAreCoherent,
      h.verifiersReadWhereTheySay⟩,
    fun h => ⟨h.reads, h.budget₀, h.budget₁, h.freeT, h.freeL, h.freeB, h.wires, h.fmt, h.backT,
      h.backL,
      h.backB, h.plain, h.coherent, h.isLocal⟩⟩

/-- The counts at the release's files, with the stops as letters. -/
def budgetAtFiles (offlineStops linkStops onlineStops : ℝ≥0∞) : Budget :=
  ⟨44040191, 62, 62, 62, 64, offlineStops, linkStops, onlineStops⟩

set_option maxRecDepth 100000 in
/-- **For index privacy.** The member at the release's description. -/
theorem public_at_description (Z : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (M s1 : ℕ)
    (hM : M + 1 ≤ 710324) (hs : s1 ≤ 688127) (offlineStops linkStops onlineStops : ℝ≥0∞)
    (capT capL capB : ℕ → ℕ) (c : Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    PublicForIndexPrivacy (layoutOf (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription) Z c m).toHashLayout
      (budgetAtFiles offlineStops linkStops onlineStops) M s1 capT capL capB :=
  (publicForIndexPrivacy_iff _ _ _ _ _ _ _).2
    (AtPublicFiles.Premises.noProverSide_description Z scope M s1 hM hs 0 0 0 offlineStops linkStops
      onlineStops
      capT capL capB c m)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.publicForIndexPrivacy_iff
#print axioms VerifiableInference.Compilation.budgetAtFiles
#print axioms VerifiableInference.Compilation.public_at_description
