-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineClausesAtTheFiles.lean: the three statements on the offline honest prover that the
definition of honest-verifier zero knowledge asks: for one run, for the interactive oracle proof,
before any hashing.

The statement of honest-verifier zero knowledge on served requests (`ZeroKnowledgeOnServedRequests`,
VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean) asks, run by run, three things of each of
the three honest provers (`RunByRun`, VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean).
This file proves the three for the offline honest prover `offlineProver (thePartsAt Z)`; the like
statements on the link's and the online prover are not here. Its only premises are three tests on
the public files `Z`: `InScope Z = true`, `protocolDataWellFormed (asDescriptionFiles Z) = true` and `readFiles Z = .ok pp`.

Two words. A stop is a list of the verifier's messages at which the prover aborts: a public stop for
a reason that reads public data alone, a private stop for a reason that may read the private input.
A row pairs a part of the prover with its simulator.

  `offline_clauses_at_the_files`: at every index in range, every randomness of the committed table
      and every out-of-domain seed: (1) the table of which the prover speaks is the committer's
      encoding `(protocolAtFiles Z).encodeIndex i r`; (2) `ExactOutsideStops`: at every list of the verifier's messages
      with its proof-of-work bits set to 0, outside the prover's private stops, what one run shows
      to the honest verifier has exactly the distribution that the named simulator makes; (3)
      `PrivateStopsAtMost … 0`: among the challenges that pass the proof-of-work tests, the share of
      private stops is 0
  `offline_rows_at_the_files`: the three facts that the general theorem on a prover built from parts
      asks of the rows: `IsProvK`, `Owed` at the muted rows (`.mute`) under the key file's relation,
      and `.owns = true`: every owner has a row
  `offline_clauses_at_the_written_files`: at the stored full-size public files `storedPublicFiles` all three
      premises are theorems, so the premises can be met
  `theLots_at_the_laid_table`: a lemma: the value `theKeyLots` of `TheLots`
      (E2E/LotKeyAcceptsAtTheFiles.lean; its parameters: AtFullSide/Honest/TheKeyLetters.lean) in
      the form that E2E/OfflineClausesOfLots.lean takes: the proximity tests' tables `ttValue Z d
      K₀` are `ttLaid Z d K₀ publicPart B` (`ttAt_is_ttValue`, E2E/LotJoinSharedAtValue.lean)

On the prover's coins. No parameter is left that a premise ties to the coins: the invariants, their
parameters and the tables are named terms; the explicit input is the key that the committer makes of
index, table randomness and seed; the condition at each proximity test's second part is shown at
every input in the relation, at every coin and every well-formed list of challenges
(`threads_at_spent`, E2E/OfflineLotsSpent.lean: one seed, the relation's own, then every coin). No
distribution here is conditioned on the coins.

What the simulator is given. Beside the verifier's messages, two things that are made from the
index: the instance, which is the out-of-domain seed with the honest answers at it, and the
committed table's symbols at the positions that the verifier reads. The three statements say that
one offline run, seen by the honest verifier, shows nothing beyond these. That these two themselves
tell nothing of the index is another statement, which is not made here; only both together speak of
the index.

The public stops are bounded by none of the three statements: if every list of messages were a
public stop, both sides would show nothing and the statements would hold vacuously. That their
measure is 0 is a field of `offlineDebts_at_the_files` (E2E/LotKeyAcceptsAtTheFiles.lean), at the
same prover.

The domain. Every index in range, every table randomness, every seed of the protocol's type of seeds
(a seed's factor has the type `OnBytes.Slice.NZ`, OnBytes/Slice/RecordRead.lean: the elements other
than 0). That the verifier accepts this prover is stated in E2E/LotKeyAcceptsAtTheFiles.lean at
indices that serve a request, which is a narrower domain.

Limits. The three statements are of the offline prover alone; what they give together with the like
statements on the link's and the online prover is not stated here. They are about the prover as
written in Lean, at the key file's description, and about no program. `ExactOutsideStops` holds at
lists whose proof-of-work bits are set to 0, outside the private stops, and at the simulator named.
The limits told in the files of the sixteen rows and in the files that assemble `TheLots` stand. For
public files in scope, at the written book. Zero knowledge of the protocol is neither stated nor
proved here.
-/
import E2E.OfflineClausesOfLots
import E2E.LotKeyAcceptsAtTheFiles
import E2E.LotJoinSharedAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.AtFiles.Full (PF)
open _root_.Desc.K14.Honest (Eight)
open ProofFile.Honest.K12.AtKey (keepsKey)
open AtPublicFiles.KeyStandFull (idleNm_tenant)
open AtPublicFiles.KeyStandWalked.Lots (ttValue)
open AtFullSide.Honest (TheKeyLetters.rest)
open AtFullSide.Honest.TheKeyLetters (lens numbers meaning tableUnused validShared publicPart later firstSaid
  TheKeyLots theKeyLots)
open VerifiableInference.Compilation (ExactOutsideStops PrivateStopsAtMost offlineSimulatorAt rangeAtFiles)
open AtPublicFiles.KeyStoredTie (stored_at_description)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles storedPublicFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) clausesAtTheFilesPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) clausesAtTheFilesValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) clausesAtTheFilesDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}

/-- **The value of `TheLots` at the key file's named parameters, with the proximity tests' tables in
the form `ttLaid`.** -/
theorem theLots_at_the_laid_table (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (B : Eight (parKey d.source PF)) :
    TheLots (Z := Z) lens numbers (meaning Z) (tableUnused Z K₀) (ttLaid Z d K₀ publicPart B) (TheKeyLetters.rest Z K₀) keepsKey (validShared Z) publicPart d
      (firstFamilyAt d (later Z d K₀))
      (fun w x => lastThread lens numbers (meaning Z) (tableUnused Z K₀) (ttLaid Z d K₀ publicPart B) (TheKeyLetters.rest Z K₀) keepsKey (validShared Z) publicPart d
        (later Z d K₀) (firstSaid Z d K₀) w x)
      (firstSaid Z d K₀)
      (fun w x => lastSaid lens numbers (meaning Z) (tableUnused Z K₀) (ttLaid Z d K₀ publicPart B) (TheKeyLetters.rest Z K₀) keepsKey (validShared Z) publicPart d
        (later Z d K₀) (firstSaid Z d K₀) w x) := by
  have L : TheLots (Z := Z) lens numbers (meaning Z) (tableUnused Z K₀) (ttValue Z d K₀) (TheKeyLetters.rest Z K₀) keepsKey (validShared Z) publicPart d
      (firstFamilyAt d (later Z d K₀))
      (fun w x => lastThread lens numbers (meaning Z) (tableUnused Z K₀) (ttValue Z d K₀) (TheKeyLetters.rest Z K₀) keepsKey (validShared Z) publicPart d
        (later Z d K₀) (firstSaid Z d K₀) w x)
      (firstSaid Z d K₀)
      (fun w x => lastSaid lens numbers (meaning Z) (tableUnused Z K₀) (ttValue Z d K₀) (TheKeyLetters.rest Z K₀) keepsKey (validShared Z) publicPart d
        (later Z d K₀) (firstSaid Z d K₀) w x) :=
    theKeyLots hd scope live hK₀
  have e : ttValue Z d K₀ = ttLaid Z d K₀ publicPart B :=
    (ttAt_is_ttValue (Z := Z) (K₀ := K₀) hs scope publicPart B).symm
  rw [e] at L
  exact L

/-- **The three offline statements at the protocol's offline honest prover** (honest verifier, one
run, before hashing): its table is the committer's encoding; at every list of messages with its
proof-of-work bits set to 0, outside the private stops, what it shows has exactly the distribution
of the named simulator; among the challenges that pass the proof-of-work tests the private stops'
share is 0. -/
theorem offline_clauses_at_the_files (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (scope : InScope Z = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) :
    ∃ d : OfflineDescription, offlineDescription Z = .ok d ∧
      thePartsAt Z = partsOfDescription d ∧ OfflineSidesAreWhole (thePartsAt Z) ∧
      ((∀ i r e, (offlineProver (thePartsAt Z)).ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r) ∧
        ExactOutsideStops (offlineProver (thePartsAt Z))
          (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline.cleared
          (offlineSimulatorAt d (thePartsAt Z) (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d))) ∧
        PrivateStopsAtMost (offlineProver (thePartsAt Z))
          (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline 0) := by
  obtain ⟨d, hd, hs⟩ := offlineDescription_named Z live
  obtain ⟨K₀, hK₀⟩ := AtPublicFiles.KeyBook.full_made
  obtain ⟨B⟩ := eight_at hs scope
  obtain ⟨-, x₀, -, -⟩ := VerifiableInference.Compilation.someRequestIsServed_holds Z scope hr
  exact ⟨d, hd, thePartsAt_ok hd, offlineSides_whole scope live,
    offline_clauses_of_lots lens numbers (meaning Z) (tableUnused Z K₀) (TheKeyLetters.rest Z K₀) (validShared Z) publicPart B (later Z d K₀) hd scope live
      hK₀ hs idleNm_tenant (fun _ => idle_cells) x₀
      (theLots_at_the_laid_table hd scope live hK₀ hs B)⟩

/-- **The three facts that the general theorem on a prover built from parts asks of the rows.** -/
theorem offline_rows_at_the_files (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (scope : InScope Z = true) :
    ∃ d : OfflineDescription, offlineDescription Z = .ok d ∧
      IsProvK Z (keyFileDescription d.source d.numbers d.later) (thePartsAt Z).book (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d))
        ((thePartsAt Z).prover d) ∧
      Owed (keyFileDescription d.source d.numbers d.later) (thePartsAt Z).book
        ((cmKey Z).proverAt 0 ((thePartsAt Z).prover d)) (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d)).mute (KeyRel Z) ∧
      (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d)).owns = true := by
  obtain ⟨d, hd, hs⟩ := offlineDescription_named Z live
  obtain ⟨K₀, hK₀⟩ := AtPublicFiles.KeyBook.full_made
  obtain ⟨B⟩ := eight_at hs scope
  exact ⟨d, hd, offline_rows_three_of_spent lens numbers (meaning Z) (tableUnused Z K₀) (TheKeyLetters.rest Z K₀) (validShared Z) publicPart B (later Z d K₀)
    hd scope live hK₀ hs idleNm_tenant
    (lotsSpent_of_lots lens numbers (meaning Z) (tableUnused Z K₀) (ttLaid Z d K₀ publicPart B) (TheKeyLetters.rest Z K₀) keepsKey (validShared Z) publicPart hd
      scope live hK₀ idleNm_tenant ProofFile.Honest.K12.AtKey.keepsKey_same
      (fun s s' h => (ProofFile.Honest.K12.AtKey.keepsKey_zero s s').1 h)
      (fun s s' h => (ProofFile.Honest.K12.AtKey.keepsKey_eleven s s').1 h) (fun _ => idle_cells)
      (theLots_at_the_laid_table hd scope live hK₀ hs B))⟩

/-- **The premises can be met: at the stored full-size public files** all three are theorems: the
files are in scope, their own test says yes, and they are read. -/
theorem offline_clauses_at_the_written_files :
    ∃ d : OfflineDescription, offlineDescription storedPublicFiles = .ok d ∧
      thePartsAt storedPublicFiles = partsOfDescription d ∧ OfflineSidesAreWhole (thePartsAt storedPublicFiles) ∧
      ((∀ i r e, (offlineProver (thePartsAt storedPublicFiles)).ext (i, r, e) = (protocolAtFiles storedPublicFiles).encodeIndex i r) ∧
        ExactOutsideStops (offlineProver (thePartsAt storedPublicFiles))
          (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles storedPublicFiles).validT w y) (workAtFiles storedPublicFiles).offline.cleared
          (offlineSimulatorAt d (thePartsAt storedPublicFiles) (rowsAtTheTerm (files := storedPublicFiles) d (theSimulators (files := storedPublicFiles) d) (theLetters (files := storedPublicFiles) d))) ∧
        PrivateStopsAtMost (offlineProver (thePartsAt storedPublicFiles))
          (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles storedPublicFiles).validT w y) (workAtFiles storedPublicFiles).offline 0) := by
  obtain ⟨pp, hr⟩ := AtFullSide.Honest.TheKeyLetters.read_zFull
  exact offline_clauses_at_the_files AtFullSide.Top.theLive_zFull VerifierAndGoals.inScope_full hr

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.offline_clauses_at_the_written_files
#print axioms AtPublicFiles.OfflineRows.theLots_at_the_laid_table
#print axioms AtPublicFiles.OfflineRows.offline_clauses_at_the_files
#print axioms AtPublicFiles.OfflineRows.offline_rows_at_the_files
