-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/HonestProverLaws.lean: what E2E/TheHonestProver.lean's online and offline provers
are, by the equations of the functions on which they match, and the two propositions of that file
which follow from the library.

  makerReturns              the proposition MakerReturns holds at all public files
  offlineDescriptionNamed   the proposition OfflineDescriptionNamed holds at all public files
  runValueCount             the proposition RunValueCount holds
  onlineProver_eq, offlineProver_eq   the provers at a return of these functions
  matrixInRange_iff         the term's range is the object's
  trace_return, key_return  what the maker's prover reads as trace and key
  proverAt_return           where the table is the committer's, the committer's share leaves the
                            prover as it is
  plug_return               where the table is the committer's, the socket's prover is the maker's
  onlineProverAt_rows       rows whose parts are the prover's own give the family

Limits.
  * Nothing is said of what the provers play.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import AtFullSide.K12.MakerReturnsAtLive
import E2E.TheHonestProverStatements
import E2E.MatrixReaderAtIndex
import Johnson.LPFPol.LiveAtPolicy

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles

/-- **The maker returns at the term's filling where the verifier's test on the public files says
yes.** -/
theorem makerReturns (files : VerifierAndGoals.PublicFiles) : MakerReturns files := by
  intro scope live
  obtain ⟨_, read⟩ := LPFPol.read_of_scope scope
  exact AtFullSide.K12.maker_returns files scope read live

/-- **The range of the term is the range of the object**: it is the test that a matrix holds an
index. -/
theorem matrixInRange_iff (matrix : FullSizeMatrix) :
    matrixInRange matrix ↔ VerifiableInference.OnPublicFiles.Flat.InRange matrix := by
  show (VerifiableInference.OnPublicFiles.Flat.indexOf matrix).isSome = true ↔ _
  unfold VerifiableInference.OnPublicFiles.Flat.indexOf
  split <;> simp_all

variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineReturn files}

/-- The trace of the maker's prover is the matrices' reader's at the public part, so a served
request has one. -/
theorem trace_return (made : onlineMaker files = .ok returned) :
    returned.H.trace = matrixInput.trace returned.Z :=
  (atPure_ok made).2.2.2.1

/-- The key of the maker's prover is `pureKey`. -/
theorem key_return (made : onlineMaker files = .ok returned) : returned.H.key = pureKey :=
  (atPure_ok made).2.2.2.2.2.2.1

end ProofFile.Honest.Term

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Sides)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open P5J (TS)

local instance (priority := high) nonemptyPadAtLaws : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValueAtLaws : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValueAtLaws : Inhabited RunValue := ⟨fun _ => 0⟩

/-- **The matrix's reader and the index's reader agree.** -/
theorem matrixReaderIsTheIndexReader : MatrixReaderIsTheIndexReader :=
  ProofFile.Honest.Term.matrixReaderIsIndexReader

set_option synthInstance.maxHeartbeats 400000 in
/-- **There are 256 ^ 32 run values.** -/
theorem runValueCount : RunValueCount := by
  show Fintype.card (Fin 32 → Fin 256) = 256 ^ 32
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **Where the verifier's test on the public files says yes, the offline description is the one
that its seat makes.** -/
theorem offlineDescriptionNamed (files : PublicFiles) : OfflineDescriptionNamed files := by
  intro live
  obtain ⟨source, numbers, later, sourced⟩ := key_sourced files live
  obtain ⟨read, made, h0, hm, hs, hn, hl⟩ := sourced.source
  refine ⟨⟨source, numbers, later⟩, ?_, sourced⟩
  simp only [offlineDescription, h0, hm, hs, hn, hl, bind, Except.bind, pure, Except.pure]

variable {files : PublicFiles}

/-- **The online prover at the three returns.** -/
theorem onlineProver_eq {returned : OnlineReturn files} {places : H2U.Places4}
    {firstChain : Chain TS ProofFile.Cl} (made : onlineMaker files = .ok returned)
    (hp : H2U.placesOfMade returned.Z.made = .ok places)
    (hc : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain) :
    onlineProver files = onlineProverAt returned places firstChain := by
  simp only [onlineProver, made, hp, hc]

/-- **The offline prover at the description.** -/
theorem offlineProver_eq (parts : Parts files) {description : OfflineDescription}
    (h : offlineDescription files = .ok description) :
    offlineProver parts =
      offlineProverWithEncodedTable files (keyFileDescription description.source description.numbers description.later) parts.book
        (parts.prover description) runValueBytes runValueBytes (offlineStart description) := by
  simp only [offlineProver, h]

/-- **Where the table is the committer's, the committer's share leaves the maker's prover as it
is.** -/
theorem proverAt_return (returned : OnlineReturn files) (h : TableIsTheCommitters returned) :
    (cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 returned.H = returned.H :=
  ProofFile.Honest.Committer.proverAt_self h.1 h.2

/-- **The link's prover in the record is `linkProver`**, which is the library's `linkProverAtFiles` and so
`explicitLinkProver` at `committerCoinCountLessOne`, by their definitions. -/
theorem linkProver_is (files : PublicFiles) (parts : Parts files) :
    (honestProvers files parts).Lk = linkProver files := by
  unfold honestProvers proversOf
  rfl

/-- **`linkProver` is the library's link prover**, at the term. -/
theorem linkProver_eq_home (files : PublicFiles) :
    linkProver files = OnBytes.LinkSim.AtHome.explicitLinkProver FlashProve.committerCoinCountLessOne files := rfl

/-- **The plug into the socket**: where the table is the committer's and the rows' parts are the
prover's own, the socket's prover is the maker's. -/
theorem plug_return (returned : OnlineReturn files) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl)
    (rows : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      ProofFile.Honest.Cells Unit Unit) (table : TableIsTheCommitters returned)
    (sameProver : rows.prover returned.H = returned.H) :
    provG files returned.Z places firstChain returned.B rows returned.H = returned.H := by
  show rows.prover ((cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 returned.H) = returned.H
  rw [proverAt_return returned table, sameProver]

/-- **Rows whose parts are the prover's own give the family at the return.** -/
theorem onlineProverAt_rows (returned : OnlineReturn files) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl)
    (rows : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      ProofFile.Honest.Cells Unit Unit) (sameProver : rows.prover returned.H = returned.H) :
    famG files returned.Z places firstChain runValueBytes runValueBytes returned.B rows returned.H =
      onlineProverAt returned places firstChain := by
  rw [famG_eq, sameProver]
  rfl

end AtPublicFiles.AtFiles.HonestTerm

#print axioms ProofFile.Honest.Term.makerReturns
#print axioms ProofFile.Honest.Term.matrixInRange_iff
#print axioms ProofFile.Honest.Term.trace_return
#print axioms ProofFile.Honest.Term.key_return
#print axioms AtPublicFiles.AtFiles.HonestTerm.matrixReaderIsTheIndexReader
#print axioms AtPublicFiles.AtFiles.HonestTerm.runValueCount
#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineDescriptionNamed
#print axioms AtPublicFiles.AtFiles.HonestTerm.onlineProver_eq
#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineProver_eq
#print axioms AtPublicFiles.AtFiles.HonestTerm.proverAt_return
#print axioms AtPublicFiles.AtFiles.HonestTerm.linkProver_is
#print axioms AtPublicFiles.AtFiles.HonestTerm.linkProver_eq_home
#print axioms AtPublicFiles.AtFiles.HonestTerm.plug_return
#print axioms AtPublicFiles.AtFiles.HonestTerm.onlineProverAt_rows
