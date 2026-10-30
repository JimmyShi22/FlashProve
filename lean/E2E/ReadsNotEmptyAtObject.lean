-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ReadsNotEmptyAtObject.lean: E2E/ReadsNotEmpty.lean at the object of E2E/ReadsAtWritten.lean
and at the object at public files on all matrices (E2E/ReadsAtFiles.lean): the key file's verifier,
and the verifier of each request of a batch, read at least one column of the committed table at
every verifier randomness. Statements and proofs.

What is shown.
  `test_reads_some`, `bat_reads_some`: for the three protocols of the full size at ANY rounds' data
    DK, DP (`threeProtocolsAtFullSize`) and all provers: if the second chain of DK (of DP) passes the test
    `Opens`, the set of positions that the object's protocol `offline` (the protocol of one request of
    `onlineBatch`) declares as read is not empty, at every input and every verifier randomness.
  **`reads_some_atWritten`**: so at the object of `reads_atWritten`: DK and DP the written data
    themselves. No premise is left, and no public file occurs.
  **`reads_some_filesAt`**: so at the object at public files Z, in scope with the gate open.

Limits.
- AT PUBLIC FILES it takes scope AND the gate open, and that the gate is open is proved in the side
  library: at the library's two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and
  at the first set's files under every policy within four bounds (`theLive_zAt`,
  AtFullSide/Top/LiveAtPolicies.lean). Where the gate is shut these two verifiers read no column
  (`reads_filesAt_shut`, E2E/ReadsAtFiles.lean).
- A lower bound of one column, of the positions that a protocol DECLARES as read. On the verifier of
  a copy's file nothing is shown here (E2E/StringsHoldLink.lean). The second half speaks of ONE
  request's verifier: so of a batch with at least one request. The object cut to the matrices in
  range is not named here (its verifier's side is the same: `v_objAt`, E2E/ObjectGuards.lean).
- All limits of E2E/ReadsCount.lean and E2E/ReadsNotEmpty.lean stand. Nothing on hiding.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import E2E.ReadsNotEmpty
import E2E.ReadsAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Reads
open Iop Prob Hiop
open OnBytes.Flat (Files relationsAndEncodingOfClaims Coding RecFull claimsLedgerOnAt codingCells)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize numsRef)
open Johnson.G (writtenKFull writtenPFull)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open LPFD.Full (XF)
open AtPublicFiles.AtFiles (filesAt)

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → View → View → View → Bool)
  (runP : X × RecFull → View → View → View → Bool) (ds : List TypedOracleCompiler.Run.PQ.RD)
  (xs : List XO) (dec : RecFull × RecFull → View → Bool) (rK rP : RecFull)
  (depthReq : ℕ) (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- The key file's verifier, at any rounds' data whose second chain passes the test. -/
theorem test_reads_some (h : Opens (DK.at frS.P.T.a).ds₂ = true) :
    ∀ x ρ, (((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers
      P).offline.extReads x ρ).Nonempty :=
  fun _ ρ => whole_reads_some .two (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
    (OnBytes.Flat.join₀ rK) ByteArray.empty OnBytes.Flat.silK runK h ρ

/-- The verifier of one request of a batch, the same. -/
theorem bat_reads_some (h : Opens (DP.at frS.P.T.a).ds₂ = true) :
    ∀ x ρ, (((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers
      P).onlineBatch.loc.extReads x ρ).Nonempty :=
  fun _ ρ => whole_reads_some .two (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
    (OnBytes.Flat.join₀ rP) ByteArray.empty OnBytes.Flat.silP runP h ρ

end

/-- The written data pass the test. -/
theorem opens_atWritten : Opens writtenKFull.ds₂ = true ∧ Opens writtenPFull.ds₂ = true := by
  rw [Johnson.G.writtenKFull_eq, Johnson.G.writtenPFull_eq]
  exact opens_written

/-- **At the object of `reads_atWritten`**: both verifiers read a column, at every input and every
verifier randomness, for all three decisions and all provers. -/
theorem reads_some_atWritten (X : Type) (pp : Inst.Model.ScalesAndPolicy)
    (req : X → Inst.Model.Instance Inst.Model.ppref) (runK : RecFull → View → View → View → Bool)
    (runP : X × RecFull → View → View → View → Bool) (dec : RecFull × RecFull → View → Bool)
    (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
    (P : (threeProtocolsAtFullSize (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)) writtenKFull writtenPFull runK runP
      PV.EntryFive.dsF PV.EntryFive.xsF dec rK rP depthReq early salt).Provers) :
    (∀ x ρ, (((threeProtocolsAtFullSize (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)) writtenKFull writtenPFull runK runP
      PV.EntryFive.dsF PV.EntryFive.xsF dec rK rP depthReq early salt).withProvers
        P).offline.extReads x ρ).Nonempty) ∧
    ∀ x ρ, (((threeProtocolsAtFullSize (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)) writtenKFull writtenPFull runK runP
      PV.EntryFive.dsF PV.EntryFive.xsF dec rK rP depthReq early salt).withProvers
        P).onlineBatch.loc.extReads x ρ).Nonempty :=
  ⟨test_reads_some _ _ writtenKFull writtenPFull runK runP _ _ dec rK rP depthReq early salt P
      (by rw [VerifiableInference.OnPublicFiles.writtenKFull_at]; exact opens_atWritten.1),
    bat_reads_some _ _ writtenKFull writtenPFull runK runP _ _ dec rK rP depthReq early salt P
      (by rw [VerifiableInference.OnPublicFiles.writtenPFull_at]; exact opens_atWritten.2)⟩

/-- **At the object at public files Z**, in scope with the gate open, for all provers. -/
theorem reads_some_filesAt (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (P : (filesAt Z).Provers) :
    (∀ x ρ, (((filesAt Z).withProvers P).offline.extReads x ρ).Nonempty) ∧
      ∀ x ρ, (((filesAt Z).withProvers P).onlineBatch.loc.extReads x ρ).Nonempty :=
  ⟨test_reads_some _ _ (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK
      (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec
      (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
      (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
      (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) P
      (by rw [key_data Z scope live]; exact opens_atWritten.1),
    bat_reads_some _ _ (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK
      (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec
      (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
      (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
      (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) P
      (by rw [proof_data Z scope live]; exact opens_atWritten.2)⟩

end AtPublicFiles.Reads

#print axioms AtPublicFiles.Reads.test_reads_some
#print axioms AtPublicFiles.Reads.bat_reads_some
#print axioms AtPublicFiles.Reads.opens_atWritten
#print axioms AtPublicFiles.Reads.reads_some_atWritten
#print axioms AtPublicFiles.Reads.reads_some_filesAt
