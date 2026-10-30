-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ReadsAtWritten.lean: the library's property `HolographicProtocol.ReadsR` (Hiop/RecInterface.lean) for the three
files' protocols of the full size: first at any rounds' data, from sums over these data; then the
sums at the written data of the key file and of the proof file, and at the written openings of the
copy's file. Statements and proofs.

`ReadsR b qT qpar qch qon` has five clauses. Four are counts of columns of a committed table that a
verifier reads, at every verifier randomness: the key file's verifier at most qT; the verifier of a
copy's file at most qpar of the first table and qch of the copy; one batch of requests, all its
requests together, at most qon. The fifth (`hidE`) is on the committer's side alone
(E2E/TableHides.lean).

What is shown.
  **`reads_fullD`**: for the three protocols `threeProtocolsAtFullSize` (Johnson/Flat/Dec/WiresAtSizes.lean) at
    ANY claims, honest side, rounds' data DK, DP, ds, openings xs, three decisions and provers:
    `ReadsR` from: the key file's three sums add up to at most qT; the proof file's first and third
    chain have the sum 0 and its second at most qon; the own trees' numbers of the copy's file are
    below 2^16; the openings' counts by table are at most qpar and qch; the configuration has
    `Hides b`. The number of proof-of-work bits of a round occurs in no premise.
  `storedSum_rdt`: data that differ in fields other than `stored` have the same sums: stated for
    any map of rounds' data that keeps `stored`.
  `stored1_keyFull`, `stored2_keyFull`, `stored3_keyFull`: the key file's written data have the sums
    0, 62, 0: by an evaluation in Lean's kernel over the written lists (18,850 + 68 + 30 rounds).
  `key_sums`, `proof_sums`: the sums at `writtenKFull` and `writtenPFull`: 0, 62, 0 and 0, 64, 0;
    the second from the library's own evaluations (Johnson/Flat/Dec/FitAtWritten.lean).
  `link_own`, `link_counts`: at the written rounds' data and openings of the copy's file: the own
    trees' numbers are below 2^16 (the library's test), and the counts are 62 and 62.
  **`reads_written`**: so at every DK, DP whose data at the tables' depth are the written ones, at
    the written ds and xs, and at the full size's written honest side:
    `ReadsR 44040191 62 62 62 64`.
  `reads_atWritten`: a member of that form: DK and DP the written data themselves. No premise is
    left, and no public file occurs.

Limits.
- The four counts are of the positions that a protocol declares as read (E2E/ReadsCount.lean's first
  limit). That two of the sets are not empty at the object of `reads_atWritten` is in
  E2E/ReadsNotEmptyAtObject.lean.
- The four counts are upper bounds for ONE run: one run of the key file's verifier, one of a copy's
  file's, one batch. How often a table is read in all is no matter of this file: whoever uses the
  property has to add up, table by table, against the 44,040,191.
- `reads_written` takes "the data are the written ones" as two premises. That they hold of the IOP
  as written in Lean, at public files in scope at which its gate is open, is in
  E2E/ReadsAtFiles.lean.
- The numbers are those of the written lists. That a program's verifier reads so many columns is
  not said: no file of a program is compared here.
- The provers are not read by any clause: the statement holds for provers that send nothing. It is
  no statement on what a prover's messages show.
- All limits of E2E/ReadsCount.lean and E2E/TableHides.lean stand.

`Spec.reads_written` says what is to be proved at the written data: it may be read as a goal. It
is not among this library's goals.

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
import E2E.ReadsCount
import E2E.TableHides
import Johnson.Flat.Dec.WiresAtSizes
import Johnson.Flat.Dec.FitAtWritten
import Johnson.Flat.Dec.DeadAtWritten
import Johnson.Flat.Dec.DataAtWritten
import Johnson.Top.Fire.Code.Vals.EntryFive

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Reads
open Iop Prob Hiop
open OnBytes.Flat (Files relationsAndEncodingOfClaims Coding RecFull claimsLedgerOnAt codingCells)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (View XO cntOf)
open OnBytes.Maker (WholeD RDT)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize numsRef)
open Johnson.G (sumE sum_eq_sumE dKeyFull dProofFull writtenKFull writtenPFull)

/-! ## 1. At any rounds' data -/

/-- **`ReadsR` for the three protocols of the full size, from sums over the rounds' data.** -/
theorem reads_fullD {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
    (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
    (runK : RecFull → View → View → View → Bool)
    (runP : X × RecFull → View → View → View → Bool) (ds : List TypedOracleCompiler.Run.PQ.RD)
    (xs : List XO) (dec : RecFull × RecFull → View → Bool) (rK rP : RecFull)
    (depthReq : ℕ) (early : X → X) (salt : ℕ)
    (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
    {b qT qpar qch qon : ℕ}
    (hK : storedSum (DK.at frS.P.T.a).ds₁ +
      (storedSum (DK.at frS.P.T.a).ds₂ + storedSum (DK.at frS.P.T.a).ds₃) ≤ qT)
    (hP₁ : storedSum (DP.at frS.P.T.a).ds₁ = 0) (hP₂ : storedSum (DP.at frS.P.T.a).ds₂ ≤ qon)
    (hP₃ : storedSum (DP.at frS.P.T.a).ds₃ = 0)
    (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (hp : cntOf false xs ≤ qpar) (hc : cntOf true xs ≤ qch)
    (hH : (OnBytes.Slice.DecR.configurationOfStoredTable A R).Hides b) :
    ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).ReadsR
      b qT qpar qch qon where
  cntT := fun _ ρ => le_trans (whole_card (DK.at frS.P.T.a) (ckP .two) (OnBytes.Flat.front₀ rK)
    (OnBytes.Flat.join₀ rK) ByteArray.empty OnBytes.Flat.silK runK ρ) hK
  cntLp := fun x ρ => le_trans (linkW_left (ckP .two) ds frS.P.T.a xs dec hown x ρ) hp
  cntLc := fun x ρ => le_trans (linkW_right (ckP .two) ds frS.P.T.a xs dec hown x ρ) hc
  cntB := whole_readsAtMost (DP.at frS.P.T.a) (ckP .two) (OnBytes.Flat.front₀ rP)
    (OnBytes.Flat.join₀ rP) ByteArray.empty OnBytes.Flat.silP runP hP₁ hP₃ hP₂ _
  hidE := AtPublicFiles.Table.obj_hidE _ P hH

/-- A map of rounds' data that keeps the stored entries keeps the sum. -/
theorem storedSum_rdt (f : RDT → RDT) (hf : ∀ d, (f d).stored = d.stored) :
    ∀ ds : List RDT, storedSum (ds.map f) = storedSum ds
  | [] => rfl
  | d :: ds => by
      show ((f d).stored.map (·.count)).sum + storedSum (ds.map f) =
        (d.stored.map (·.count)).sum + storedSum ds
      rw [hf d, storedSum_rdt f hf ds]

/-! ## 2. The sums at the written data -/

/-- The sum, in the form that Lean's kernel evaluates. -/
theorem storedSum_eq (ds : List RDT) :
    storedSum ds = sumE 0 (ds.map fun d => (d.stored.map (·.count)).sum) :=
  sum_eq_sumE _

set_option maxRecDepth 1000000 in
theorem stored1_keyFull :
    sumE 0 (dKeyFull.ds₁.map fun d => (d.stored.map (·.count)).sum) = 0 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem stored2_keyFull :
    sumE 0 (dKeyFull.ds₂.map fun d => (d.stored.map (·.count)).sum) = 62 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem stored3_keyFull :
    sumE 0 (dKeyFull.ds₃.map fun d => (d.stored.map (·.count)).sum) = 0 := by decide +kernel

/-- **The key file's written data**: the second chain alone opens the table, at 62 sampled
positions. -/
theorem key_sums : storedSum writtenKFull.ds₁ = 0 ∧ storedSum writtenKFull.ds₂ = 62 ∧
    storedSum writtenKFull.ds₃ = 0 := by
  rw [Johnson.G.writtenKFull_eq]
  exact ⟨(storedSum_eq _).trans stored1_keyFull, (storedSum_eq _).trans stored2_keyFull,
    (storedSum_eq _).trans stored3_keyFull⟩

/-- **The proof file's written data**: the second chain alone, which a batch shares, opens the
table, at 64 sampled positions. -/
theorem proof_sums : storedSum writtenPFull.ds₁ = 0 ∧ storedSum writtenPFull.ds₂ = 64 ∧
    storedSum writtenPFull.ds₃ = 0 := by
  rw [Johnson.G.writtenPFull_eq]
  exact ⟨(storedSum_eq _).trans Johnson.G.stored1_proofFull,
    (storedSum_eq _).trans Johnson.G.stored2_proofFull,
    (storedSum_eq _).trans Johnson.G.stored3_proofFull⟩

/-- The own trees of the copy's file have numbers below 2^16: the library's test. -/
theorem link_own : ∀ d ∈ PV.EntryFive.dsF, ∀ n ∈ d.opens, n < 2 ^ 16 :=
  (OnBytes.Flat.entryFit_of_test VerifiableInference.OnPublicFiles.entryFitB_dsFull_140).own

/-- **The written openings of the copy's file**: 62 sampled positions for the first table, 62 for
the copy. -/
theorem link_counts : cntOf false PV.EntryFive.xsF = 62 ∧ cntOf true PV.EntryFive.xsF = 62 := by
  show cntOf false OnBytes.Slice.frD.xs = 62 ∧ cntOf true OnBytes.Slice.frD.xs = 62
  rw [OnBytes.Slice.fr_xs]
  exact ⟨rfl, rfl⟩

/-! ## 3. Together -/

/-- The statement of `reads_written`. -/
def Spec.reads_written : Prop :=
  ∀ (X : Type) (pp : Inst.Model.ScalesAndPolicy) (req : X → Inst.Model.Instance Inst.Model.ppref)
    (DK DP : WholeD) (runK : RecFull → View → View → View → Bool)
    (runP : X × RecFull → View → View → View → Bool) (dec : RecFull × RecFull → View → Bool)
    (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
    (P : (threeProtocolsAtFullSize (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)) DK DP runK runP PV.EntryFive.dsF
      PV.EntryFive.xsF dec rK rP depthReq early salt).Provers),
    DK.at frS.P.T.a = writtenKFull → DP.at frS.P.T.a = writtenPFull →
      ((threeProtocolsAtFullSize (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
        (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)) DK DP runK runP PV.EntryFive.dsF
        PV.EntryFive.xsF dec rK rP depthReq early salt).withProvers P).ReadsR 44040191 62 62 62 64

/-- **At the written data**: the key file's verifier reads at most 62 columns, the verifier of a
copy's file at most 62 of the first table and 62 of the copy, one batch at most 64; and at every OOD
seed the law of (OOD answers, any 44,040,191 columns) is the same for all matrices. For all three
decisions and all provers. -/
theorem reads_written : Spec.reads_written :=
  fun X pp req DK DP runK runP dec rK rP depthReq early salt P eK eP =>
    reads_fullD _ _ DK DP runK runP PV.EntryFive.dsF PV.EntryFive.xsF dec rK rP depthReq early salt
      P (by have h := key_sums; rw [eK]; omega)
      (by rw [eP]; exact proof_sums.1) (by rw [eP]; exact proof_sums.2.1.le)
      (by rw [eP]; exact proof_sums.2.2) link_own link_counts.1.le link_counts.2.le
      (AtPublicFiles.Table.hides_full X pp req 44040191 (Nat.le_refl _))

/-- **A member**: at the written data themselves, taken as the two files' data, no premise is left.
For every table of scales and policy, all three decisions and all provers. -/
theorem reads_atWritten (X : Type) (pp : Inst.Model.ScalesAndPolicy)
    (req : X → Inst.Model.Instance Inst.Model.ppref) (runK : RecFull → View → View → View → Bool)
    (runP : X × RecFull → View → View → View → Bool) (dec : RecFull × RecFull → View → Bool)
    (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
    (P : (threeProtocolsAtFullSize (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)) writtenKFull writtenPFull runK runP
      PV.EntryFive.dsF PV.EntryFive.xsF dec rK rP depthReq early salt).Provers) :
    ((threeProtocolsAtFullSize (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)) writtenKFull writtenPFull runK runP
      PV.EntryFive.dsF PV.EntryFive.xsF dec rK rP depthReq early salt).withProvers P).ReadsR
        44040191 62 62 62 64 :=
  reads_written X pp req writtenKFull writtenPFull runK runP dec rK rP depthReq early salt P
    VerifiableInference.OnPublicFiles.writtenKFull_at VerifiableInference.OnPublicFiles.writtenPFull_at

end AtPublicFiles.Reads

#print axioms AtPublicFiles.Reads.reads_fullD
#print axioms AtPublicFiles.Reads.storedSum_rdt
#print axioms AtPublicFiles.Reads.stored1_keyFull
#print axioms AtPublicFiles.Reads.stored2_keyFull
#print axioms AtPublicFiles.Reads.stored3_keyFull
#print axioms AtPublicFiles.Reads.key_sums
#print axioms AtPublicFiles.Reads.proof_sums
#print axioms AtPublicFiles.Reads.link_own
#print axioms AtPublicFiles.Reads.link_counts
#print axioms AtPublicFiles.Reads.reads_written
#print axioms AtPublicFiles.Reads.reads_atWritten
