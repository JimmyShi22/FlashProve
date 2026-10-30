-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BudBoth.lean: kind K14: AT THE PROOF FILE's IOP AS WRITTEN IN LEAN
(below: the description), IN A RUN OF ONE REQUEST, THE POSITIONS THAT THE FRAME LAYS FOR THE TREES
OF BOTH SENDINGS OF THE SHARED CHAIN MEET budAt (Johnson/SendSim/At/Sim.lean): at every message, for
its main rows' code and for its mask rows' code. For all public files Z that pass the library's two
tests InScope and protocolDataWellFormed, and every public part Zp of which the library's LaidAt holds at the proof
file's own data and decision at Z. Counts on public numbers. Statements with their proofs; no
definition.

  budAt_of_test   general in the description: where countsWithinB (Honest/K14/BudTest.lean) accepts
                  at the library's count in a batch of one request: budAt at the positions that the
                  frame lays (budAt_of_counts, Honest/K14/BudSends.lean)
  readsWithinAtB_eq   readsWithinAtB (Johnson/SendSim/Seat/ReadsTestAt.lean) is countsWithinB at the
                  count by sources: by definition
  sendings_trees, three_counts, four_rows, tests_bite   **the test is not idle at the written sizes,
                  and it can fail there**: each sending has two messages, each in a tree (o_u and
                  the first mask in one; o_omega and o_sp in two); the counts at the three trees'
                  numbers in a batch of one request are 101, 106, 152; the four rows' r are 101,
                  152, 3,571, 152: so o_u's main rows and o_sp's mask row are filled; at a count
                  greater by one the test rejects at both sendings
  declOpens_written   what the description's declared rounds open is what the library's written
                  rounds' data open. (In the library the equation stands inside proofs, under no
                  name: E2E/TreeReadsDeclared.lean, Johnson/Desc/K14/Honest/SpReadsDeclared.lean,
                  SpAllAt.lean)
  count_written   so the count is that of the library's short lists (same_proof, proofOpens:
                  E2E/TreeReadsAtWritten.lean)
  first_chain_83  the first chain sends 83 trees
  tests_at_files  **the test accepts at both sendings**: "send o_u" from the shared chain's tree
                  number 0, "send o_omega" from number 1 (two evaluations at the written sizes and
                  the short lists)
  budAt_u_at_files, budAt_omega_at_files   **budAt at both**, at every due list of challenges

What is assumed. InScope Z, protocolDataWellFormed (asDescriptionFiles Z), LaidAt.
What is not claimed. A RUN OF ONE REQUEST: at o_omega's tree the last chain reads 55 positions for
EACH request of a batch: nothing on the union over a batch. That the two sendings' first trees have
the numbers 0 and 1 as the frame counts the trees in front of a part: Honest/K14/BudRows.lean. The
key file's description is not treated. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BudTest
import Johnson.Desc.ProofFile.Honest.K14.BudAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (FileDescription Chain)
open OnBytes.SendSim.At (budAt)
open VerifierAndGoals (InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofData theProofRun)
open P5J (LaidAt F0T TS)
open AtPublicFiles.TreeReads (declOpens treeNo opensOf opensOf_at opens_of_data proof_data same_proof
  proofOpens sized_at written_proof)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.PlanWritten (proofSizedFull)

/-- **Where the test accepts at the library's count in a batch of one request: budAt.** -/
theorem budAt_of_test {Xi : Type} {F : FileDescription Xi} {file : String} {D : OnBytes.Maker.WholeD}
    (h : F.data file = .ok D) (ch : Nat) (P : VerifiableInference.Desc.K1.Par) (n₀ : Nat)
    (hB : countsWithinB ((declOpens F).inBatch 1) (treeNo F ch n₀) P.codes P.sent = true)
    (ρ : Draws) (hρ : ρ.due F = true) (rs : List Nat) :
    budAt P (asksFrom (treeAsks F ρ ch) rs n₀) := by
  refine budAt_of_counts h ch P n₀ (fun k τ hk hτ => ?_) ρ hρ rs
  have h1 := List.all_eq_true.1 hB k (List.mem_range.2 hk)
  rw [hτ] at h1
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
  have e : treeNo F ch (n₀ + τ) = treeNo F ch n₀ + τ := (Nat.add_assoc _ _ _).symm
  rw [e]
  exact ⟨fun hm => h1.1.resolve_left hm, fun hm => h1.2.resolve_left hm⟩

/-- readsWithinAtB is this test at the count by sources. -/
theorem readsWithinAtB_eq {Xi : Type} (F : FileDescription Xi) (ch : Nat)
    (P : VerifiableInference.Desc.K1.Par) (n₀ : Nat) :
    OnBytes.SendSim.Seat.readsWithinAtB F ch P n₀ =
      countsWithinB (OnBytes.SendSim.Seat.drawnForAt F ch) n₀ P.codes P.sent := rfl

/-! ## The test is not idle at the written sizes, and it can fail there -/

/-- At the written sizes each sending has two messages, and each message lies in a tree: o_u and the
first mask in the sending's tree number 0; o_omega in number 0 and o_sp in number 1. (Kin for the
second half: the library's tree_omega_at, Johnson/Desc/Book/LayOmega.lean.) -/
theorem sendings_trees :
    (((VerifiableInference.Desc.Own.treesMade proofSizedFull.codes
        ((Desc.K14.withU proofSizedFull.batch.shape).getD #[])).getD {}).tree.toList,
      ((VerifiableInference.Desc.Own.treesMade proofSizedFull.codes
        (Desc.K14.withOmega proofSizedFull.batch.shape)).getD {}).tree.toList) =
      ([0, 0], [0, 1]) := by decide +kernel

/-- The counts in a batch of one request at the three trees' numbers. -/
theorem three_counts : (proofOpens.inBatch 1 83, proofOpens.inBatch 1 84,
    proofOpens.inBatch 1 85) = (101, 106, 152) := by decide +kernel

/-- The four messages' rows and codes at the written sizes: for each message of each sending: its
main rows, its mask rows, the r of its main rows' code, the r of its mask rows' code (0 where it has
no such row). WITH three_counts: o_u's main rows: 101 of 101: FILLED · the first mask's row: 101 of
152 · o_omega's main rows: 106 of 3,571 · o_sp's mask row: 152 of 152: FILLED. (The library's own
list of the rows with more encoding randomness than reads, at 64 requests: proofSlack,
E2E/TreeReadsAtWritten.lean.) -/
theorem four_rows :
    ((((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).toList.map fun x =>
        (x.shape.mainRows, x.shape.maskRows,
          (proofSizedFull.codes.base.getD x.shape.code default).r,
          (proofSizedFull.codes.mask.getD x.shape.maskCode default).r)),
      ((Desc.K14.withOmega proofSizedFull.batch.shape).toList.map fun x =>
        (x.shape.mainRows, x.shape.maskRows,
          (proofSizedFull.codes.base.getD x.shape.code default).r,
          (proofSizedFull.codes.mask.getD x.shape.maskCode default).r))) =
      ([(107, 0, 101, 0), (0, 1, 0, 152)], [(12, 0, 3571, 0), (0, 1, 0, 152)]) := by
  decide +kernel

/-- **IT CAN FAIL**: at a count that is greater by one the test rejects at both sendings: at each a
row is filled (four_rows with three_counts). IT BITES AT ONE ROW A SENDING: of the two rows with
slack it tells nothing; and it cannot tell a wrong first tree: "send o_omega" from the number 83
would pass too. -/
theorem tests_bite :
    countsWithinB (fun j => proofOpens.inBatch 1 j + 1) 83 proofSizedFull.codes
        ((Desc.K14.withU proofSizedFull.batch.shape).getD #[]) = false ∧
      countsWithinB (fun j => proofOpens.inBatch 1 j + 1) 84 proofSizedFull.codes
        (Desc.K14.withOmega proofSizedFull.batch.shape) = false := by decide +kernel

variable (Z : VerifierAndGoals.PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (theProofData (asDescriptionFiles Z))
    (theProofRun (asDescriptionFiles Z)) Zp Np cF)

include scope live L in
/-- What the description's declared rounds open is what the written rounds' data open. -/
theorem declOpens_written :
    declOpens (F0T OnBytes.secondHashFunction Zp Np cF) = opensOf Johnson.G.writtenPFull := by
  rw [← proof_data Z scope live, opensOf_at, FlashProve.dp_built_live Z live,
    opens_of_data L.data]

include scope live L in
/-- So the count is that of the library's short lists. -/
theorem count_written (N : Nat) :
    (declOpens (F0T OnBytes.secondHashFunction Zp Np cF)).inBatch N = proofOpens.inBatch N :=
  funext fun j => by rw [declOpens_written Z scope live Zp Np cF L, same_proof.inBatch]

include scope live L in
/-- The first chain sends 83 trees. (Kin: the library's Desc.K14.Honest.first_trees,
Johnson/Desc/K14/Honest/SpAllAt.lean, says that the description and the data computed from Z count
the same trees of the first chain; the number is not in it. The number stands of the rounds' data in
t1_written, Johnson/HB/LLHARD/TreesWritten.lean, and AtMg.trees, HeadFacts.lean; and this very
sentence, under no name, inside the proof of sp_reads_declared.) -/
theorem first_chain_83 : (F0T OnBytes.secondHashFunction Zp Np cF).t₁ = 83 := by
  rw [← Desc.K14.Honest.opens_first_decl, declOpens_written Z scope live Zp Np cF L,
    Desc.K14.Honest.opens_first_data]
  exact same_proof.e₁

include scope live L in
/-- **The test accepts at both sendings.** -/
theorem tests_at_files (a : Nat) :
    countsWithinB ((declOpens (F0T OnBytes.secondHashFunction Zp Np cF)).inBatch 1)
        (treeNo (F0T OnBytes.secondHashFunction Zp Np cF) 1 0) (jobU ⟨qAt Zp Np, a⟩).Q.codes
        (jobU ⟨qAt Zp Np, a⟩).Q.sent = true ∧
      countsWithinB ((declOpens (F0T OnBytes.secondHashFunction Zp Np cF)).inBatch 1)
        (treeNo (F0T OnBytes.secondHashFunction Zp Np cF) 1 1) (jobOmega ⟨qAt Zp Np, a⟩).Q.codes
        (jobOmega ⟨qAt Zp Np, a⟩).Q.sent = true := by
  have eU : (jobU ⟨qAt Zp Np, a⟩).Q.sent = (Desc.K14.withU (qAt Zp Np).S).getD #[] :=
    Desc.K14.Law.parK1_sent (qAt Zp Np) 2 _ _
  have eO : (jobOmega ⟨qAt Zp Np, a⟩).Q.sent = Desc.K14.withOmega (qAt Zp Np).S :=
    Desc.K14.Law.parK1_sent (qAt Zp Np) 5 _ _
  have t0 : treeNo (F0T OnBytes.secondHashFunction Zp Np cF) 1 0 = 83 := by
    show (F0T OnBytes.secondHashFunction Zp Np cF).t₁ + 0 = 83
    rw [first_chain_83 Z scope live Zp Np cF L]
  have t1 : treeNo (F0T OnBytes.secondHashFunction Zp Np cF) 1 1 = 84 := by
    show (F0T OnBytes.secondHashFunction Zp Np cF).t₁ + 1 = 84
    rw [first_chain_83 Z scope live Zp Np cF L]
  rw [eU, eO, t0, t1, count_written Z scope live Zp Np cF L 1]
  show countsWithinB (proofOpens.inBatch 1) 83 Zp.p.chains.made.sized.proof.codes
      ((Desc.K14.withU Zp.p.chains.made.sized.proof.batch.shape).getD #[]) = true ∧
    countsWithinB (proofOpens.inBatch 1) 84 Zp.p.chains.made.sized.proof.codes
      (Desc.K14.withOmega Zp.p.chains.made.sized.proof.batch.shape) = true
  rw [sized_at scope L, written_proof]
  decide +kernel

include scope live L in
/-- **budAt at "send o_u"**, at the shared chain's trees from number 0 on: a run of one request. -/
theorem budAt_u_at_files (a : Nat) (ρ : Draws)
    (hρ : ρ.due (F0T OnBytes.secondHashFunction Zp Np cF) = true) (rs : List Nat) :
    budAt (jobU ⟨qAt Zp Np, a⟩).Q (asksFrom (treeAsks (F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) rs 0) :=
  budAt_of_test L.data 1 _ 0 (tests_at_files Z scope live Zp Np cF L a).1 ρ hρ rs

include scope live L in
/-- **budAt at "send o_omega"**, at the shared chain's trees from number 1 on: a run of one
request. -/
theorem budAt_omega_at_files (a : Nat) (ρ : Draws)
    (hρ : ρ.due (F0T OnBytes.secondHashFunction Zp Np cF) = true) (rs : List Nat) :
    budAt (jobOmega ⟨qAt Zp Np, a⟩).Q
      (asksFrom (treeAsks (F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) rs 1) :=
  budAt_of_test L.data 1 _ 1 (tests_at_files Z scope live Zp Np cF L a).2 ρ hρ rs

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.budAt_of_test
#print axioms ProofFile.Honest.K14.readsWithinAtB_eq
#print axioms ProofFile.Honest.K14.sendings_trees
#print axioms ProofFile.Honest.K14.three_counts
#print axioms ProofFile.Honest.K14.four_rows
#print axioms ProofFile.Honest.K14.tests_bite
#print axioms ProofFile.Honest.K14.declOpens_written
#print axioms ProofFile.Honest.K14.count_written
#print axioms ProofFile.Honest.K14.first_chain_83
#print axioms ProofFile.Honest.K14.tests_at_files
#print axioms ProofFile.Honest.K14.budAt_u_at_files
#print axioms ProofFile.Honest.K14.budAt_omega_at_files
