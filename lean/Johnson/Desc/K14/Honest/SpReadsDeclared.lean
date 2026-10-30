--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/SpReadsDeclared.lean: the count of Johnson/Desc/K14/Honest/SpReads.lean AT
THE DECLARED ROUNDS OF THE PROOF FILE's IOP AS WRITTEN IN LEAN (below: the description): for all
public files Z that pass the library's two tests InScope and protocolDataWellFormed, and every public part Zp of
which the library's LaidAt holds at the proof file's own data and decision at Z.

  **sp_reads_declared**   add up, over the description's declared rounds, each round's declared
                  number of sampled positions, once for each time that the round lists the tree
                  whose number over the file is t₁ + 2 (the third tree that the shared chain sends),
                  the shared chain's rounds once and the other two chains' as many times as Zp's
                  sizes say slots: the sum IS the field r of the mask code that Zp's sizes list
                  under the shape's sharedMaskCode
  sp_first_whole  the general file's count leaves out the first chain's LAST declared round. Taken
                  whole, the first chain's declared rounds add nothing at that number (the general
                  file's readsOn_first_whole, called)
  sp_code_declared   that code is (2 ^ 13, 64, 152)
  spRow_declared  the test on the plan (SpRow.lean) accepts at Zp's own sizes
  opens_first_data, opens_first_decl, treeNo_of_shared   three equations that hold by definition, on
                  the general files' definitions; they would belong in these files

All is called: the count, its tie to the declared rounds and the equations of data and sizes with
the written ones are E2E/TreeReads.lean's, E2E/TreeReadsDeclared.lean's and
E2E/TreeReadsAtFiles.lean's; the entry at that number is SpReads.lean's.

What is assumed. InScope Z and protocolDataWellFormed (asDescriptionFiles Z). THAT protocolDataWellFormed ACCEPTS AT ANY Z IS NOT PROVED IN
THIS FILE: if it held nowhere, the theorems of this file that take it would say nothing.
What is not claimed. Which message lies in that tree. Nothing of distinct positions, of a run, of a
prover or of a coin. That a run of the description's sub-protocols asks for no position beyond the
declared rounds' sampled ones. The key file's description is not treated. All that the heads of the
files called do not claim. Nothing on soundness or on hiding.

-/
import E2E.TreeReadsDeclared
import Johnson.Desc.K14.Honest.SpReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open VerifiableInference VerifiableInference.PlanWritten VerifiableInference.Number.ByRuns
open VerifiableInference.Desc (Chain)
open Johnson.G Johnson.G.MadeFree Lk6.AtPlan
open OnBytes OnBytes.Params OnBytes.Maker
open AtPublicFiles.TreeReads
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofData theProofRun)
open P5J

/-- The number of trees that the first chain sends, in what a file's data open. -/
theorem opens_first_data (D : WholeD) : (opensOf D).t₁ = D.t₁ := rfl

/-- The like in what a description's declared rounds open. -/
theorem opens_first_decl {Xi : Type} (F : VerifiableInference.Desc.FileDescription Xi) :
    (declOpens F).t₁ = F.t₁ := rfl

/-- The number over the file of the n-th tree of the shared chain. -/
theorem treeNo_of_shared {Xi : Type} (F : VerifiableInference.Desc.FileDescription Xi) (n : ℕ) :
    treeNo F 1 n = F.t₁ + n := rfl

/-- **At the description's declared rounds.** -/
theorem sp_reads_declared (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (theProofData (asDescriptionFiles Z))
      (theProofRun (asDescriptionFiles Z)) Zp Np cF) :
    (declOpens (F0T OnBytes.secondHashFunction Zp Np cF)).inBatch Zp.p.chains.made.sized.lines.slots
        (treeNo (F0T OnBytes.secondHashFunction Zp Np cF) 1 2) =
      (spCode Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch.shape).r := by
  have e : opensOf writtenPFull = declOpens (F0T OnBytes.secondHashFunction Zp Np cF) := by
    rw [← proof_data Z scope live, opensOf_at, FlashProve.dp_built_live Z live,
      opens_of_data L.data]
  have ht : (F0T OnBytes.secondHashFunction Zp Np cF).t₁ = 83 := by
    rw [← opens_first_decl, ← e, opens_first_data, writtenPFull_eq]
    exact t_proof.1
  have hn : treeNo (F0T OnBytes.secondHashFunction Zp Np cF) 1 2 = 85 := by
    rw [treeNo_of_shared, ht]
  rw [← e, hn, sized_at scope L, written_slots, written_proof]
  exact sp_reads_proof

/-- **The first chain's declared rounds, taken whole**, the last among them, add nothing at that
number. -/
theorem sp_first_whole (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (theProofData (asDescriptionFiles Z))
      (theProofRun (asDescriptionFiles Z)) Zp Np cF) :
    readsOn (declPairs (F0T OnBytes.secondHashFunction Zp Np cF).t₁ (F0T OnBytes.secondHashFunction Zp Np cF).t₂ 0
      (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.1) (treeNo (F0T OnBytes.secondHashFunction Zp Np cF) 1 2) = 0 := by
  have e : opensOf writtenPFull = declOpens (F0T OnBytes.secondHashFunction Zp Np cF) := by
    rw [← proof_data Z scope live, opensOf_at, FlashProve.dp_built_live Z live,
      opens_of_data L.data]
  have ht : (F0T OnBytes.secondHashFunction Zp Np cF).t₁ = 83 := by
    rw [← opens_first_decl, ← e, opens_first_data, writtenPFull_eq]
    exact t_proof.1
  rw [readsOn_first_whole L.data, ← e, treeNo_of_shared, ht]
  exact sp_each_proof.2.1

/-- The test on the plan accepts at that public part's own sizes. -/
theorem spRow_declared (Z : PublicFiles) (scope : InScope Z = true)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ((withU Zp.p.chains.made.sized.proof.batch.shape).any
        (spRowB Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch.shape) &&
      spTailB Zp.p.chains.made.sized.proof.batch Zp.p.chains.made.sized.proof.codes) = true := by
  rw [sized_at scope L, written_proof]
  exact spRow_written

/-- The code there. -/
theorem sp_code_declared (Z : PublicFiles) (scope : InScope Z = true)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ((spCode Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch.shape).logN,
      (spCode Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch.shape).ell,
      (spCode Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch.shape).r) =
      (13, 64, 152) := by
  rw [sized_at scope L, written_proof]
  exact sp_numbers.1

end Desc.K14.Honest

#print axioms Desc.K14.Honest.opens_first_data
#print axioms Desc.K14.Honest.opens_first_decl
#print axioms Desc.K14.Honest.treeNo_of_shared
#print axioms Desc.K14.Honest.sp_reads_declared
#print axioms Desc.K14.Honest.sp_first_whole
#print axioms Desc.K14.Honest.spRow_declared
#print axioms Desc.K14.Honest.sp_code_declared
