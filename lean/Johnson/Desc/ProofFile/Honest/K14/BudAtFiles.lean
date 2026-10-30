-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BudAtFiles.lean: kind K14: AT THE PROOF FILE's IOP AS WRITTEN IN
LEAN (below: the description), IN A RUN OF ONE REQUEST, THE POSITIONS THAT THE FRAME LAYS FOR o_sp's
TREE MEET spBud (Honest/K14/FreshDefs.lean), the bound in fresh_at_omega
(Honest/K14/FreshField.lean): for all public files Z that pass the library's two tests InScope and
protocolDataWellFormed, and every public part Zp of which the library's LaidAt holds at the proof file's own data
and decision at Z. Counts on public numbers. Statements with their proofs; no definition.

  sp_count_one    the library's count at the shared chain's third tree, in a batch of ONE request,
                  is at most the r of the code spCode: sp_reads_declared
                  (Johnson/Desc/K14/Honest/SpReadsDeclared.lean), which has the count at as many
                  requests as the sizes say, and inBatch_mono (E2E/TreeReads.lean)
  sp_code_r       that r is the r of the mask code that o_sp's shape names at the shared chain's
                  own parameters qAt Zp Np (an evaluation at the written sizes)
  sp_tree_one     of the sending's trees o_sp's is number 1, from 0 (an evaluation)
  spBud_at_files  **spBud at the positions that the frame lays, at every due list of challenges,
                  for the trees of the shared chain from number 1 on**: whatever the rounds' numbers
                  of roots
  spBud_at_head   the same under the library's one hypothesis at the full size and protocolDataWellFormed

What is assumed. InScope Z, protocolDataWellFormed (asDescriptionFiles Z), LaidAt. At the goals' two named sets of public
files the first two are theorems of the library (AtFullSide/Bind/LiveAtNamed.lean).
What is not claimed. THAT "send o_omega"'s FIRST TREE HAS THE NUMBER 1 IN THE SHARED CHAIN, as the
frame counts the trees in front of a part: one_before_omega, Honest/K14/BudAtRow.lean. A RUN OF ONE
REQUEST: nothing on the union of the positions that the requests of a batch read. THE COUNT IS
FILLED: 152 of 152. The key file's description is not treated. Nothing on what is or is not hidden;
no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BudSends
import Johnson.Desc.ProofFile.Honest.K14.AskedAtShared
import Johnson.Desc.K14.Honest.SpReadsDeclared
import Johnson.P5J.AtName
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open VerifierAndGoals (InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofData theProofRun)
open P5J (LaidAt F0T TS)
open AtPublicFiles.TreeReads (declOpens treeNo inBatch_mono sized_at written_slots written_proof)
open Desc.K14.Honest (spCode sp_reads_declared)

variable (Z : VerifierAndGoals.PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (theProofData (asDescriptionFiles Z))
    (theProofRun (asDescriptionFiles Z)) Zp Np cF)

include scope live L in
/-- The library's count at the shared chain's third tree, in a batch of one request. -/
theorem sp_count_one :
    (declOpens (F0T OnBytes.secondHashFunction Zp Np cF)).inBatch 1
        (treeNo (F0T OnBytes.secondHashFunction Zp Np cF) 1 2) ≤
      (spCode Zp.p.chains.made.sized.proof.codes
        Zp.p.chains.made.sized.proof.batch.shape).r := by
  rw [← sp_reads_declared Z scope live Zp Np cF L]
  exact inBatch_mono _ (by rw [sized_at scope L, written_slots]; decide) _

include scope L in
/-- That r is the r of the mask code that o_sp's shape names. -/
theorem sp_code_r (a : Nat) : (spMaskCode ⟨qAt Zp Np, a⟩).r =
    (spCode Zp.p.chains.made.sized.proof.codes
      Zp.p.chains.made.sized.proof.batch.shape).r := by
  show (Zp.p.chains.made.sized.proof.codes.mask.getD
    Zp.p.chains.made.sized.proof.batch.shape.sharedSplit.maskCode default).r = _
  rw [sized_at scope L, written_proof]
  decide +kernel

include scope L in
/-- Of the sending's trees o_sp's is number 1. (Kin: the library's tree_omega_at,
Johnson/Desc/Book/LayOmega.lean, says the like, general in the shape, of another function that lays
trees: layTrees at linMessageOmega.) -/
theorem sp_tree_one (a : Nat) :
    ((VerifiableInference.Desc.Own.treesMade (jobOmega ⟨qAt Zp Np, a⟩).Q.codes
      (jobOmega ⟨qAt Zp Np, a⟩).Q.sent).getD {}).tree[1]? = some 1 := by
  have e : (jobOmega ⟨qAt Zp Np, a⟩).Q.sent = Desc.K14.withOmega (qAt Zp Np).S :=
    Desc.K14.Law.parK1_sent (qAt Zp Np) 5 _ _
  rw [e]
  show ((VerifiableInference.Desc.Own.treesMade Zp.p.chains.made.sized.proof.codes
    (Desc.K14.withOmega Zp.p.chains.made.sized.proof.batch.shape)).getD {}).tree[1]? = some 1
  rw [sized_at scope L, written_proof]
  decide +kernel

include scope live L in
/-- **spBud at the positions that the frame lays for the shared chain's trees from number 1 on**, at
every due list of challenges: a run of one request. -/
theorem spBud_at_files (a : Nat) (ρ : Draws) (hρ : ρ.due (F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (rs : List Nat) :
    spBud ⟨qAt Zp Np, a⟩ (asksFrom (treeAsks (F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) rs 1) :=
  spBud_of_count L.data ⟨qAt Zp Np, a⟩ 1 (fun t ht => by
    obtain rfl : 1 = t := Option.some.inj ((sp_tree_one Z scope Zp Np cF L a).symm.trans ht)
    rw [sp_code_r Z scope Zp Np cF L a]
    exact sp_count_one Z scope live Zp Np cF L) ρ hρ rs

omit scope L in
include live in
/-- **The same under the library's one hypothesis at the full size**, where the verifier's test on
the public files accepts. -/
theorem spBud_at_head {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z (VerifierAndGoals.AtTheName.dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF
      x₀) (a : Nat) (ρ : Draws) (hρ : ρ.due (F0T OnBytes.secondHashFunction Zp Np cF) = true) (rs : List Nat) :
    spBud ⟨qAt Zp Np, a⟩ (asksFrom (treeAsks (F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) rs 1) :=
  spBud_at_files Z h.scope live Zp Np cF (P5J.dpZ_live live ▸ h.laid) a ρ hρ rs

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sp_count_one
#print axioms ProofFile.Honest.K14.sp_code_r
#print axioms ProofFile.Honest.K14.sp_tree_one
#print axioms ProofFile.Honest.K14.spBud_at_files
#print axioms ProofFile.Honest.K14.spBud_at_head
