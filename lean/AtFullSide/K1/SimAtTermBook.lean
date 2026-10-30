-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/SimAtTermBook.lean: the shared "sending" (the kind K1): AT THE ONLINE HONEST PROVER's OWN
MAKER (onlineMaker, E2E/TheHonestProver.lean), AT ITS OWN BOOK: Good (fits, exact, fresh) at 51 of the
52 rows of lotS and wS, with no premise on the book left: at every row but the opening's. A join of
k1_sim_at_term (AtFullSide/K1/SimAtTerm.lean) and clear_but_opening (AtFullSide/K1/BookAtWClear.lean).
Two theorems; no definition.

  jobs_split            the 52 jobs are the opening's job and 51 more, none of which stands at the
                        opening's place
  k1_good_but_opening   Good at each of the 51, at .own, A.B, orderOf A.F, 0, 0

Limits. THE OPENING's ROW IS NOT HERE: its sender lends the most (a mask row's free entries; the
coefficients of the table that rides), and fresh at it waits for the premise on the book there. At the
fifty rows of the links' reads and digits fresh says little: nobody spends a coin of these senders. At
W's row it says that the 11 coefficients that the last chain's test spends are uniform and independent
of what W's sender shows and of what is known there. Good is had at predicates A₁, B₁ that never hold:
plays and acc are met for nothing. All limits of the files named. No property of the protocol is
claimed.
-/
import AtFullSide.K1.SimAtTerm
import AtFullSide.K1.BookAtWClear

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K1
open VerifiableInference.Desc
open ProofFile (Inst)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim
open ProofFile.Honest.Term (matrixInput tableCoins onlineFilling onlineMaker OnlineReturn makerReturns)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes.SendSim.At OnBytes.SendSim.Seat

/-- **The 52 jobs are the opening's and 51 more.** -/
theorem jobs_split (Z : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope Z = true) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    ∃ J₀ rest, k1Jobs OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G = J₀ :: rest ∧
      J₀.P.place = ⟨1, some 0, 1, .K1⟩ ∧ rest.length = 51 ∧
      ∀ J ∈ rest, J.P.place ≠ ⟨1, some 0, 1, .K1⟩ := by
  obtain ⟨h52, hnd⟩ := rows_52 hS matrixInput id (tableCoins Z) OnBytes.HonestTrace.Sz.ref openHonest hA
  rw [rows_eq] at h52 hnd
  rw [List.length_map] at h52
  rw [List.map_map] at hnd
  refine ⟨_, _, (rfl : k1Jobs OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G =
    placeJob (X := Unit) (K1.firstPar A.G.first (K1.gpOf A.Z))
      (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩) (firstFold A.G.first)
      (lotData OnBytes.HonestTrace.Sz.ref A.Z A.G) ::
    ((lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData OnBytes.HonestTrace.Sz.ref) A.Z
        A.G).tail ++
      wJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (K13.wDataAt openHonest.pile) A.Z A.G)), rfl,
    ?_, ?_⟩
  · exact Nat.succ.inj h52
  · intro J hJ e
    have hn : ((⟨1, some 0, 1, .K1⟩ : Place) ::
      ((lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData OnBytes.HonestTrace.Sz.ref) A.Z
          A.G).tail ++
        wJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (K13.wDataAt openHonest.pile) A.Z A.G).map
        (·.P.place)).Nodup := hnd
    exact (List.nodup_cons.1 hn).1 (e ▸ List.mem_map.2 ⟨J, hJ, rfl⟩)

/-- **GOOD AT 51 OF THE 52 ROWS, AT THE ONLINE PROVER's OWN MAKER AND BOOK; NO PREMISE ON THE BOOK IS
LEFT THERE.** -/
theorem k1_good_but_opening {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)} (Z : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope Z = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A)
    (T : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells → Thread A.B A.F.S₁ A.F.Cl
      (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) Unit Inst)
    (Sd : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells → Nat → Coins A.B →
      Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) Unit → Prop) (fs : List (Fall A.F.S₁)) :
    ∀ J ∈ k1Jobs OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G,
      J.P.place ≠ ⟨1, some 0, 1, .K1⟩ →
      ∀ r : Unlettered (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) Unit Inst,
      r = jobRow (witAt matrixInput id (tableCoins Z) A.Z) J →
      ∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre₀ .own σ A.B (orderOf A.F) 0 0 A₁ B₁ (r.lay T Sd A.F.first.blocksInOrder).On
          (r.lay T Sd A.F.first.blocksInOrder).bud :=
  fun J hJ hne r hr =>
    (((k1_sim_at_term (pre₀ := pre₀) Z hS hL).2 A hA).2.2 T Sd fs J hJ r hr).2.2.1
      (clear_but_opening hS hL _ _ hA _ J hJ hne)

end AtFullSide.K1

#print axioms AtFullSide.K1.jobs_split
#print axioms AtFullSide.K1.k1_good_but_opening
