-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/SimAtTerm.lean: the shared "sending" (the kind K1): its two lots with their simulators
(lotS, wS: Johnson/Desc/ProofFile/Honest/K1/Sim/AtFill.lean) AT THE FILLING OF THE ONLINE HONEST
PROVER (onlineFilling, E2E/TheHonestProver.lean), at what its maker onlineMaker returns, at the face,
the order, the chain's numbers and THE BOOK that Owed names (Honest/Owed.lean): .own, orderOf A.F, 0,
0, A.B. Three theorems.

  k1_sim_at_term    in scope, where the gate accepts: the maker returns some A; at EVERY A that it
                    returns there are 52 rows at 52 places, and job by job: fits and exact, free of
                    any book; and the four premises that the rule asks of a row, of which Good stands
                    under the premise on A.B at that job's own sender
  k1_lots_at_term   without the simulators the two values are the first and the last lot of
                    onlineFilling
  files_pass        the stored full-size public files pass both tests: the premises of
                    k1_sim_at_term are met

Limits. All limits of AtFill.lean. The premise on the book at a job's sender stands. In the side
library, because it imports files of it. No property of the protocol is claimed.
-/
import AtFullSide.Honest.HonestProverLaws
import AtFullSide.Top.LiveAtFull
import Johnson.Desc.ProofFile.Honest.K1.Sim.AtFill

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

/-- **K1's SIMULATORS AT THE ONLINE PROVER's FILLING.** -/
theorem k1_sim_at_term {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)} (Z : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope Z = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    (∃ A, onlineMaker Z = .ok A) ∧
    ∀ A, onlineMaker Z = .ok A →
      (rowsOfLots A.Z A.G [lotS matrixInput id (tableCoins Z) OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref,
        wS matrixInput id (tableCoins Z) OnBytes.secondHashFunction openHonest]).length = 52 ∧
      ((rowsOfLots A.Z A.G [lotS matrixInput id (tableCoins Z) OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref,
        wS matrixInput id (tableCoins Z) OnBytes.secondHashFunction openHonest]).map (·.place)).Nodup ∧
      ∀ (T : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells → Thread A.B A.F.S₁ A.F.Cl
          (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) Unit Inst)
        (Sd : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells → Nat → Coins A.B →
          Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) Unit → Prop) (fs : List (Fall A.F.S₁)),
      ∀ J ∈ k1Jobs OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G,
      ∀ r : Unlettered (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Inst Cells) Unit Inst,
      r = jobRow (witAt matrixInput id (tableCoins Z) A.Z) J →
      A.F.first.blocksInOrder.any (fun b => b.place == r.place) = true ∧
      (∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
        σ.fits = true ∧ ExactAt .own σ 0 0 r.On r.bud) ∧
      (SpendersClearAny J.P J.ride A.B (orderOf A.F) ⟨J.P.place, 0⟩ →
        ∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
          ∃ A₁ B₁, Good pre₀ .own σ A.B (orderOf A.F) 0 0 A₁ B₁ (r.lay T Sd A.F.first.blocksInOrder).On
            (r.lay T Sd A.F.first.blocksInOrder).bud) ∧
      (∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
        A.F.first.blocksInOrder = pre ++ σ.block :: t →
        n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
        ∀ ρ : ProofFile.Honest.Draws, ρ.due A.F = true →
        (r.lay T Sd A.F.first.blocksInOrder).bud u.number ((ρ.first.drop n).take u.rounds.length)
          (asksFrom (treeAsks A.F ρ 0) (u.rounds.map (·.2.length))
            (((rowsOfChain A.F.first.blocksInOrder).take n).map (·.2.length)).sum)) ∧
      ∀ w b len, OnFromS (T w) (Sd w) (r.lay T Sd A.F.first.blocksInOrder) b len := by
  refine ⟨makerReturns Z hS hL, fun A hA => ?_⟩
  obtain ⟨h52, hnd⟩ := rows_52 hS matrixInput id (tableCoins Z) OnBytes.HonestTrace.Sz.ref openHonest hA
  exact ⟨h52, hnd, fun T Sd fs =>
    handIn_at_return hS hL matrixInput id (tableCoins Z) OnBytes.HonestTrace.Sz.ref openHonest hA .own
      A.B (orderOf A.F) 0 0 T Sd fs⟩

/-- **Without the simulators the two values are the first and the last lot of the filling.** -/
theorem k1_lots_at_term (Z : VerifierAndGoals.PublicFiles) :
    (onlineFilling Z).lots =
      (lotS matrixInput id (tableCoins Z) OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref).toHLot ::
        (((widerFillAt matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots.tail ++
            [closeLotAt matrixInput OnBytes.HonestTrace.Sz.ref,
              proxLotAt matrixInput OnBytes.HonestTrace.Sz.ref]).map
          (HLot.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z))) ++
          [(wS matrixInput id (tableCoins Z) OnBytes.secondHashFunction openHonest).toHLot]) :=
  lots_split matrixInput id (tableCoins Z) matrixInput.dummy OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- **Some public files pass both tests.** -/
theorem files_pass : ∃ Z : VerifierAndGoals.PublicFiles,
    VerifierAndGoals.InScope Z = true ∧ FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true :=
  ⟨VerifierAndGoals.storedPublicFiles, VerifierAndGoals.inScope_full, AtFullSide.Top.theLive_zFull⟩

end AtFullSide.K1

#print axioms AtFullSide.K1.k1_sim_at_term
#print axioms AtFullSide.K1.k1_lots_at_term
#print axioms AtFullSide.K1.files_pass
