-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the first chain's last test as a value of the frame's lot with simulators.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/SlotValueL.lean: a value of SLot (Thread/Rows.lean) whose lot is
proxLotAt (AtPureWiderK12.lean), the list that the filling lays at the test: the same parts, each
with its simulator, the condition OnEntry and the bound budBoth.

  jobOfLot             the job that proxLotAt lays, at a finish
  rowOfJob             the row of a job: its two parts with their simulators
  rowsOfLot, simulatorLot   the rows, the value
  simulatorLot_toHLot  **its lot is proxLotAt**

Definitions and one equation. Nothing here says that the value meets Good: SlotL.lean says that at
a seated side. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.SlotL
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open H2K.Member (codesFull)
open VerifiableInference.Desc (Block)

variable {W₀ X : Type}

/-- **The job that proxLotAt lays**, at the finish pl. -/
def jobOfLot (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground)
    (pl : K2.SwitchPlace) : TestJob (Local W₀ IndexCommitterCoins Inst Cells) X :=
  jobL (H2U.p12OfMade Z.made) (doorAtL Z) (widerRows S Z G)
    (fun w => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
    (K2.lotClosingAt G.first.layout (K2.segmentsOf Z G)) pl

/-- The simulators' job at the public part. -/
def simulatorJobOfLot (Z : Pub) : SimJob Inst :=
  simulatorJobAtFirstChainTest Z (H2U.p12OfMade Z.made)
    (osL.map fun x => ((srcOf 0 x.2).1, (srcOf 0 x.2).2, x.1.a))

/-- **The row of a job**: its two parts with their simulators, at its place. -/
def rowOfJob (Z : Pub) (J : TestJob (Local W₀ IndexCommitterCoins Inst Cells) X) :
    Unlettered (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst :=
  ⟨J.p.place, testPairs J (simulatorJobOfLot Z),
    OnEntry Face.own J (simulatorJobOfLot Z) codesFull 0 osL, budBoth (simulatorJobOfLot Z)⟩

/-- **The rows**, under proxLotAt's own guards. -/
def rowsOfLot (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) :
    List (Unlettered (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst) :=
  match ProofFile.onlineFirstChainAt Z with
  | .ok cF =>
    if cF.blocksInOrder.any (·.place == placeL) && (H2U.p12OfMade Z.made).place == placeL then
      ((finishAt Z G).bind fun p =>
        if fitsL (H2U.p12OfMade Z.made) p then some (jobOfLot I S Z G p) else none).toList.map
        (rowOfJob Z)
    else []
  | .error _ => []

/-- **The value.** -/
def simulatorLot (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    SLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst :=
  ⟨(proxLotAt (X := X) I S).name, rowsOfLot I S⟩

/-- **Its lot is the one that the filling lays.** -/
theorem simulatorLot_toHLot (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    (simulatorLot (X := X) I S).toHLot = proxLotAt I S := by
  unfold SLot.toHLot simulatorLot proxLotAt
  refine congrArg (HLot.mk _) (funext fun Z => funext fun G => ?_)
  dsimp only
  unfold rowsOfLot
  cases hc : ProofFile.onlineFirstChainAt Z with
  | error e => rfl
  | ok cF =>
    dsimp only
    by_cases hg : (cF.blocksInOrder.any (·.place == placeL) &&
        (H2U.p12OfMade Z.made).place == placeL) = true
    · rw [if_pos hg, if_pos hg]
      show _ = (proxLotOf I S).halves Z G
      unfold proxLotOf lotAtDoor lotL lotOf
      dsimp only
      cases hf : finishAt Z G with
      | none => rfl
      | some p =>
        simp only [Option.bind_some]
        split
        · rfl
        · rfl
    · rw [if_neg hg, if_neg hg]
      rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.simulatorLot
#print axioms ProofFile.Honest.K12.Sim2.simulatorLot_toHLot
