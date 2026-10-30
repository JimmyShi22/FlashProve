-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/Sim/AtFilling.lean: THE SIX ROWS' HALVES ARE WHAT THE FRAME's MAKER OF THE SHARED CHAIN's HALVES
RETURNS: under the library's head, at every reader of the index, `nowSharedBy` (Honest/AtPureWiderAt.lean) returns the halves of
`simRows` at the frame's own reader of the index committer's coins. So the rows of Honest/K14/Sim/Rows.lean are the rows of the
parts that that maker lays, not a second text of them.

  `simRows_now`    **the equation**
  `simLot`, `simLot_at_head`   **K14's simulators as a value of `SLot`** (Honest/Thread/Rows.lean): the rows of the public part, where
                  the maker lays halves; under the head they are `simRows`

Limits. A maker's list, not a filling's field: that a filling's shared field is this list is that filling's text. No property of the
protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sim.Good
import Johnson.Desc.ProofFile.Honest.K14.AtWiderShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12.Seat (tests last)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument} {W₀ Pb : Type}

/-- **`nowSharedBy` returns the six rows' halves.** -/
theorem simRows_now (h : P5J.AtMgA o Z D r₀ Zp Np cF x₀) (weights : W₀ → Weights) :
    nowSharedBy weights Zp =
      .ok ((simRows (simData Zp Np) (simPub Zp Np) weights (randNow (qAt Zp Np)) :
        List (Unlettered Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit Pb)).map (·.half)) := by
  rw [simRows_half]
  exact nowSharedBy_at_head h weights

/-- **K14's six rows as a value of `SLot`**: read off the public part by the filling's own two readers, with the two round numbers
made by `dataOf`; no row where the frame's maker lays no half. The ground is not read. -/
def simLot (weights : W₀ → Weights) : SLot Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit Pb :=
  { name := "K14"
    rows := fun Zp _ =>
      match p14At Zp, onlineSharedChain Zp with
      | some P, some s =>
        match (sixOf P s.chain.blocksInOrder weights (randNow P) :
            Except String (List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit))),
          dataOf P.S s.chain.blocksInOrder with
        | .ok _, some d => simRows d ⟨P, d.atPoint⟩ weights (randNow P)
        | _, _ => []
      | _, _ => [] }

/-- **Under the head the lot's rows are `simRows`.** -/
theorem simLot_at_head (h : P5J.AtMgA o Z D r₀ Zp Np cF x₀) (weights : W₀ → Weights) (G : Ground) :
    (simLot (Pb := Pb) weights).rows Zp G =
      simRows (simData Zp Np) (simPub Zp Np) weights (randNow (qAt Zp Np)) := by
  obtain ⟨a, b, -⟩ := filling_at_head h
  obtain ⟨sentU, layO, hP⟩ := plan2_at_head h
  obtain ⟨B⟩ := hP.eight
  have F := flatOf_plain Zp.p.chains (qAt Zp Np) B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8
    (tests Np) last B.made
  have hd := dataOf_flat F B.made (qAt Zp Np).S
  have hs := six_at_head (Ky := OnBytes.TableKey) (X := Unit) h weights
  show (match p14At Zp, onlineSharedChain Zp with
      | some P, some s =>
        match (sixOf P s.chain.blocksInOrder weights (randNow P) :
            Except String (List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit))),
          dataOf P.S s.chain.blocksInOrder with
        | .ok _, some d => simRows d ⟨P, d.atPoint⟩ weights (randNow P)
        | _, _ => []
      | _, _ => []) = _
  rw [a, b]
  simp only []
  have hd' : dataOf (qAt Zp Np).S (Desc.K14.Law.seatN Zp Np).chain.blocksInOrder =
      some { S := (qAt Zp Np).S, atPoint := 0, atZeta := 6 } := hd
  rw [hs, hd']
  rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.simLot_at_head
#print axioms ProofFile.Honest.K14.simRows_now
