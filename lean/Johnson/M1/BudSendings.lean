-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/BudSendings.lean: what the shared chain's two sendings ("send o_u", "send o_omega") owe to `BudDebts`, at their rows
as they are laid: `sendingRows` (Honest/K14/ExactRows.lean) has the count `budAt` for its bud, and `bud₂_u`, `bud₂_omega`
(Honest/K14/BudRows.lean) are the field's body at such a row.

  `sendings_budOwed₂`   at each of the two rows laid at the description's shared list: `BudOwed₂`

Limits. Under InScope, protocolDataWellFormed and LaidAt, at the proof file's description. A run of one request: nothing on the union of the
positions that the requests of a batch read. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.M1.BudShareCore
import Johnson.Desc.ProofFile.Honest.K14.BudRows
import Johnson.Desc.ProofFile.Honest.K14.ExactRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K14 VerifiableInference.Desc
open P5J (TS F0T)
open FlashProve (protocolDataWellFormed theProofData theProofRun)
open VerifierAndGoals (InScope asDescriptionFiles)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **Each of the two sendings' rows, laid, owes nothing more to `BudDebts`.** -/
theorem sendings_budOwed₂ (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (theProofData (asDescriptionFiles Z))
      (theProofRun (asDescriptionFiles Z)) Zp Np cF) (a : Nat) {X Pb W₀ Rc Ky : Type} {Bk : ProverCoinCounts}
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (T : Common W₀ Rc Ky → Thread Bk (F0T OnBytes.secondHashFunction Zp Np cF).S₂ (F0T OnBytes.secondHashFunction Zp Np cF).Cl
      Empty (Common W₀ Rc Ky) X Pb)
    (Sd : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X → Prop) :
    ∀ q ∈ (sendingRows ⟨qAt Zp Np, a⟩ weights rand : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)),
      BudOwed₂ (F0T OnBytes.secondHashFunction Zp Np cF) (q.lay T Sd (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) := by
  intro q hq
  simp only [sendingRows, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact bud₂_u scope live L a _ _ _ rfl rfl fun _ _ _ h => h
  · exact bud₂_omega scope live L a _ _ _ rfl rfl fun _ _ _ h => h

end Johnson.M1

#print axioms Johnson.M1.sendings_budOwed₂
