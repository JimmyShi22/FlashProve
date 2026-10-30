-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/RowsAtShared.lean: kind K14: WHAT THE FRAME's RULE FOR ROWS ASKS
OF THE TWO SENDINGS' ROWS (RowsServe, Honest/K14/SendingRowsStated.lean), AT THE FIELD shared, FLAT,
OF THE PROOF FILE's IOP AS WRITTEN IN LEAN, under the library's head (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean). One statement with its proof: two calls. No definition.

Why. sendingRowsAtHead (Honest/K14/SendingRowsLaw.lean) has RowsServe at the shared rounds' own flat
list carried to any type of claims. Of the frame's two debts beside the field exact (bud₂ and on₂,
Honest/Law/OwedRule.lean) the BODIES at these rows are shown at the description's own list: bud₂'s
at every due list of one request's challenges (Honest/K14/BudRows.lean); on₂'s as an implication
from the letters of a frame's sentence (Honest/K14/OnRows.lean). Neither debt is thereby paid. The
two lists are one: shared_flat_at (Honest/K14/OmegaAtShared.lean), by unfolding, at the library's
earlier hash and the description's own type of claims.

  rowsServe_at_shared   **RowsServe at that field**

What is not claimed. All that Honest/K14/SendingRowsStated.lean's head says is not claimed, but for
its sentence on that one equation. That any book passes the two owners' tests. That a filling lays
these rows. One request. The full size alone. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingRowsLaw
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place Chain)
open Desc.K14 (St)

/-- **RowsServe at the description's own field shared, flat**, under the library's head. -/
theorem rowsServe_at_shared {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (X W₀ Rc Ky : Type) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (fs : List (Fall St)) (Bk : ProverCoinCounts) (ord : List Place) :
    RowsServe (X := X) (Ky := Ky) (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder ⟨qAt Zp Np, 0⟩
      weights rand fs Bk ord := by
  rw [shared_flat_at]
  exact sendingRowsAtHead h ProofFile.Cl X W₀ Rc Ky weights rand fs Bk ord

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.rowsServe_at_shared
