-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptRowsPaid.lean: the closing of a segment (K10): the one named premise of AtFullSide/K10/ScriptRows.lean, paid by
the library's law on the code switch's closing; so the code switch's rows are laid, with no premise but the hypothesis, the
maker's return and the test on the input's public instance.

  `closes_at_base`       `Closes A`, by `closing_at_head` (Johnson/Desc/ProofFile/Honest/K2/Law/ClosingAtHead.lean)
  **`rows_laid_first`**    the premise hV of `tab_of_switch` and `fresh_of_switch`

Limits. Those of AtFullSide/K10/ScriptRows.lean. 25 closed facts by Lean's kernel lie beneath. No property is claimed.
-/
import AtFullSide.K10.ScriptRows
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA TS)
open ProofFile.Honest
open ProofFile.Honest.K1 (readersB LocB)
open ProofFile.Honest.K2.Law (SwitchCoins)
open ProofFile.Honest.K2 (SwitchPlace switchPlaces switchRowsLaid lotClosingAt segmentsOf)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The named premise, paid. -/
theorem closes_at_base {S : Sz} (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) : Closes A := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  intro p hp
  rw [eG] at hp ⊢
  exact K2.Law.closing_at_head h.toAtMg O p hp

/-- **THE SWITCH's ROWS ARE LAID.** -/
theorem rows_laid_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (w : LocB W₀)
    (hx : (P5J.F0T OnBytes.secondHashFunction A.Z Np cF).okStart w.x = true) (hd : List Fmt.Drawn) :
    ∃ V, switchRowsLaid (widerRows Sz.ref A.Z A.G) (readersB I A.Z)
      (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) p c w hd = .ok V :=
  rows_laid_of h hA (closes_at_base h hA) hp c w hx hd

end AtFullSide.K10

#print axioms AtFullSide.K10.closes_at_base
#print axioms AtFullSide.K10.rows_laid_first
