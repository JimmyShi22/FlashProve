-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptRows.lean: the closing of a segment (K10): THE CODE SWITCH's ROWS ARE LAID: at each place of the code switch,
at the data, the readers and the closing of the first chain's script of the base prover (`firstScriptAt`,
AtFullSide/K1/FirstScript.lean), the switch's own text of its rows (`switchRowsLaid`) returns: at all coins, at all challenges, and
at every input whose public instance passes the description's test on the instance. This is the premise hV of `tab_of_switch`
and `fresh_of_switch` (Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieSwitch.lean, XchFreshSwitch.lean).

  `Closes A`             ONE NAMED PREMISE: the public test on the closing (`closingOk`) says yes at each place of the code switch. The
                         library pays it under the hypothesis (`closing_at_head`, Honest/K2/Law/ClosingAtHead.lean: 25 closed facts by
                         Lean's kernel, which want much memory): AtFullSide/K10/ScriptRowsPaid.lean calls it
  `four_at_base`         under the hypothesis: the other four public tests say yes at each place
  **`rows_laid_of`**       THE STATEMENT, from `Closes A`

By: `rows_isSome` (Johnson/Desc/ProofFile/Honest/K2/Law/LotsAnswer.lean): whether the text returns is four public tests, under a fifth
on the closing; `serves_at_head`, `roomy_at_head`, `fits_at_head`
(Honest/K2/Law/PublicAtHead.lean); `publicOk_of_okStart` (Johnson/HonestTrace/Joint/ReadsLightPaid.lean).

Limits. AT THE SIZES `Sz.ref` ALONE: the public test on the data is shown at these. On whether the text returns: nothing on what
it returns. The hypothesis and the maker's return are premises. Closed facts by Lean's kernel lie beneath, in the files called.
The full size and the older hash alone. No property is claimed.
-/
import AtFullSide.K1.FirstScript
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswer
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead
import Johnson.HonestTrace.Joint.ReadsLightPaid
import Johnson.Desc.ProofFile.Honest.AtHeadGround

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
open ProofFile.Honest.K2 (SwitchPlace switchPlaces switchRowsLaid lotClosingAt segmentsOf publicOk placeFits
  closingOk freshTable)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The named premise**: the public test on the closing says yes at each place of the code switch. -/
def Closes (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) : Prop :=
  ∀ p ∈ switchPlaces A.Z A.G, closingOk freshTable ((segmentsOf A.Z A.G).take p.link) p = true

/-- The other four public tests, at each place of the code switch. -/
theorem four_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) {ξ : ProofFile.Inst}
    (hx : (P5J.F0T OnBytes.secondHashFunction A.Z Np cF).okStart ξ = true) :
    p.sizes.serves = true ∧ p.sizes.roomy = true ∧
      publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout p ((segmentsOf A.Z A.G).take p.link) ξ = true ∧
      placeFits p = true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rw [eG] at hp ⊢
  exact ⟨K2.Law.serves_at_head h.toAtMg O p hp,
    K2.Law.roomy_at_head h.toAtMg O p hp, OnBytes.HonestTrace.U3.Fit.publicOk_of_okStart h O hx p hp,
    K2.Law.fits_at_head h.toAtMg O p hp⟩

/-- **THE SWITCH's ROWS ARE LAID**, at all coins and challenges, at every input whose public instance passes the description's
test on the instance. -/
theorem rows_laid_of (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (hC : Closes A) {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (w : LocB W₀)
    (hx : (P5J.F0T OnBytes.secondHashFunction A.Z Np cF).okStart w.x = true) (hd : List Fmt.Drawn) :
    ∃ V, switchRowsLaid (widerRows Sz.ref A.Z A.G) (readersB I A.Z)
      (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) p c w hd = .ok V := by
  have t0 := hC p hp
  obtain ⟨t1, t2, t3, t4⟩ := four_at_base h hA hp hx
  have e := K2.Law.rows_isSome (widerRows Sz.ref A.Z A.G) (readersB I A.Z) A.G.first.layout (segmentsOf A.Z A.G) p t0
    c w hd
  rw [t1, t2, t3, t4] at e
  cases hV : switchRowsLaid (widerRows Sz.ref A.Z A.G) (readersB I A.Z)
      (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) p c w hd with
  | ok V => exact ⟨V, rfl⟩
  | error m =>
    rw [hV] at e
    cases e

end AtFullSide.K10

#print axioms AtFullSide.K10.four_at_base
#print axioms AtFullSide.K10.rows_laid_of
