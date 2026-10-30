-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLPublicFilling.lean

It states no goal. No property of the protocol is claimed.

hok and hpub of
`acceptedS_stands_L` (the middle conjunct, hS, is what `shapeFits_head_L` pays inside it)
at what `onlineProverFromPublicFiles` returns, at any filling whose rows are `widerRows Sz.ref`: at
the ground and the rows of that return, which are the letters that the lot lays
(`AtFullSide.K12.L_found`: D, lay, segs at A.G).

  `rows_at_filling`, `rows_read_through`  the filling `onlineProverPartsInUse`, and that filling read
                                    through, have the rows `widerRows S`
  `ground_of_return`, `rows_of_return`  the return's ground is the blank ground; its rows are
                                    those of that law
  `closing_premises_at_return`       hok, hS, and the public test at every instance that passes
                                    `okStart`, at the finish, at the return's rows
  `public_at_every_place`            the public test at every place of the code switch, at the
                                    return's rows

By what. `atPure_ok` (Honest/AtPureLaw.lean), `atPure_at_laid` (Honest/AtHead.lean),
`closing_premises_at_finish` (LotLPublicClosing.lean), `publicOk_of_okStart`
(Johnson/HonestTrace/Joint/ReadsLightPaid.lean).

Hypotheses. h: the head. hA: `onlineProverFromPublicFiles` returns. hrows: the filling's rows are at `Sz.ref`. The
term's filling is at `Sz.ref`, read through (`onlineFilling`; not beneath this file). hc: the statement of
`closing_at_head`.

Limits.
- That the side found at the test's place is `proverSideOfProximityTest (jobL …)` is not shown here: `L_found` has it
  before the filling is read through. On whether the side plays: nothing.
- Public tests alone. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLPublicClosing
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA F0T TS)

variable {W₀ W₀' Rc Rc' Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {pl : K2.SwitchPlace}

/-- The rows of the filling at the sizes S. -/
theorem rows_at_filling (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : Sz) (O : OnlineProverArguments) :
    (onlineProverPartsInUse I o S O).rows = widerRows S := rfl

/-- Reading a filling through keeps its rows. -/
theorem rows_read_through (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d : W₀') (I : WiderIn W₀)
    (o : ProofFile.SecondHashFunctionArgument) (S : Sz) (O : OnlineProverArguments) :
    (OnlineProverParts.through g rd d (onlineProverPartsInUse I o S O)).rows = widerRows S := rfl

section Return
variable {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- The return's ground is the blank ground. -/
theorem ground_of_return (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
  have eZ := (atPure_at_laid h.laid hA).1
  have k := (atPure_ok hA).2.1
  rwa [eZ] at k

/-- The return's rows, at the return's ground. -/
theorem rows_of_return (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hrows : P.rows = widerRows Sz.ref) :
    A.rows = K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp A.G := by
  have eZ := (atPure_at_laid h.laid hA).1
  have k := (atPure_ok hA).2.2.2.2.2.2.2.2.2.2.2
  rw [k, hrows, eZ]
  rfl

/-- **At the return's own ground and rows: hok, hS and the public test.** -/
theorem closing_premises_at_return (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hrows : P.rows = widerRows Sz.ref)
    (hf : finishAt Zp A.G = some pl) (hc : ClosingAtEveryPlace Z Zp Np cF) :
    K2.closingOk K2.freshTable ((K2.segmentsOf Zp A.G).take pl.link) pl = true ∧
      K2.ShapeFits pl.sizes.codes (shapeL pl) none ∧
      ∀ ξ : ProofFile.Inst, (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true →
        K2.publicOk A.rows A.G.first.layout pl
          ((K2.segmentsOf Zp A.G).take pl.link) ξ = true := by
  rw [rows_of_return h hA hrows]
  exact closing_premises_at_finish h (ground_of_return h hA) hf hc

/-- **The public test at every place of the code switch**, at the return's rows. -/
theorem public_at_every_place (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hrows : P.rows = widerRows Sz.ref)
    {ξ : ProofFile.Inst} (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    ∀ p ∈ K2.switchPlaces Zp A.G,
      K2.publicOk A.rows A.G.first.layout p ((K2.segmentsOf Zp A.G).take p.link) ξ = true := by
  rw [rows_of_return h hA hrows]
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : Bs.G₀ = A.G := Option.some.inj (O.blank.symm.trans (ground_of_return h hA))
  rw [← e]
  exact OnBytes.HonestTrace.U3.Fit.publicOk_of_okStart h O hx

end Return

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.rows_at_filling
#print axioms ProofFile.Honest.K12.AtProof.rows_read_through
#print axioms ProofFile.Honest.K12.AtProof.ground_of_return
#print axioms ProofFile.Honest.K12.AtProof.rows_of_return
#print axioms ProofFile.Honest.K12.AtProof.closing_premises_at_return
#print axioms ProofFile.Honest.K12.AtProof.public_at_every_place
