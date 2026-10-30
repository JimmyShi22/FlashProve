-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/ReadsDebt2.lean

One theorem; no definition. Under the head, the opening (the terms:
Johnson/HonestTrace/U3Fit/SeatsAtHead.lean and Johnson/HonestTrace/U3Fit/SortedAtHead.lean) and
"okStart ξ = true", "ReadsLight Zp Bs.G₀ ξ" (Johnson/Desc/ProofFile/Honest/K2/Law/LightDebts.lean)
follows from three premises: "LookFits" (Johnson/HonestTrace/U3Fit/ValsGeneral.lean) at segment 24,
"LookFits" at the twelve layers' segments, and that "attVals" (Johnson/HonestTrace/U3Rows.lean)
returns at the twelve groups. Public data alone. A SegVals is carried whole; its field vec, a
function that awaits the trace's cells, is applied nowhere here.

Main theorem: "readsLight_debt". It calls "readsLight_of_start"
(Johnson/HonestTrace/U3Fit/ReadsDebt.lean), "returns_of_makers"
(Johnson/HonestTrace/U3Fit/ValsSorts.lean) and "layersVals_at_head"
(Johnson/HonestTrace/U3Fit/LayersAtHead.lean).

Limits. Head and opening are premises: the full size and the format's second hash function alone. All three
further premises stand unshown in this file; Johnson/HonestTrace/U3Fit/ReadsDebt3.lean discharges
the first two. No closed fact and no raised option of its own; files that it imports have them.
Not claimed: "ReadsLight" without these premises; that some instance passes "okStart". No property
of a release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.ReadsDebt
import Johnson.HonestTrace.U3Fit.LayersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile.Honest.K2.Law (ReadsLight)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open Johnson.AtFull.Desc (spotsWritten)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)}

/-- **"ReadsLight" from three premises**: the lookup's two clauses at segment 24 and at the twelve
layers' segments, and that "attVals" returns at the twelve groups. -/
theorem readsLight_debt (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true)
    (hH : LookFits Zp spotsWritten 24 .K6 Bs.G₀.W.HLy.fs)
    (hLy : ∀ g < 12, LookFits Zp spotsWritten (2 * g) .K4 Bs.G₀.W.layers.y.fo)
    (hA : ∀ g < 12, ∃ V, attVals Zp Bs.G₀ spotsWritten (2 * g + 1) g = .ok V) :
    ReadsLight Zp Bs.G₀ ξ :=
  readsLight_of_start h O hx hH (returns_of_makers h O.blank
    (fun g hg => by
      obtain ⟨V, hV, -⟩ := layersVals_at_head h O.blank hg (hLy g hg)
      exact ⟨V, hV⟩) hA)

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement and its axioms: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.readsLight_debt
#print axioms OnBytes.HonestTrace.U3.Fit.readsLight_debt
