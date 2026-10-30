-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/ReadsDebt.lean

One theorem; no definition. Under the head, the opening (the terms:
Johnson/HonestTrace/U3Fit/SeatsAtHead.lean and Johnson/HonestTrace/U3Fit/SortedAtHead.lean) and
"okStart ξ = true", "ReadsLight Zp Bs.G₀ ξ" (Johnson/Desc/ProofFile/Honest/K2/Law/LightDebts.lean)
follows from two premises: "LookFits Zp spotsWritten 24 .K6 Bs.G₀.W.HLy.fs"
(Johnson/HonestTrace/U3Fit/ValsGeneral.lean), and that "valsAt" returns at the 24 segments below 24,
at every cov. Public data alone. A SegVals is carried whole; its field vec, a function that awaits
the trace's cells, is applied nowhere here.

Main theorem: "readsLight_of_start". It calls "readsLight_of_vals"
(Johnson/HonestTrace/U3Fit/ReadsLight.lean), "valsAt_head_returns"
(Johnson/HonestTrace/U3Fit/ReturnsAtHead.lean) and "covOf_sized_of_okStart"
(Johnson/Desc/ProofFile/Honest/K2/Law/CovOfAtStart.lean).

Limits. Head and opening are premises: the full size and the format's second hash function alone. Both
further premises stand unshown in this file. Elsewhere in this folder the first is a theorem under
the head, "lookFits_head" (Johnson/HonestTrace/U3Fit/LookFits.lean), and so is the second at the
twelve layers' segments, "layers_return_at_head" (Johnson/HonestTrace/U3Fit/ReturnsAtHead.lean); at
attention's twelve no file of this folder shows it. Johnson/HonestTrace/U3Fit/ReadsDebt3.lean is the
form with that one premise left. The layers' and attention's makers do not read the covered
positions: so the second is asked at every cov. No closed fact and no raised option of its own;
files that it imports have them.
Not claimed: "ReadsLight" without these premises; that some instance passes "okStart". No property
of a release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.ReadsLight
import Johnson.HonestTrace.U3Fit.ReturnsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.CovOfAtStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Pub Ground)
open ProofFile.Honest.K2.Law (ReadsLight covOf_sized_of_okStart)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open Johnson.AtFull.Desc (spotsWritten)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)}

/-- **"ReadsLight" from two premises**: the lookup's two clauses at segment 24, and that "valsAt"
returns at the 24 segments below it, at every cov. -/
theorem readsLight_of_start (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true)
    (hL : LookFits Zp spotsWritten 24 .K6 Bs.G₀.W.HLy.fs)
    (hv : ∀ cov, ∀ l < 24, ∃ V, valsAt Zp Bs.G₀ cov l = .ok V) : ReadsLight Zp Bs.G₀ ξ := by
  refine readsLight_of_vals h O ξ fun l hl => ?_
  by_cases e : l = 24
  · subst e
    exact valsAt_head_returns h O.blank (covOf_sized_of_okStart h O hx) hL
  · exact hv _ l (by omega)

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement and its axioms: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.readsLight_of_start
#print axioms OnBytes.HonestTrace.U3.Fit.readsLight_of_start
