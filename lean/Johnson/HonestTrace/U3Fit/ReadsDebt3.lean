-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/ReadsDebt3.lean

One theorem; no definition. Under the head, the opening (the terms:
Johnson/HonestTrace/U3Fit/SeatsAtHead.lean and Johnson/HonestTrace/U3Fit/SortedAtHead.lean) and
"okStart ξ = true", "ReadsLight Zp Bs.G₀ ξ" (Johnson/Desc/ProofFile/Honest/K2/Law/LightDebts.lean)
follows from one premise: that "attVals Zp Bs.G₀ spotsWritten (2 * g + 1) g"
(Johnson/HonestTrace/U3Rows.lean) returns at each g below 12. Public data alone. A SegVals is
carried whole; its field vec, a function that awaits the trace's cells, is applied nowhere here.

Main theorem: "readsLight_of_att". It calls "readsLight_debt"
(Johnson/HonestTrace/U3Fit/ReadsDebt2.lean) and "lookFits_head", "lookFits_layers"
(Johnson/HonestTrace/U3Fit/LookFits.lean).

Limits. Head and opening are premises: the full size and the format's second hash function alone. That
"attVals" returns is a premise: no file of this folder shows it. No closed fact and no raised option
of its own; files that it imports have them.
Not claimed: "ReadsLight" without that premise; that some instance passes "okStart". No property of
a release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.ReadsDebt2
import Johnson.HonestTrace.U3Fit.LookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Ground)
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

/-- **"ReadsLight" from one premise: that "attVals" returns at the twelve groups.** -/
theorem readsLight_of_att (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true)
    (hA : ∀ g < 12, ∃ V, attVals Zp Bs.G₀ spotsWritten (2 * g + 1) g = .ok V) :
    ReadsLight Zp Bs.G₀ ξ :=
  readsLight_debt h O hx (lookFits_head h O.blank) (fun _ hg => lookFits_layers h O.blank hg) hA

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement and its axioms: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.readsLight_of_att
#print axioms OnBytes.HonestTrace.U3.Fit.readsLight_of_att
