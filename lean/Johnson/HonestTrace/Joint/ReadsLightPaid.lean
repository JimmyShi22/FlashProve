-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/ReadsLightPaid.lean

Nothing on hiding. Theorems; no definition. Public data alone.
FOR K8 AND K2: "ReadsLight Zp Bs.G₀ ξ" (Johnson/Desc/ProofFile/Honest/K2/Law/LightDebts.lean) at
every ξ with "okStart ξ = true", with no premise left but the head and the opening, under which both callers stand.

How. "readsLight_of_att" (Johnson/HonestTrace/U3Fit/ReadsDebt3.lean) had one premise left: that "attVals" returns at the
twelve groups. The library has that: "att_returns_at_open" (Johnson/Desc/ProofFile/Honest/K5/Law/AttValsAtHead.lean).
So each theorem here is a call or two.

* "readsLight_of_okStart": under the head and the opening.
* "readsLight_of_okStart_at_ground": under the head alone, at whatever ground "blankBy" returns at Zp.
* "publicOk_of_okStart": so K2's public test says yes at every place of the kind ("publicOk_of_reads",
  Johnson/Desc/ProofFile/Honest/K2/Law/PublicOkOfReads.lean), with no named statement left.

Limits. The head (and the opening) are premises: the full size and the hash "OnBytes.secondHashFunction" alone.
Closed facts by Lean's
kernel lie beneath, in the files called. The light test goes one way. Nothing on what the data hold.
Not claimed: that some instance passes "okStart". No property of a release, of a verifier or of a prover.
-/
import Johnson.HonestTrace.U3Fit.ReadsDebt3
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicOkOfReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Ground)
open ProofFile.Honest.K2 (switchPlaces segmentsOf publicOk withSwitchData)
open ProofFile.Honest.K2.Law (ReadsLight publicOk_of_reads)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)}

/-- **"ReadsLight" at every instance that passes "okStart": under the head and the opening, no premise more.** -/
theorem readsLight_of_okStart (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) : ReadsLight Zp Bs.G₀ ξ :=
  readsLight_of_att h O hx (OnBytes.HonestTrace.U3.Att.att_returns_at_open h O)

/-- **The same under the head alone**, at whatever ground "blankBy" returns at Zp. -/
theorem readsLight_of_okStart_at_ground (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) : ReadsLight Zp G ξ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  exact readsLight_of_okStart h O hx

/-- **So K2's public test says yes at every place of the kind, at every instance that passes "okStart".** -/
theorem publicOk_of_okStart (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    ∀ p ∈ switchPlaces Zp Bs.G₀,
      publicOk (withSwitchData Sz.ref (ProofFile.Honest.K1.lotData Sz.ref) Zp Bs.G₀) Bs.G₀.first.layout p
        ((segmentsOf Zp Bs.G₀).take p.link) ξ = true :=
  publicOk_of_reads h O (readsLight_of_okStart h O hx)

end OnBytes.HonestTrace.U3.Fit

#check @OnBytes.HonestTrace.U3.Fit.readsLight_of_okStart
#check @OnBytes.HonestTrace.U3.Fit.readsLight_of_okStart_at_ground
#check @OnBytes.HonestTrace.U3.Fit.publicOk_of_okStart
#print axioms OnBytes.HonestTrace.U3.Fit.readsLight_of_okStart
#print axioms OnBytes.HonestTrace.U3.Fit.readsLight_of_okStart_at_ground
#print axioms OnBytes.HonestTrace.U3.Fit.publicOk_of_okStart
