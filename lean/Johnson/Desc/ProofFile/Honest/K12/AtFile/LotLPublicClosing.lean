-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLPublicClosing.lean

It states no goal. No property of the protocol is claimed.

The three public premises under
which the carrying message's rows return at the first chain's closing proximity test (hok and hpub
of `acceptedS_stands_L`, not beneath this file; the middle conjunct, hS, is what `shapeFits_head_L` pays inside
it), under the library's head at the blank ground.

  `ClosingAtEveryPlace`       hok's law as a statement: `closing_at_head`, a premise here
  `finish_in_places`          the finish is one of the places
  `closing_public_of_okStart` at the finish, at every instance that passes `okStart`
  `closing_public_at_valid`   hpub to the letter, where what is valid implies `okStart`
  `sends_two_of_fits`         the lot's public test gives the sending's two messages
  `shape_fits_of_place`       hS of `placeFits` and those two messages
  `closing_premises_at_finish`  hok, hS and hpub together at the finish, from the head and the ground

By what. `publicOk_of_okStart` (Johnson/HonestTrace/Joint/ReadsLightPaid.lean),
`fits_at_head` (K2/Law/PublicAtHead.lean), `fitsL_head_L` (AtFullSide/K12/FitsAtHeadL.lean),
`shapeFits_of` (K2/Law/Counts.lean).

Hypotheses. hc: what `closing_at_head` (K2/Law/ClosingAtHead.lean) says; LotLPublicPaid.lean
calls it. h: the head at the format's second hash function. hG: the blank ground, which is the ground that
`onlineProverFromPublicFiles` returns. hf: pl is the finish. hpub's D is the data at `Sz.ref`, at that ground: the
data that the term lays. At other sizes this says nothing, and K2/Law/LightWritten.lean shows a
closed test that says no at `Sz.small`.

Limits.
- The full size and the format's second hash function alone. Closed facts by Lean's kernel lie beneath.
- `okStart` is a premise of hpub here; LotLPublicServed.lean pays it at the named public files.
- They say that public tests pass: nothing on what a prover sends, nothing on a run.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.HonestTrace.Joint.ReadsLightPaid
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead
import AtFullSide.K12.FitsAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {W₀ Rc Tr : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {G : ProofFile.Ground} {pl : K2.SwitchPlace}

/-- **hok's law, as a statement**: under the opening the closing's public test says yes at every
place of the plan. This is the statement of `closing_at_head`
(Honest/K2/Law/ClosingAtHead.lean), less the head h. -/
def ClosingAtEveryPlace (W : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) : Prop :=
  ∀ (Bs : ProofFile.PureBase) (base : List (Block S ProofFile.Cl)),
    IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np) →
    ∀ p ∈ K2.switchPlaces Zp Bs.G₀,
      K2.closingOk K2.freshTable ((K2.segmentsOf Zp Bs.G₀).take p.link) p = true

/-- The finish is one of the code switch's places. -/
theorem finish_in_places (hf : finishAt Zp G = some pl) : pl ∈ K2.switchPlaces Zp G :=
  List.mem_of_find?_eq_some hf

/-- **At the finish**: at every instance that passes the first test, the filling's public test at
the closing says yes. -/
theorem closing_public_of_okStart (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hf : finishAt Zp G = some pl)
    {ξ : ProofFile.Inst} (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout pl
      ((K2.segmentsOf Zp G).take pl.link) ξ = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  exact OnBytes.HonestTrace.U3.Fit.publicOk_of_okStart h O hx pl (finish_in_places hf)

/-- **hpub to the letter**, at whatever the thread calls valid, where that implies the first test. -/
theorem closing_public_at_valid (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hf : finishAt Zp G = some pl)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (hV : ∀ v, Vd v → (F0T OnBytes.secondHashFunction Zp Np cF).okStart v.x = true) :
    ∀ v, Vd v →
      K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout pl
        ((K2.segmentsOf Zp G).take pl.link) v.x = true :=
  fun v hv => closing_public_of_okStart h hG hf (hV v hv)

/-- Where the lot's public test says yes the sending has two messages. -/
theorem sends_two_of_fits {q : VerifiableInference.Desc.K12.P12} {p : K2.SwitchPlace}
    (h : fitsL q p = true) : (sentL p).size = 2 := by
  simp only [fitsL, fitsLs, List.all_cons, Bool.and_eq_true] at h
  exact beq_iff_eq.1 h.1

/-- **hS**, from the shared sending's test at the place and the sending's two messages. -/
theorem shape_fits_of_place {p : K2.SwitchPlace} (hf : K2.placeFits p = true)
    (h2 : (sentL p).size = 2) : K2.ShapeFits p.sizes.codes (shapeL p) none := by
  have hs : (K2.switchSent p.sizes p.others).size = 2 := h2
  have h := K2.shapeFits_of (k := 0) hf (by rw [hs]; omega)
  have e : K2.foldAt (K2.switchFresh p.sizes p.others p.foldVars) 0 = none := by
    simp [K2.foldAt, K2.switchFresh, hs]
  rw [e] at h
  exact h

/-- **hok, hS and hpub together at the finish**, from the head and the blank ground. -/
theorem closing_premises_at_finish (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hf : finishAt Zp G = some pl)
    (hc : ClosingAtEveryPlace Z Zp Np cF) :
    K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take pl.link) pl = true ∧
      K2.ShapeFits pl.sizes.codes (shapeL pl) none ∧
      ∀ ξ : ProofFile.Inst, (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true →
        K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout pl
          ((K2.segmentsOf Zp G).take pl.link) ξ = true := by
  refine ⟨?_, ?_, fun ξ hx => closing_public_of_okStart h hG hf hx⟩
  · obtain ⟨Bs, base, O⟩ := h.laid.opened
    obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
    exact hc Bs base O pl (finish_in_places hf)
  · obtain ⟨pl', hf', hfit⟩ := fitsL_head_L h.toAtMg hG
    have e : pl' = pl := Option.some.inj (hf'.symm.trans hf)
    rw [e] at hfit
    refine shape_fits_of_place ?_ (sends_two_of_fits hfit)
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
    exact K2.Law.fits_at_head h.toAtMg O pl (finish_in_places hf)

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.finish_in_places
#print axioms ProofFile.Honest.K12.AtProof.closing_public_of_okStart
#print axioms ProofFile.Honest.K12.AtProof.closing_public_at_valid
#print axioms ProofFile.Honest.K12.AtProof.sends_two_of_fits
#print axioms ProofFile.Honest.K12.AtProof.shape_fits_of_place
#print axioms ProofFile.Honest.K12.AtProof.closing_premises_at_finish
