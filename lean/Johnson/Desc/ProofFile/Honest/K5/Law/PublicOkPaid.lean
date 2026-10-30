-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/PublicOkPaid.lean: THE PREMISE hv OF OUR FORMS ON A CODE
SWITCH's LOTS ("at every valid input the switch's public test accepts the input's public instance"),
AT THE REFERENCE SIZES `Sz.ref`, THE SWITCHES' OWN DATA JOINED TO THE SHARED SENDING's, THE GROUND's
LAYOUT, THE PLAN's SEGMENTS AND THE FRAME's `ReadyInput`: CONDITIONAL ON THE LIBRARY's HEAD ALONE.
No yes of the test at an instance is a premise any more, and none that an instance passes okStart.
Five theorems; no definition; each is a call or two. Public data alone.

  `readsLight_at_open`  h; O; okStart at ξ ⊢ `K2.Law.ReadsLight` Zp Bs.G₀ ξ
  `publicOk_at_open`    h; O; okStart at ξ ⊢ at each place of the kind `K2.publicOk` says yes at ξ
  `publicOk_at_head`    the same at the maker's own ground G, with the opening taken from the head
  `hv_at_open`, `hv_at_head`  the two at every w with `ReadyInput` F H w, at w.x: hv's own form

The letters. The filling: `K2.withSwitchData` `Sz.ref` (`K1.lotData` `Sz.ref`) Zp G. The layout:
G.first.layout. The segments: (`K2.segmentsOf` Zp G).take p.link. The valid inputs: `ReadyInput`
(`P5J.F0T` `OnBytes.secondHashFunction` Zp Np cF) H, at any prover H.

By: `K2.Law.publicOk_of_two` (Honest/K2/Law/LightAtHead.lean): the test hangs on two named
statements; `K2.Law.digits_light_at_head` (DigitsLightAtHead.lean there): the first;
`OnBytes.HonestTrace.U3.Fit.readsLight_of_att` (Johnson/HonestTraceRun/U3ReadsDebt3.lean): the
second from one premise, that attention's maker of values returns at the twelve attention segments;
`OnBytes.HonestTrace.U3.Att.att_returns_at_open` (AttValsAtHead.lean in this folder): that premise.

WHAT LIES BENEATH, AMONG OTHER FILES: those under
Honest/K2/Law/ and Johnson/HonestTrace/U3Fit/, and AttValsAtHead.lean. This file is as good
as they are.

Limits. THE HEAD IS A HYPOTHESIS. At `Sz.ref`, at the ground's own layout and at the plan's own
segments alone: PublicOkAtReady.lean in this folder has these three as letters, at the price of one
yes of the test as a premise. THE FIRST THREE HOLD OF NOTHING WHERE NO INSTANCE PASSES okStart, AND
THE LAST TWO WHERE NO INPUT MEETS `ReadyInput`: neither is shown here to be met. Of `ReadyInput` the
first clause alone is spent. One filling: nothing on two fillings. The test reads the input's public
instance alone; what it accepts is not said here. Closed facts that Lean's kernel decided by
evaluation lie beneath, in the files named above. The full size; the format's second hash function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.DigitsLightAtHead
import Johnson.HonestTrace.U3Fit.ReadsDebt3
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput
import Johnson.P5J.LaidOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Chain)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Ky Tr X₀ X : Type}

/-- **UNDER THE HEAD AND THE OPENING THE LIGHT TEST SAYS YES AT THE READS' DATA, AT EVERY INSTANCE
THAT PASSES okStart.** CONDITIONAL: h; O; hx. -/
theorem readsLight_at_open {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {ξ : ProofFile.Inst} (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    K2.Law.ReadsLight Zp Bs.G₀ ξ :=
  OnBytes.HonestTrace.U3.Fit.readsLight_of_att h O hx
    (OnBytes.HonestTrace.U3.Att.att_returns_at_open h O)

/-- **UNDER THE HEAD AND THE OPENING THE SWITCH's PUBLIC TEST SAYS YES AT EVERY PLACE OF THE KIND
AND EVERY INSTANCE THAT PASSES okStart.** CONDITIONAL: h; O; hx. -/
theorem publicOk_at_open {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {ξ : ProofFile.Inst} (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    ∀ p ∈ K2.switchPlaces Zp Bs.G₀,
      K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) Bs.G₀.first.layout p
        ((K2.segmentsOf Zp Bs.G₀).take p.link) ξ = true :=
  K2.Law.publicOk_of_two h O (K2.Law.digits_light_at_head h O) (readsLight_at_open h O hx)

/-- **THE SAME AT THE MAKER's GROUND, UNDER THE HEAD ALONE.** CONDITIONAL: h; hG: G is the maker's
own ground; hx. -/
theorem publicOk_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    ∀ p ∈ K2.switchPlaces Zp G,
      K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout p
        ((K2.segmentsOf Zp G).take p.link) ξ = true := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  subst e
  exact publicOk_at_open h O hx

/-- **hv AT `ReadyInput`, UNDER THE HEAD AND THE OPENING.** NOT IN FRONT OF A LAW OVER COINS.
CONDITIONAL: h; O; hp. -/
theorem hv_at_open {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) {p : K2.SwitchPlace}
    (hp : p ∈ K2.switchPlaces Zp Bs.G₀) :
    ∀ w : Local W₀ Rc ProofFile.Inst Tr, ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) H w →
      K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) Bs.G₀.first.layout p
        ((K2.segmentsOf Zp Bs.G₀).take p.link) w.x = true :=
  fun _ hw => publicOk_at_open h O hw.1 p hp

/-- **hv AT `ReadyInput`, UNDER THE HEAD ALONE.** NOT IN FRONT OF A LAW OVER COINS.
CONDITIONAL: h; hG: G is the maker's own ground; hp. -/
theorem hv_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces Zp G) :
    ∀ w : Local W₀ Rc ProofFile.Inst Tr, ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) H w →
      K2.publicOk (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout p
        ((K2.segmentsOf Zp G).take p.link) w.x = true :=
  fun _ hw => publicOk_at_head h hG hw.1 p hp

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.readsLight_at_open
#print axioms ProofFile.Honest.K5.publicOk_at_open
#print axioms ProofFile.Honest.K5.publicOk_at_head
#print axioms ProofFile.Honest.K5.hv_at_open
#print axioms ProofFile.Honest.K5.hv_at_head
