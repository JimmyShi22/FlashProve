-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/PublicOkAtJoinedHead.lean: UNDER THE LIBRARY's HEAD, AT EACH
CODE SWITCH OF THE PLAN: THE SWITCH's PUBLIC TEST `K2.publicOk`, AT THE SWITCHES' OWN DATA JOINED TO
THE SHARED SENDING's (`K2.withSwitchData` S (`K1.lotData` S) Zp G), IS ONE Bool AT ALL INSTANCES AT
WHICH THE DESCRIPTION's TEST ON THE INSTANCE SAYS YES (`FileDescription.okStart`). SO ITS YES AT ONE SUCH
INSTANCE IS ITS YES AT EVERY ONE. Three theorems; no definition; calls alone.

  `publicOk_joined_one_open`  h, the opening O, p of the plan at O's ground, okStart at ξ and ξ₀ ⊢
                              `K2.publicOk` at ξ is `K2.publicOk` at ξ₀
  `publicOk_joined_one_head`  the same at the maker's ground G (hG); no opening among the premises
  `publicOk_joined_all_head`  and its yes at ξ₀ ⊢ its yes at every ξ with okStart

By: `publicOk_joined_congr` (PublicOkAtJoined.lean); its hs from `K2.Law.ownSeated_at_head`
(Honest/K2/Law/OwnSeatedAtHead.lean), its h from `K2.Law.covOf_sized_of_okStart`
(Honest/K2/Law/CovOfAtStart.lean), twice: the Bool is true at both. The opening comes of the head
(the field opened, Johnson/P5J/LaidOpens.lean); its ground is the maker's by `IM.Open.blank`
(Johnson/IMR/SeatOpen.lean).

Limits. ONE FILLING: nothing on two fillings. THAT THE TEST SAYS YES AT ANY INSTANCE IS NOT SAID: h₀
of the third theorem is a premise; nor that any instance passes okStart. lay and segs are letters.
Stated at the joined term, not at `widerRows` (Honest/AtPureWider.lean), which unfolds to it. The
full size and the earlier hash `OnBytes.secondHashFunction`, as the head has them. It rests on two evaluations
in Lean's kernel in OwnSeatedAtHead.lean. All limits of PublicOkAtJoined.lean, OwnSeatedAtHead.lean
and CovOfAtStart.lean hold. The head is a hypothesis.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.PublicOkAtJoined
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnSeatedAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.CovOfAtStart
import Johnson.P5J.LaidOpens
import Johnson.IMR.SeatOpen

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

/-- **UNDER THE HEAD AND THE OPENING THE PUBLIC TEST AT THE JOINED DATA IS ONE Bool AT ALL INSTANCES
THAT PASS okStart.** CONDITIONAL: h; O; hp; hx, hx₀. -/
theorem publicOk_joined_one_open {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (S : Sz) {ξ ξ₀ : ProofFile.Inst} (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true)
    (hx₀ : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ₀ = true) (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces Zp Bs.G₀) :
    K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp Bs.G₀) lay p segs ξ =
      K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp Bs.G₀) lay p segs ξ₀ :=
  publicOk_joined_congr S (K2.Law.ownSeated_at_head h O p hp)
    ((K2.Law.covOf_sized_of_okStart h O hx).trans (K2.Law.covOf_sized_of_okStart h O hx₀).symm)
    lay segs

/-- **THE SAME AT THE MAKER's GROUND.** CONDITIONAL: h; hG: G is the maker's own ground; hp; hx,
hx₀. -/
theorem publicOk_joined_one_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) (S : Sz) {ξ ξ₀ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true)
    (hx₀ : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ₀ = true) (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces Zp G) :
    K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp G) lay p segs ξ =
      K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp G) lay p segs ξ₀ := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  subst e
  exact publicOk_joined_one_open h O S hx hx₀ lay segs hp

/-- **SO ITS YES AT ONE INSTANCE THAT PASSES okStart IS ITS YES AT EVERY ONE.** CONDITIONAL: h; hG;
hp; hx₀; h₀: the test says yes at ξ₀. -/
theorem publicOk_joined_all_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) (S : Sz) {ξ₀ : ProofFile.Inst}
    (hx₀ : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ₀ = true) (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces Zp G)
    (h₀ : K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp G) lay p segs ξ₀ = true) :
    ∀ ξ : ProofFile.Inst, (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true →
      K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp G) lay p segs ξ = true :=
  fun _ hx => (publicOk_joined_one_head h hG S hx hx₀ lay segs hp).trans h₀

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.publicOk_joined_one_open
#print axioms ProofFile.Honest.K5.publicOk_joined_one_head
#print axioms ProofFile.Honest.K5.publicOk_joined_all_head
