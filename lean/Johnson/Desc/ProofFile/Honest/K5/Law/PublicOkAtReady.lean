-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/PublicOkAtReady.lean: THE PREMISE hv OF OUR FORMS ON A CODE
SWITCH's LOTS ("at every valid input the switch's public test accepts the input's public instance"),
AT THE SWITCHES' OWN DATA JOINED TO THE SHARED SENDING's AND AT THE FRAME's `ReadyInput`, FROM ONE
YES OF THAT TEST AT ONE INSTANCE. CONDITIONAL ON THAT YES: h₀. One theorem; no definition; one call.

  `hv_joined_of_one`  h; hG; p of the plan; okStart at ξ₀; h₀: `K2.publicOk` says yes at ξ₀ ⊢ at
                      every w with `ReadyInput` F H w: `K2.publicOk` says yes at w.x

The letters. The filling: D := `K2.withSwitchData` S (`K1.lotData` S) Zp G. The valid inputs:
`ReadyInput` (`P5J.F0T` `OnBytes.secondHashFunction` Zp Np cF) H, at any prover H. The segments: segs.take
p.link, as the forms have them; lay and segs are letters.

By: `publicOk_joined_all_head` (PublicOkAtJoinedHead.lean), at the first clause of `ReadyInput`
(Honest/Thread/ReadyInput.lean): the description's test okStart at the input's instance.

Limits. h₀ IS A PREMISE: THAT THE TEST SAYS YES AT ANY INSTANCE IS PROVED NOWHERE HERE; nor that any
instance passes okStart. It spends the first clause of `ReadyInput`, okStart w.x, and no other.
NOT IN FRONT OF A LAW OVER COINS. ONE FILLING: nothing on two fillings. It holds of nothing where
no input meets `ReadyInput`. All limits of PublicOkAtJoinedHead.lean and ReadyInput.lean hold.
The head is a hypothesis.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.PublicOkAtJoinedHead
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA F0T TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Ky Tr X₀ X : Type}

/-- **hv AT THE JOINED DATA AND AT `ReadyInput`, FROM ONE YES AT ONE INSTANCE THAT PASSES okStart.**
NOT IN FRONT OF A LAW OVER COINS. CONDITIONAL: h; hG: G is the maker's own ground;
hp; hx₀; h₀: the test says yes at ξ₀. -/
theorem hv_joined_of_one (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) (S : Sz)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) {ξ₀ : ProofFile.Inst}
    (hx₀ : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ₀ = true) (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces Zp G)
    (h₀ : K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp G) lay p (segs.take p.link) ξ₀ =
      true) :
    ∀ w : Local W₀ Rc ProofFile.Inst Tr, ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) H w →
      K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp G) lay p (segs.take p.link) w.x = true :=
  fun w hw => publicOk_joined_all_head h hG S hx₀ lay (segs.take p.link) hp h₀ w.x hw.1

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.hv_joined_of_one
