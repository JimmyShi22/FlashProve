-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/XchHeardAt.lean: the closing of a segment (K10): the premise hD1 of `tieBySwitch_head`
(Johnson/Desc/ProofFile/Honest/K10/Pay/XchSwitchHead.lean), under the head and the opening, at the filling `widerRows`
(Johnson/Desc/ProofFile/Honest/AtPureWider.lean): the data of an own message of a segment in front of the switch's link read no more
challenges than have been heard in front of the code switch. A bridge: the law is `heard_at_switches`
(AtFullSide/K2/HeardAtSwitches.lean); here it is brought to that premise's own form.

  **`heard_at_switch_head`**   hD1, to the sign. The two forms part in the number of the switch's border alone: the law counts the rounds
                     in front of the place's number in the written list of places (`switchNo`), the premise those in front of the
                     place's number in the chain's own list (`fxAt`, Pay/XchSwitchPub.lean); under the head the two numbers are one
                     (`borderNo_written`, Johnson/Desc/ProofFile/Honest/K1/Law/MembersByBorder.lean)

Limits. The head and the opening are premises. The full size and the older hash alone. Counts of challenges alone. No property is
claimed.
-/
import AtFullSide.K2.HeardAtSwitches
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSwitchPub
import Johnson.Desc.ProofFile.Honest.AtPureWider

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open VerifiableInference.Desc (Block Chain)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest ProofFile.Honest.K10
open ProofFile.Honest.K2 (SwitchPlace switchPlaces)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **The data of an own message of a segment in front read no more challenges than have been heard in front of the
switch.** -/
theorem heard_at_switch_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) (S : OnBytes.HonestTrace.Sz) {l : Nat} {p : SwitchPlace}
    (hP : p ∈ switchPlaces Zp Bs.G₀) (hlink : p.link = l) :
    ∀ (ξ : ProofFile.Inst) (i m : Nat) (a : MsgAddr), p.addrs i m = some a → i < l →
      (ProofFile.Honest.widerRows S Zp Bs.G₀ ξ).heardAt a ≤ fxAt cF p := by
  intro ξ i m a ha hi
  have e := AtFullSide.K2.heard_at_switches h O S p hP p hP ξ i m a (by rw [hlink]; exact hi) ha
  unfold fxAt
  rw [K1.borderNo_written h]
  exact e

end AtFullSide.K10

#print axioms AtFullSide.K10.heard_at_switch_head
