-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12LeftOfRest
import Johnson.Loose.H2K12.ClearAtHead
import Johnson.Loose.H2K12.RadiusAtHead
/-
Johnson/Loose/H2K12/K12RestOfPins.lean: THE LAW
OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN, sub-protocol number 354 of the
table's written list: TWO MORE PAYMENTS ON THE SHORTER LIST OF DEBTS K12Rest₆ (K12LeftOfRest.lean):
its fields radius and clear fall to its own field madePin. Two theorems: calls.
  k12Rest_of_pins  K12Rest₆ from the head and FOUR PREMISES, BY NAME: AtMgR at the condition of the
                   counted form, heads, and the two pins (madeRow Zp = true; the cut of the first
                   chain's flat list is the written one): K12Rest₆'s own fields reached, heads,
                   madePin, cutPin, to the letter; their docstrings stand there. radius:
                   radius_at_head (H2K12/RadiusAtHead.lean), a call of rad_in_scope.
                   clear: clear_atMg (H2K12/ClearAtHead.lean), off the written sendings and entries,
                   which madePin gives where the value is laid; "the value is laid" comes off the
                   head
  k12_kind_of_pins the same premises: then LastTypedAt → h.Kind 𝔏 K12
WHAT IT IS NOT. A JOINING: IT PAYS NO LAW. AtMgR holds the whole structure of facts on reached
states (Johnson/Desc/First/FoldFacts.lean), unpaid here. Who pays the two pins, and where
nobody does, stands in K12Rest₆'s docstrings. No example. The full size alone.
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K12

open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (KindName)
open P5J (AtMgA AtMgR F0T TS Free)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE SHORTER LIST OF DEBTS, FROM THE HEAD AND FOUR PREMISES.** -/
theorem k12Rest_of_pins (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    {L : VerifiableInference.Desc.K12.Door.Laid}
    (R : AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) L)
    (heads : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (hm : VerifiableInference.PlanWritten.madeRow Zp = true)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull) : K12Rest₆ h 𝔏 L :=
  ⟨heads, R, hm, hc, radius_at_head h hm,
    clear_atMg h (writtenAll354_of_pins h.scope h.laid.pub hm
      (h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks))⟩

/-- **THE KIND's LAW IN THE COUNTED FORM, FROM THE HEAD AND FOUR PREMISES.** -/
theorem k12_kind_of_pins (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    {L : VerifiableInference.Desc.K12.Door.Laid}
    (R : AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) L)
    (heads : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (hm : VerifiableInference.PlanWritten.madeRow Zp = true)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull) :
    LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL → h.Kind 𝔏 KindName.K12 :=
  k12_kind_of_rest (k12Rest_of_pins h 𝔏 R heads hm hc)

end H2K12

#print axioms H2K12.k12Rest_of_pins
#print axioms H2K12.k12_kind_of_pins
