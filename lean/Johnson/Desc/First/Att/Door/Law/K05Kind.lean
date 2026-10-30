-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K05Kind.lean: kind K5: **THE END OF THE KIND's LAW IN THE COUNTED FORM (K05LawR, Door/Law/K05LawR.lean) IS ANOTHER FILE's OWN NAME FOR THE KIND's SHARE AT THE CLOSED CONSTANT**
(P5J.AtMgA.Kind, Johnson/P5J/RowsAtAll.lean): the field that a theorem over all kinds' laws takes for K5. The two conditions beside the promise are one: RchPub (Johnson/Top/H0/Walk/ReachPub.lean) at typedPub ("reached, and the public part is a
typed instance's") and P5J.AtMg.rch (Johnson/P5J/FourAtMg.lean).
Typed by reading Johnson/P5J/RowsAtAll.lean · FourAtMg.lean · RowsAtMg.lean · Johnson/Top/H0/Walk/ReachPub.lean ·
K05LawR.lean.

Main names:
  rch_is_R1: h.toAtMg.rch = RchPub ‹the seated description› typedPub. k05_kind_iff: KindTiedR ‹AtMgA.Kind's letters› at that RchPub … .K5 ↔ h.Kind 𝔏 .K5.
  k05_kind: K05LawR, at a head h, under its own named premises (the three flat lists' heads · the listed seats · K5Along at the picked condition), gives h.Kind 𝔏 .K5.
IS IT EMPTY HERE? Two unfoldings and one call. K05LawR IS A HYPOTHESIS HERE: NOT PROVED. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K05LawR
import Johnson.P5J.RowsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (RchAt RchPub)
open P5J (AtMg AtMgA mgAtAll F0T TS Free fullLinks)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)

/-- The condition AtMg.rch (FourAtMg.lean) beside the first table's promise is the picked one. -/
theorem rch_is_R1 : h.toAtMg.rch = RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub := rfl

/-- **The law's end is the name P5J.AtMgA.Kind (RowsAtAll.lean) for the kind's share.** -/
theorem k05_kind_iff :
    KindTiedR (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) (h.toAtMg.ex 𝔏) (h.toAtMg.row 𝔏)
      KindName.K5 ↔ h.Kind 𝔏 KindName.K5 := Iff.rfl

/-- **From the kind's law in the counted form: the field for K5.** -/
theorem k05_kind (law : K05LawR) (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (L : Laid) (hL : P5J.At.laid? Zp = some L)
    (A : K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) L
      (P5J.At.d12 Zp L).M h.𝔇.sent) : h.Kind 𝔏 KindName.K5 :=
  (k05_kind_iff h 𝔏).1 (law Z D r Zp Np cF x h 𝔏 q₁ q₂ q₃ L hL A)

end

end H2K5.Door

#print axioms H2K5.Door.rch_is_R1
#print axioms H2K5.Door.k05_kind_iff
#print axioms H2K5.Door.k05_kind
