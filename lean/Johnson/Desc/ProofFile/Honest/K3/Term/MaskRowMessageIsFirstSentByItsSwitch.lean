-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Term/MaskRowMessageIsFirstSentByItsSwitch.lean: the honest side of the
kind "lookup" (K3), at the full size: the message that holds a later link's mask row is one of which
the switch into that link is the FIRST sender (`K2.firstSender`, Honest/K2/ScriptLots.lean): no kept
copy. Two closed facts on the written places, evaluated in Lean's kernel, with a control; and what a
caller of K2's lots needs at a switch, under the head, in one theorem.

  `switchesAreFirstSendersOfMaskRowsWritten`   the closed fact
  `keptCopiesAreNotFirstSentWritten`           a control: of message number 1 no such switch is the first sender
  `writtenSwitchesLeadIntoLaterLinks`          no written place leads into link 0
  `maskRowMessageAtASwitchUnderTheHead`        under the head: the link is 1 at least; the message is one of
                                               the sending; the switch is its first sender; the written
                                               owner's place is the switch's

Limits. At the full size, at the earlier hash. The written places' own limits stand
(Honest/K2/Law/PlacesWritten.lean). Numbers on public data. Nothing is claimed on soundness,
completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.MaskRowOwnerAtTheWrittenBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain)
open ProofFile.Honest.K2 (SwitchPlace switchSent switchPlaces)
open ProofFile.Honest.K2.Law (placesW)
open P5J (AtMgA TS F0T)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

set_option maxRecDepth 1000000 in
/-- **At every written place that leads into a link below 25 the switch is the first sender of the
message that holds the link's mask row.** -/
theorem switchesAreFirstSendersOfMaskRowsWritten : (placesW.all fun p => decide (25 ≤ p.link) ||
    K2.firstSender p (maskRowMessageInSwitch p.link)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: of message number 1, a kept copy, no such switch is the first sender. -/
theorem keptCopiesAreNotFirstSentWritten : (placesW.any fun p => !decide (25 ≤ p.link) &&
    K2.firstSender p 1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- No written place leads into link 0. -/
theorem writtenSwitchesLeadIntoLaterLinks : (placesW.all fun p => decide (1 ≤ p.link)) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)}

/-- **What a caller of K2's lots needs at a switch that leads into a link below 25, under the head.**
-/
theorem maskRowMessageAtASwitchUnderTheHead (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀)
    (hl : p.link < 25) :
    1 ≤ p.link ∧ maskRowMessageInSwitch p.link < (switchSent p.sizes p.others).size ∧
      K2.firstSender p (maskRowMessageInSwitch p.link) = true ∧
      (maskRowOwnerWritten p.link).place = p.place := by
  have hpW : p ∈ placesW := by
    rw [← K2.Law.places_at_head h.toAtMg O]
    exact hp
  have a := List.all_eq_true.1 switchesAreFirstSendersOfMaskRowsWritten p hpW
  rw [decide_eq_false (Nat.not_le.2 hl), Bool.false_or] at a
  have b := of_decide_eq_true (List.all_eq_true.1 writtenSwitchesLeadIntoLaterLinks p hpW)
  have u := List.all_eq_true.1 switchesOwnMaskRowsWritten p hpW
  rw [decide_eq_false (Nat.not_le.2 hl), Bool.false_or] at u
  unfold switchOwnsLinksMaskRow at u
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at u
  have t := List.all_eq_true.1 switchMessagesHoldOneMaskRowWritten p hpW
  rw [decide_eq_false (Nat.not_le.2 hl), Bool.false_or] at t
  unfold switchMessageHoldsOneMaskRow at t
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at t
  exact ⟨b, t.1.1.1.1, a, (congrArg Addr.place u.1).symm⟩

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.switchesAreFirstSendersOfMaskRowsWritten
#print axioms ProofFile.Honest.K3.Term.keptCopiesAreNotFirstSentWritten
#print axioms ProofFile.Honest.K3.Term.writtenSwitchesLeadIntoLaterLinks
#print axioms ProofFile.Honest.K3.Term.maskRowMessageAtASwitchUnderTheHead
