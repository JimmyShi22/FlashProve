-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LightAtHead.lean: the kind "the code switch" (K2): UNDER THE
LIBRARY's HEAD AND THE OPENING, AT THE REFERENCE SIZES `Sz.ref`, FOUR OF THE SIX NAMED STATEMENTS OF
LightDebts.lean (of this folder) HOLD; SO THE LOT's PUBLIC TEST `publicOk` AT EVERY PLACE OF THE
KIND HANGS ON THE OTHER TWO ALONE: THE DIGITS' AND THE READS'. Statements with their proofs:
transports and calls; no definition.

  `first_at_head`   the ground's codes, shape and layout are the written ones
  `switchSeat_at_head`, `mineSwitch_at_head`, `mineFirst_at_head`, `switchData_at_head`,
  `firstFill_at_head`   the kind's terms at the description's public part and ground are the written
                    terms of LightWritten.lean (of this folder)
  `addressed_at_head`, `switchesLight_at_head`, `openingLight_at_head`, `ownShares_at_head`
                    `Addressed` · `SwitchesLight Sz.ref` · `OpeningLight Sz.ref` ·
                    `OwnShares Sz.ref`
  `publicOk_of_two`   `DigitsLight` and `ReadsLight` at an instance ⊢ at each place of the kind
                    `publicOk` says yes at that instance, at the filling `withSwitchData Sz.ref
                    (K1.lotData Sz.ref)`, the ground's layout and the segments in front of the place

By: `places_at_head`, `segments_at_head` (PlacesWritten.lean of this folder) · `IM.Open.first`
(Johnson/IMR/SeatOpen.lean) · `first_written_in_scope` (Johnson/Goal/Numbers/MadeInScope.lean) ·
`pin1_atAll` (Johnson/Desc/K1/Law/PinsAtHead.lean) · `cellsVals_eq` (LabelByList.lean of this
folder) · the four closed facts of LightWritten.lean · `publicOk_of_debts` (LightDebts.lean).

Limits. THE HEAD AND THE OPENING ARE PREMISES. `DigitsLight` AND `ReadsLight` ARE PREMISES OF THE
LAST STATEMENT: PROVED IN NO FILE THAT THIS ONE STANDS ON. At `Sz.ref` alone. The full size; the
format's second hash function. EIGHT CLOSED FACTS BY LEAN's KERNEL LIE BENEATH, four of them controls. One
way alone, as the light test is. Nothing on what the data hold. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LightWritten
import Johnson.Desc.K1.Law.PinsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (layoutFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

section
variable (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
  (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (seatZ Zp Np) (secondAt Zp Np))
include h O

/-- **The ground's codes, shape and layout are the written ones.** -/
theorem first_at_head : Bs.G₀.first.codes = proofSizedFull.codes ∧
    Bs.G₀.first.shape = proofSizedFull.request ∧ Bs.G₀.first.layout = layoutFull := by
  obtain ⟨hc, -, hs, -, -, hl⟩ := VerifiableInference.PlanWritten.Joined.first_written_in_scope
    h.scope h.laid.pub (VerifiableInference.Desc.K1.pin1_atAll h)
  rw [O.first]
  exact ⟨hc, hs, hl⟩

theorem switchSeat_at_head : switchSeat Zp Bs.G₀ = switchSeatW := by
  unfold switchSeat switchSeatW ownSeats ownSeatsW
  rw [places_at_head h.toAtMg O, (first_at_head h O).2.1]

theorem mineSwitch_at_head : mineSwitch Zp Bs.G₀ = mineSwitchW := by
  funext a
  unfold mineSwitch mineSwitchW
  rw [switchSeat_at_head h O]

theorem mineFirst_at_head : mineFirst Zp Bs.G₀ = mineFirstW := by
  funext a
  unfold mineFirst mineFirstW
  rw [mineSwitch_at_head h O]

theorem switchData_at_head (Sd : Sz) : switchData Sd Zp Bs.G₀ = switchDataL Sd := by
  unfold switchData K1.firstData switchDataL
  rw [switchSeat_at_head h O, (first_at_head h O).1, (first_at_head h O).2.1,
    (first_at_head h O).2.2, cellsVals_eq]

theorem firstFill_at_head (Sd : Sz) : K1.firstFill Sd Bs.G₀.first = firstFillL Sd := by
  unfold K1.firstFill K1.firstData firstFillL
  rw [(first_at_head h O).1, (first_at_head h O).2.1, (first_at_head h O).2.2, cellsVals_eq]

/-- **Every own message of every segment in front of a place has an address there.** -/
theorem addressed_at_head : Addressed Zp Bs.G₀ := by
  intro p hp
  rw [places_at_head h.toAtMg O] at hp
  rw [segments_at_head h.toAtMg O, addressed_by, addrs_written p hp]
  exact addressedBy_take addressedW _

/-- **The light test at the switches' own data.** -/
theorem switchesLight_at_head : SwitchesLight Sz.ref Zp Bs.G₀ := by
  intro p hp
  rw [places_at_head h.toAtMg O] at hp
  rw [segments_at_head h.toAtMg O, switchData_at_head h O, mineSwitch_at_head h O,
    (first_at_head h O).2.2, lightAt_by, addrs_written p hp]
  exact lightBy_take switchesW _

/-- **The light test at the opening's data.** -/
theorem openingLight_at_head : OpeningLight Sz.ref Zp Bs.G₀ := by
  intro p hp
  rw [places_at_head h.toAtMg O] at hp
  rw [segments_at_head h.toAtMg O, firstFill_at_head h O, mineFirst_at_head h O,
    (first_at_head h O).2.2, lightAt_by, addrs_written p hp]
  exact lightBy_take openingW _

/-- **Each switch's own sending's share.** -/
theorem ownShares_at_head : OwnShares Sz.ref Zp Bs.G₀ := by
  intro p hp
  rw [places_at_head h.toAtMg O] at hp
  unfold ownShare
  rw [switchData_at_head h O, mineSwitch_at_head h O, (first_at_head h O).2.2]
  exact List.all_eq_true.1 ownSharesW p hp

/-- THE DIGITS' AND THE READS' STATEMENTS ARE PREMISES. **UNDER THE HEAD AND THE OPENING THE LOT's
PUBLIC TEST AT EVERY PLACE OF THE KIND HANGS ON THESE TWO ALONE.** -/
theorem publicOk_of_two {ξ : ProofFile.Inst} (h3 : DigitsLight Zp Bs.G₀) (h4 : ReadsLight Zp Bs.G₀ ξ) :
    ∀ p ∈ switchPlaces Zp Bs.G₀,
      publicOk (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) Bs.G₀.first.layout p
        ((segmentsOf Zp Bs.G₀).take p.link) ξ = true :=
  publicOk_of_debts (addressed_at_head h O) (switchesLight_at_head h O)
    (openingLight_at_head h O) h3 h4 (ownShares_at_head h O)

end

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.first_at_head
#print axioms ProofFile.Honest.K2.Law.switchSeat_at_head
#print axioms ProofFile.Honest.K2.Law.mineSwitch_at_head
#print axioms ProofFile.Honest.K2.Law.mineFirst_at_head
#print axioms ProofFile.Honest.K2.Law.switchData_at_head
#print axioms ProofFile.Honest.K2.Law.firstFill_at_head
#print axioms ProofFile.Honest.K2.Law.addressed_at_head
#print axioms ProofFile.Honest.K2.Law.switchesLight_at_head
#print axioms ProofFile.Honest.K2.Law.openingLight_at_head
#print axioms ProofFile.Honest.K2.Law.ownShares_at_head
#print axioms ProofFile.Honest.K2.Law.publicOk_of_two
