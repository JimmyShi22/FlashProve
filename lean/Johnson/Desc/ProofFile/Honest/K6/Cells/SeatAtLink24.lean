-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/SeatAtLink24.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
THE SEAT OF THE HEAD's OWN MESSAGE IN THE FILLING's MAP OF SEATS (`K2.switchSeat`,
Honest/K2/OwnData.lean). Under the hypothesis h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). On public
data alone. No definition; one theorem.

  `k6_seat_at_link24`   the address of own message 0 of the switch into link 24 has the seat
                        (segment 24, message 0)

By. The lines of `switchSeat_reaches` (Honest/K5/Law/SwitchReach.lean), which stops in front of
segment 24 and ends in "there is an address": `seatBy_at` (Honest/K5/Law/SeatReach.lean),
`ownSeats_apart`; here at the place that the switch's authors' written list gives
(`places_at_head`, Honest/K2/Law/PlacesWritten.lean); the library's `IM.Open.blank`,
`IM.Open.first` (Johnson/IMR/SeatOpen.lean), `pins_at_head`, `made_row_gives`
(Johnson/Desc/First/Att/Door/Law/); `msgNo24W` (Honest/K6/Cells/Link24Main.lean).

What it is not.
  * A map of seats: nothing on what is laid there.
  * h: the full size and the format's second hash function alone.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Cells.Link24Main
import Johnson.Desc.ProofFile.Honest.K5.Law.SwitchReach
import Johnson.Desc.First.Att.Door.Law.K5CondOfHead
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales is no instance in this file: no statement here can take it
in silence. An instance is taken away, none is added. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest (Addr K2.SwitchPlace K2.switchSeat K2.ownSeats K2.switchPlaces)
open ProofFile.Honest.K5 (seatBy_at ownSeats_apart)
open ProofFile.Honest.K6 (msgNo24W)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

/-- CONDITIONAL: h; hG; hp; hlk. ON PUBLIC DATA ALONE. **THE SEAT OF THE HEAD's OWN MESSAGE.** -/
theorem k6_seat_at_link24 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {p : K2.SwitchPlace}
    (hp : p ∈ ProofFile.Honest.K2.Law.placesW) (hlk : p.link = 24) :
    K2.switchSeat Zp G (p.ownAddr 0) = some (24, 0) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : G = Bs.G₀ := Option.some.inj (hG.symm.trans (IM.Open.blank O))
  have hp' : p ∈ K2.switchPlaces Zp Bs.G₀ := by
    rw [ProofFile.Honest.K2.Law.places_at_head h.toAtMg O]
    exact hp
  have hx : ((⟨p.place, 0⟩ : Addr), 24, 1 + p.sizes.kept.length) ∈ K2.ownSeats Zp Bs.G₀ := by
    unfold K2.ownSeats
    exact List.mem_map.2 ⟨p, hp', by rw [hlk]⟩
  obtain ⟨-, -, f3, -, -, -⟩ := (H2K5.Door.made_row_gives (H2K5.Door.pins_at_head h.toAtMg).1).1
  have es : Zp.first.shape = VerifiableInference.PlanWritten.proofSizedFull.request := f3
  have hk : ProofFile.Honest.msgNo Zp.first.shape 24 0 0 = some 0 := by
    rw [es]
    exact msgNo24W
  show K2.switchSeat Zp Bs.G₀ ⟨⟨p.place, 0⟩, 1 + p.sizes.kept.length + 0⟩ = some (24, 0)
  unfold K2.switchSeat
  rw [IM.Open.first O]
  exact seatBy_at (ownSeats_apart O Bs.G₀) hx hk

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_seat_at_link24
