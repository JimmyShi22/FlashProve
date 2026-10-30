-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05FrontRides.lean: kind K5: FrontAll
(Johnson/Desc/First/Att/K05BehindWorth.lean) RIDES OVER THE KIND's OWN BLOCK: what holds of the
verifier's state in front of the block (piece 3 of an attention segment) holds of the state behind
it.

Why. The row K05_host_planes_door (Johnson/Desc/First/Att/K05HostPlanesDoor.lean) asks FrontAll at
sP, THE STATE BEHIND PIECE 3 (the border in front of piece 4): there the table's item formsT m 2
"planes" is open, and there the kind's readers answer. The items whose Bools pay FrontAll
(frontAll_of_door) are open IN FRONT of piece 3; three of them are dropped by the kind's own row.

IS IT EMPTY HERE? NO MEMBER IS SHOWN.

EVERY LETTER: a, b, F, G, h, rs, xr are the theorem's letters: F by the ledger's equation; G, h by
the hearing's return; b by the lay's equation.

Main name:
  `frontAll_rides`: FrontAll … gL a, seatSO.ledger a = some F, hear xr (F, rs, 0) = some (h, G, [],
    0) and seatSO.lay a h G = some b give FrontAll … gL b. The facts on the open link, the statement
    and the book: lay_keeps and the three rides (Johnson/Desc/First/Att/K05DoorLaws.lean) · the
    ledger: hear_below (Johnson/Desc/First/Att/K05HearBelow.lean): sized; as many slots; the same
    arrays · what the open segment holds of the lookup argument: the lay leaves it · gL's closing
    form and SecL: they read no ledger.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05BehindWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Sent)

/-- **FrontAll rides over the kind's own block.** -/
theorem frontAll_rides {x : VerifiableInference.Desc.First.Look.Place} {A : Attention.Plan} {D : Sent}
    {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))} {qs : List (ℕ × OracleShape)} {hi : ℕ}
    {gL : Forest.Heard} {a b : First.S} {F G : Fork} {h : Heard} {rs : List Fmt.RoundView}
    {xr : Params.AttentionRounds} (Y : FrontAll x A D own ps qs hi gL a)
    (hl : seatSO.ledger a = some F) (hh : hear xr (F, rs, 0) = some (h, G, [], 0))
    (e : seatSO.lay a h G = some b) : FrontAll x A D own ps qs hi gL b := by
  obtain ⟨L, T⟩ := Y.facts
  obtain ⟨k1, k2, _⟩ := lay_keeps hl e
  obtain ⟨hz, hns, T0, hT, hK, hW, hR1⟩ := Y.ledger F hl
  obtain ⟨hzG, bl⟩ := hear_below hh hz
  obtain ⟨att, ea, _, eb⟩ := lay_is hl e
  have hhere : b.here = .att { att with F := G, heard5 := some h } := by
    rw [eb]
    rfl
  refine ⟨⟨L, ⟨(live_rides hl e _).trans T.hB1, (seatsOn_ride hl e _ _ _).trans T.hB2,
    (shapesOn_ride hl e _ _).trans T.hB3, T.hlink, T.hshape, T.hlay, T.harr,
    by rw [k2]; exact T.hcodes, k1.trans T.hL, T.there⟩⟩, fun F' hF' => ?_, fun a₀ h0 => ?_, Y.plain,
    fun L' hL' => Y.sec L' (k1.symm.trans hL')⟩
  · have eF : G = F' := by
      unfold seatSO at hF'
      simp only [hhere] at hF'
      exact Option.some.inj hF'
    rw [← eF]
    exact ⟨hzG, by rw [bl.ns]; exact hns, T0, by rw [bl.trees]; exact hT, hK, hW, hR1⟩
  · rw [hhere] at h0
    obtain rfl := First.Here.att.inj h0
    exact Y.reads att ea

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.frontAll_rides
