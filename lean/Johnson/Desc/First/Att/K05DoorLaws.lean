-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05DoorLaws.lean: kind K5: WHAT A YES OF THE THREE BOOLS OF
Johnson/Desc/First/Att/K05DoorB.lean GIVES THE LAW: FrameIs
(Johnson/Desc/First/Att/K05SeatsOne.lean) and SeatOk (Johnson/Desc/First/Att/K05MsgTieOf.lean): so
that what the tie on the witness asks of the record is three Bools with code, one equation on the
live request's shape, and public facts.

IS IT EMPTY HERE? NO MEMBER IS SHOWN: no Bool is evaluated at a record.

Main names:
  `frameIs_of_B`: liveReqB (bornAt D i) s = true, the open link is number i, and its own copy of the
    live request has the description's shape: FrameIs D i ….
  `seatOk_of_B`: **SeatOk at every seat that lies in its table**: from seatsAtB at the plan's seats
    (List.ofFn seat) and shapesAtB at the shapes of the caller's list: oracle and place by the
    first; row by the second: the seat's row is below the shape's number of rows, which is at most 2
    to the statement's row bits (le_two_pow_ceilLog2, OnBytes/Slice/ProgCodes.lean).
  `maskBits_of_B`: where the shape of message number k has one mask row, its oracle has no row bits
    in its mask table (the premise hmb of addrTie_of, Johnson/Desc/First/Att/K05AddrTieOf.lean, at
    that oracle).
  `seatOk_on`, `maskBits_on`: the like from seatsOnB and shapesOnB: at the members that the pairs name.
  `lay_keeps`: the hearing's lay leaves the open link, the statement and the book. `live_rides`,
    `seatsOn_ride`, `shapesOn_ride`: so the Bools have behind the lay the value that they had in front.
Limits. A rule over letters. Who makes the Bools true at a border, and who keeps them, is not said.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MsgTieOf
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.K9 (seatAt)
open VerifiableInference.Desc.First.Look (Sent bornAt)

/-- **FrameIs from the Bool on the live request.** -/
theorem frameIs_of_B {D : Sent} {i : ℕ} {s : First.S} {L : LinkCtx}
    (h : liveReqB (bornAt D i) s = true) (hL : s.link? = some L) (hi : L.link = i)
    (hs : L.check.frame.shape = D.shape) : FrameIs D i L.check.frame := by
  obtain ⟨h1, h2, h3⟩ := liveReqB_at h hL
  exact ⟨hs, h3, h1.trans hi, h2⟩

/-- **SeatOk from the two Bools on the book and the statement.** -/
theorem seatOk_of_B (cs : Codes) (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (kept : ℕ) (own : List (ℕ × ℕ)) {s : First.S} {L : LinkCtx} (hL : s.link? = some L)
    (h1 : seatsAtB kept (List.ofFn seat) own s = true)
    (h2 : shapesAtB kept (l.map (·.1)) s = true)
    (z : VerifiableInference.Desc.First.Look.Seat) (hz : z.Fits cs l) :
    ∃ o, SeatOk cs l seat L.check.frame kept own s.st s.book z o := by
  obtain ⟨hk, hfit⟩ := id hz
  have e1 : (List.ofFn seat)[z.msg]? = some (seat ⟨z.msg, hk⟩) := by
    rw [List.getElem?_ofFn, dif_pos hk]
  have e2 : (l.map (·.1))[z.msg]? = some (l.get ⟨z.msg, hk⟩).1 := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hk]
    rfl
  obtain ⟨o, a1, a2, a3⟩ := seatsAtB_at h1 hL e1
  obtain ⟨o', y, b1, b2, b3⟩ := shapesAtB_at h2 hL e2
  obtain rfl : o = o' := Option.some.inj (a1.symm.trans b1)
  refine ⟨o, hz, a1, fun _ => ?_, ?_⟩
  · unfold seatAt
    rw [a2]
    show (if own.contains (seat ⟨z.msg, hk⟩) = true then some (seat ⟨z.msg, hk⟩) else none) = _
    rw [if_pos a3]
  · have hb : s.st.rowBits o (tableOfSeat z) = ceilLog2 ((l.get ⟨z.msg, hk⟩).1.rows (tableOfSeat z)) := by
      unfold Statement.rowBits
      rw [b2]
      show ceilLog2 (y.shape.rows (tableOfSeat z)) = _
      rw [b3]
    rw [hb]
    refine Nat.lt_of_lt_of_le ?_ (OnBytes.Slice.le_two_pow_ceilLog2 _)
    unfold tableOfSeat
    by_cases hm : z.mask = true
    · rw [if_pos hm] at hfit ⊢
      exact hfit.1
    · rw [if_neg hm] at hfit ⊢
      exact hfit.1

/-- One mask row: no row bits. -/
theorem maskBits_of_B (l : List (OracleShape × ℕ)) (kept : ℕ) {s : First.S} {L : LinkCtx}
    (hL : s.link? = some L) (h2 : shapesAtB kept (l.map (·.1)) s = true) {k o : ℕ}
    (hk : k < l.length) (ho : oracleOfMsg L.check.frame kept k = some o)
    (h1 : (l.get ⟨k, hk⟩).1.maskRows = 1) : s.st.rowBits o .mask = 0 := by
  have e2 : (l.map (·.1))[k]? = some (l.get ⟨k, hk⟩).1 := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hk]
    rfl
  obtain ⟨o', y, b1, b2, b3⟩ := shapesAtB_at h2 hL e2
  obtain rfl : o = o' := Option.some.inj (ho.symm.trans b1)
  unfold Statement.rowBits
  rw [b2]
  show ceilLog2 (y.shape.rows .mask) = 0
  rw [b3]
  show ceilLog2 (l.get ⟨k, hk⟩).1.maskRows = 0
  rw [h1]
  rfl

/-- **SeatOk from the two Bools at the members that are named**: at a seat whose member is named. -/
theorem seatOk_on (cs : Codes) (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (kept : ℕ) (own : List (ℕ × ℕ)) (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape))
    {s : First.S} {L : LinkCtx} (hL : s.link? = some L) (h1 : seatsOnB kept ps own s = true)
    (h2 : shapesOnB kept qs s = true) (z : VerifiableInference.Desc.First.Look.Seat)
    (hz : z.Fits cs l)
    (hp : ∀ hk : z.msg < l.length,
      (z.msg, seat ⟨z.msg, hk⟩) ∈ ps ∧ (z.msg, (l.get ⟨z.msg, hk⟩).1) ∈ qs) :
    ∃ o, SeatOk cs l seat L.check.frame kept own s.st s.book z o := by
  obtain ⟨hk, hfit⟩ := id hz
  obtain ⟨o, a1, a2, a3⟩ := seatsOnB_at h1 hL (hp hk).1
  obtain ⟨o', y, b1, b2, b3⟩ := shapesOnB_at h2 hL (hp hk).2
  obtain rfl : o = o' := Option.some.inj (a1.symm.trans b1)
  refine ⟨o, hz, a1, fun _ => ?_, ?_⟩
  · unfold seatAt
    rw [a2]
    show (if own.contains (seat ⟨z.msg, hk⟩) = true then some (seat ⟨z.msg, hk⟩) else none) = _
    rw [if_pos a3]
  · have hb : s.st.rowBits o (tableOfSeat z) = ceilLog2 ((l.get ⟨z.msg, hk⟩).1.rows (tableOfSeat z)) := by
      unfold Statement.rowBits
      rw [b2]
      show ceilLog2 (y.shape.rows (tableOfSeat z)) = _
      rw [b3]
    rw [hb]
    refine Nat.lt_of_lt_of_le ?_ (OnBytes.Slice.le_two_pow_ceilLog2 _)
    unfold tableOfSeat
    by_cases hm : z.mask = true
    · rw [if_pos hm] at hfit ⊢
      exact hfit.1
    · rw [if_neg hm] at hfit ⊢
      exact hfit.1

/-- One mask row: no row bits: at a member that is named. -/
theorem maskBits_on (kept : ℕ) (qs : List (ℕ × OracleShape)) {s : First.S} {L : LinkCtx}
    (hL : s.link? = some L) (h2 : shapesOnB kept qs s = true) {k o : ℕ} {sh : OracleShape}
    (hq : (k, sh) ∈ qs) (ho : oracleOfMsg L.check.frame kept k = some o) (h1 : sh.maskRows = 1) :
    s.st.rowBits o .mask = 0 := by
  obtain ⟨o', y, b1, b2, b3⟩ := shapesOnB_at h2 hL hq
  obtain rfl : o = o' := Option.some.inj (ho.symm.trans b1)
  unfold Statement.rowBits
  rw [b2]
  show ceilLog2 (y.shape.rows .mask) = 0
  rw [b3]
  show ceilLog2 sh.maskRows = 0
  rw [h1]
  rfl

/-! ## The hearing's lay leaves what the Bools read -/

/-- The lay leaves the open link, the statement and the book. -/
theorem lay_keeps {a b : First.S} {h : Heard} {F G : Fork} (hl : seatSO.ledger a = some F)
    (e : seatSO.lay a h G = some b) : b.link? = a.link? ∧ b.st = a.st ∧ b.book = a.book := by
  obtain ⟨att, ea, _, rfl⟩ := lay_is hl e
  refine ⟨?_, rfl, rfl⟩
  unfold First.S.link? behind
  rw [ea]

theorem live_rides {a b : First.S} {h : Heard} {F G : Fork} (hl : seatSO.ledger a = some F)
    (e : seatSO.lay a h G = some b) (born : Array (ℕ × ℕ)) : liveReqB born b = liveReqB born a := by
  unfold liveReqB
  rw [(lay_keeps hl e).1]

theorem seatsOn_ride {a b : First.S} {h : Heard} {F G : Fork} (hl : seatSO.ledger a = some F)
    (e : seatSO.lay a h G = some b) (k : ℕ) (ps : List (ℕ × (ℕ × ℕ))) (own : List (ℕ × ℕ)) :
    seatsOnB k ps own b = seatsOnB k ps own a := by
  unfold seatsOnB
  rw [(lay_keeps hl e).1, (lay_keeps hl e).2.2]

theorem shapesOn_ride {a b : First.S} {h : Heard} {F G : Fork} (hl : seatSO.ledger a = some F)
    (e : seatSO.lay a h G = some b) (k : ℕ) (qs : List (ℕ × OracleShape)) :
    shapesOnB k qs b = shapesOnB k qs a := by
  unfold shapesOnB
  rw [(lay_keeps hl e).1, (lay_keeps hl e).2.1]

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seatOk_on
#print axioms VerifiableInference.Desc.First.Att.P.maskBits_on
#print axioms VerifiableInference.Desc.First.Att.P.lay_keeps
#print axioms VerifiableInference.Desc.First.Att.P.live_rides
#print axioms VerifiableInference.Desc.First.Att.P.seatsOn_ride
#print axioms VerifiableInference.Desc.First.Att.P.shapesOn_ride
#print axioms VerifiableInference.Desc.First.Att.P.frameIs_of_B
#print axioms VerifiableInference.Desc.First.Att.P.seatOk_of_B
#print axioms VerifiableInference.Desc.First.Att.P.maskBits_of_B
