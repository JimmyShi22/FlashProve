-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/FallPlaces.lean: the places of the fifty sub-protocols of the
proof file's first chain at which the falls of the batchings stand, by their numbers. In each of the
25 segments a fall may stand at the batching and at the sub-protocol without a round right after it.
The authors of these falls write their places out (chain 1, the segment, a piece, a kind). Lemmas on
the chain speak of the sub-protocol at a number. Here the two are tied: where the chain's places are
the written list `P5J.At.ps` (hypothesis `hps`), the sub-protocol at the number stands at the
written place.

  1  `placeOf_get`   the place of the sub-protocol at a number is the list's member at that number
  2  `fall_places_yes`, `fall_places_control`   the closed statement on the list, by
     `decide +kernel`, and a control that rejects
  3  `place_batch`, `place_behind`, `place_batch_head`, `place_behind_head`   the four lemmas

Limits.
  * `hps` is a hypothesis. `hps_cut` (Honest/Law/CoverCut.lean) proves it from the chain's written
    cut.
  * No fall is named here.
  * The closed statement is decided at one form of the written list. The full size alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName Block)

variable {S Cl : Type}

/-- The place of the sub-protocol at a number is the list's member at that number. -/
theorem placeOf_get {all : List (Block S Cl)} {ps : List Place} (hps : all.map (·.place) = ps)
    {n : Nat} {blk : Block S Cl} (hb : all[n]? = some blk) : ps[n]? = some blk.place := by
  rw [← hps, List.getElem?_map, hb]
  rfl

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- In segments 0 to 23 the batching stands at number `14 * l + 9`, at piece 8, and the sub-protocol
after it at piece 9. In segment 24 they stand at numbers 347 and 348, at pieces 10 and 11. -/
theorem fall_places_yes : ((List.range 24).all fun l =>
      decide (P5J.At.ps[14 * l + 9]? = some ⟨1, some l, 8, KindName.K9⟩) &&
        decide (P5J.At.ps[14 * l + 10]? = some ⟨1, some l, 9, KindName.frame⟩)) = true ∧
    P5J.At.ps[347]? = some ⟨1, some 24, 10, KindName.K9⟩ ∧
    P5J.At.ps[348]? = some ⟨1, some 24, 11, KindName.frame⟩ := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: the first test rejects if segment 24 is taken in. -/
theorem fall_places_control : ((List.range 25).all fun l =>
      decide (P5J.At.ps[14 * l + 9]? = some ⟨1, some l, 8, KindName.K9⟩) &&
        decide (P5J.At.ps[14 * l + 10]? = some ⟨1, some l, 9, KindName.frame⟩)) = false := by
  decide +kernel

/-- The batching of segment `l`, for `l` below 24. -/
theorem place_batch {all : List (Block S Cl)} (hps : all.map (·.place) = P5J.At.ps) {l : Nat}
    (hl : l < 24) {blk : Block S Cl} (hb : all[14 * l + 9]? = some blk) :
    blk.place = ⟨1, some l, 8, KindName.K9⟩ := by
  have t := List.all_eq_true.1 fall_places_yes.1 l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at t
  have t1 := of_decide_eq_true t.1
  rw [placeOf_get hps hb] at t1
  exact Option.some.inj t1

/-- The sub-protocol after the batching of segment `l`, for `l` below 24. -/
theorem place_behind {all : List (Block S Cl)} (hps : all.map (·.place) = P5J.At.ps) {l : Nat}
    (hl : l < 24) {blk : Block S Cl} (hb : all[14 * l + 10]? = some blk) :
    blk.place = ⟨1, some l, 9, KindName.frame⟩ := by
  have t := List.all_eq_true.1 fall_places_yes.1 l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at t
  have t2 := of_decide_eq_true t.2
  rw [placeOf_get hps hb] at t2
  exact Option.some.inj t2

/-- The batching of segment 24. -/
theorem place_batch_head {all : List (Block S Cl)} (hps : all.map (·.place) = P5J.At.ps)
    {blk : Block S Cl} (hb : all[347]? = some blk) :
    blk.place = ⟨1, some 24, 10, KindName.K9⟩ := by
  have t := fall_places_yes.2.1
  rw [placeOf_get hps hb] at t
  exact Option.some.inj t

/-- The sub-protocol after the batching of segment 24. -/
theorem place_behind_head {all : List (Block S Cl)} (hps : all.map (·.place) = P5J.At.ps)
    {blk : Block S Cl} (hb : all[348]? = some blk) :
    blk.place = ⟨1, some 24, 11, KindName.frame⟩ := by
  have t := fall_places_yes.2.2
  rw [placeOf_get hps hb] at t
  exact Option.some.inj t

end ProofFile.Honest

#print axioms ProofFile.Honest.placeOf_get
#print axioms ProofFile.Honest.fall_places_yes
#print axioms ProofFile.Honest.fall_places_control
#print axioms ProofFile.Honest.place_batch
#print axioms ProofFile.Honest.place_behind
#print axioms ProofFile.Honest.place_batch_head
#print axioms ProofFile.Honest.place_behind_head
