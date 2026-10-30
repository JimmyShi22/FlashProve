-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/SeatsFacts.lean: on the written lists of places: where the
first chain's falls and marks may be, counted, as theorems; and which kinds are in the shared and in
the last chain (the second chain of the other files). The two tests on a place (`fallSeat`,
`markSeat`, Honest/Law/CoverSeats.lean) are counted in that file by lines that Lean's compiler runs;
here the same statements are theorems. They are stated at the full size's lists (`P5J.At.ps`,
`P5J.At.links`, Johnson/P5J/LettersAt.lean; `sharedPlaces true`,
Johnson/Desc/Shared/BordersShared.lean; `lastPlaces`, Johnson/Desc/Last/BordersLast.lean).

  1  `seats_counts`   358 places: 62 seats of falls (12 of the kind K4, 25 batchings, 25
     sub-protocols after a batching); 101 seats of marks (50 of K3, 12 of K4, 12 of K5, 1 of K6, 25
     of K8, 1 of K11: `markSeat` asks the kind alone, so these are all places of each kind); 12 are
     both (those of the kind K4); 207 are neither
  2  `seats_control`   the control that rejects: of the 75 places of the kind K9 not all are seats
     of falls; some place is neither a fall's seat nor a mark's
  3  `seatFrontB`, `seatFrontB_yes`, `seat_front`   the place right before a seat of a fall of the
     kind "frame", if there is one, is a seat of a fall of the kind K9: the batching
  4  `seat_front_control`   with K10 in place of K9 the test returns false
  5  `sharedPlaces_kinds`, `lastPlaces_kinds`   the kinds of the shared chain's twelve places and of
     the last chain's four, in their order; `other_chains_kinds`: they are "frame", K1, K12 and K14
     alone

Proved by `decide +kernel` (a closed, true statement on the library's own written lists, evaluated):
`seats_counts`, `seats_control`, `seat_front_control`, and the one test inside `seat_front`.

Limits.
  * Lists alone: which fall or mark is where is stated by its author; nothing here compares what an
    author supplies with the tests.
  * Decided at the lists as they are written in the library: if a list changes, the
    theorems have to be decided anew.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverSeats
import Johnson.Desc.Shared.BordersShared
import Johnson.Desc.Last.BordersLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.Shared (sharedPlaces)
open VerifiableInference.Desc.Last (lastPlaces)

/-! ## 1 The counts -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem seats_counts :
    P5J.At.ps.length = 358 ∧
    (P5J.At.ps.filter (fallSeat P5J.At.links)).length = 62 ∧
    (P5J.At.ps.filter fun p => fallSeat P5J.At.links p && p.kind == KindName.K4).length = 12 ∧
    (P5J.At.ps.filter fun p => fallSeat P5J.At.links p && p.kind == KindName.K9).length = 25 ∧
    (P5J.At.ps.filter fun p => fallSeat P5J.At.links p && p.kind == KindName.frame).length = 25 ∧
    (P5J.At.ps.filter markSeat).length = 101 ∧
    (P5J.At.ps.filter fun p => p.kind == KindName.K3).length = 50 ∧
    (P5J.At.ps.filter fun p => p.kind == KindName.K4).length = 12 ∧
    (P5J.At.ps.filter fun p => p.kind == KindName.K5).length = 12 ∧
    (P5J.At.ps.filter fun p => p.kind == KindName.K6).length = 1 ∧
    (P5J.At.ps.filter fun p => p.kind == KindName.K8).length = 25 ∧
    (P5J.At.ps.filter fun p => p.kind == KindName.K11).length = 1 ∧
    (P5J.At.ps.filter fun p => fallSeat P5J.At.links p && markSeat p).length = 12 ∧
    (P5J.At.ps.filter fun p => !fallSeat P5J.At.links p && !markSeat p).length = 207 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem seats_control :
    (P5J.At.ps.filter fun p => p.kind == KindName.K9).length = 75 ∧
    (P5J.At.ps.all fun p => p.kind != KindName.K9 || fallSeat P5J.At.links p) = false ∧
    (P5J.At.ps.all fun p => fallSeat P5J.At.links p || markSeat p) = false := by
  decide +kernel

/-! ## 2 Before a seat of the kind "frame" -/

/-- The test, number by number. `k`: the kind that is asked before. The 358 is the list's length
(`seats_counts`). Where there is no next place the test passes. -/
def seatFrontB (k : KindName) : Bool :=
  (List.range 358).all fun i =>
    match P5J.At.ps[i]?, P5J.At.ps[i + 1]? with
    | some p, some q =>
      !(fallSeat P5J.At.links q && q.kind == KindName.frame) ||
        (fallSeat P5J.At.links p && p.kind == k)
    | _, _ => true

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem seatFrontB_yes : seatFrontB KindName.K9 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem seat_front_control : seatFrontB KindName.K10 = false := by
  decide +kernel

theorem seat_front : ∀ (i : Nat) (p q : Place), P5J.At.ps[i]? = some p →
    P5J.At.ps[i + 1]? = some q → fallSeat P5J.At.links q = true → q.kind = KindName.frame →
    fallSeat P5J.At.links p = true ∧ p.kind = KindName.K9 := by
  intro i p q hp hq hf hk
  have hi : i < 358 := by
    by_contra hn
    have e : P5J.At.ps[i]? = none :=
      List.getElem?_eq_none (by rw [seats_counts.1]; omega)
    rw [e] at hp
    cases hp
  have h := List.all_eq_true.1 seatFrontB_yes i (List.mem_range.2 hi)
  rw [hp, hq] at h
  simp only [hf, hk, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-! ## 3 The two other chains -/

theorem sharedPlaces_kinds : (sharedPlaces true).map (·.kind) =
    [KindName.frame, .K14, .K1, .K14, .K14, .K1, .K14, .K14, .K14, .K12, .K12, .frame] := rfl

theorem lastPlaces_kinds : lastPlaces.map (·.kind) = [KindName.K14, .frame, .K12, .frame] := rfl

theorem other_chains_kinds : ∀ p ∈ sharedPlaces true ++ lastPlaces,
    p.kind = KindName.frame ∨ p.kind = KindName.K1 ∨ p.kind = KindName.K12 ∨
      p.kind = KindName.K14 := by
  decide

end ProofFile.Honest

#print axioms ProofFile.Honest.seats_counts
#print axioms ProofFile.Honest.seats_control
#print axioms ProofFile.Honest.seatFrontB_yes
#print axioms ProofFile.Honest.seat_front_control
#print axioms ProofFile.Honest.seat_front
#print axioms ProofFile.Honest.sharedPlaces_kinds
#print axioms ProofFile.Honest.lastPlaces_kinds
#print axioms ProofFile.Honest.other_chains_kinds
