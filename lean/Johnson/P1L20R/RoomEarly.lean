-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomEarly.lean:
THE TWIN OF room_field (Johnson/P1L20R/RoomFold.lean) AT A SEGMENT'S FIRST TWO
PLACES: in front of "link m: laid" and in front of link m's first sub-protocol, at m = 1 ... 24, the
index-mask message's ledger is not closed and has just free0 entries less the bearing segments in
front of m: roomIsB free0 fvs m.

  roomEarlyB, roomEarlyB_full   a test with code on the written list: at the 48 places with piece
                    0 or 1 of a segment behind the first, the border's number lies in the fact's
                    stretch, and as many entries are taken in front of it as bearing segments stand
                    in front of m: by Lean's kernel
  room_early_places   what the test says of one place
  roomEarly_field   THE FIELD, in room_field's letters, with "p.piece < 2" and "0 < m" in the place
                    of "2 <= p.piece"

Limits. Those of room_field: RoomOwes is a premise, shown at nothing.
(Where this and lean/THEOREM.md differ, the page holds.) At segment 0 nothing is
said: in front of its first sub-protocol the ledger is not made yet. No soundness statement.

-/
import Johnson.P1L20R.RoomFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- A test with code on the written list: in front of a sub-protocol of segment m, behind segment
0, at piece 0 or 1. -/
def roomEarlyB : Bool :=
  (List.range 358).all fun k =>
    match (flatPlacesOf linksFull true)[k]? with
    | some p =>
      match p.link with
      | some m =>
        !(decide (p.piece < 2) && decide (0 < m)) ||
          (decide (3 ≤ k) && decide (k ≤ 355) && decide (m < 25) &&
            takenAt k == rowsBefore bearingList m)
      | none => true
    | none => true

set_option maxRecDepth 1000000 in
theorem roomEarlyB_full : roomEarlyB = true := by decide +kernel

theorem room_early_places {k m : ℕ} {p : VerifiableInference.Desc.Place}
    (hk : (flatPlacesOf linksFull true)[k]? = some p) (hm : p.link = some m) (h2 : p.piece < 2)
    (h0 : 0 < m) : 3 ≤ k ∧ k ≤ 355 ∧ m < 25 ∧ takenAt k = rowsBefore bearingList m := by
  have hlt : k < 358 := by
    rw [← places_length_full]
    exact (List.getElem?_eq_some_iff.1 hk).1
  have h := List.all_eq_true.1 roomEarlyB_full k (List.mem_range.2 hlt)
  simp only [hk, hm, h2, h0, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The twin of room_field at a segment's first two places**, behind segment 0. -/
theorem roomEarly_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {free0 : ℕ} {Q : Type} {start : Q → S}
    (H : RoomOwes c start free0) {X : Type} {Rch : ℕ → X → Prop} {at_ : X → Q × S}
    (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder start k (at_ a)) :
    ∀ k a p m, Rch k a → (at_ a).2.failed = none →
      (flatPlacesOf linksFull true)[k]? = some p → p.link = some m → p.piece < 2 → 0 < m →
      roomIsB free0 (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) m (at_ a).2 = true := by
  intro k a p m hr _ hk hm h2 h0
  obtain ⟨g1, g2, g3, g4⟩ := room_early_places hk hm h2 h0
  unfold roomIsB
  rw [rowsBefore_scope hS hR O hp g3, ← g4]
  exact room_at_reach hS hR O hp H (hRch k a hr) g1 g2

end

end P1L20

#print axioms P1L20.roomEarlyB_full
#print axioms P1L20.roomEarly_field
