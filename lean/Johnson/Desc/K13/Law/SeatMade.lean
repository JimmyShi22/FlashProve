-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SeatMade.lean: W's SEAT IN THE RECORD's BOOK: a test with code on the first
chain's record; IT IS MADE BY W's COMMITMENT WITH KIND K13's BLOCK BEHIND IT, AND KEPT BY THE
CHAIN's LAST BLOCK. A definition, and statements with their proofs. It names no table of joints.
Main names:
  `wSeatB seat s`: the record names a number for W, and by the record's own book the message with
    that number sits at `seat` (a tree and a place in it).
  `atM4_w`: behind a yes of `atM4 P (K1.sendAtS P')` W's number is the number of the first message
    that the block has sent.
  `atM4_seat`: **the maker**: where the book in front has a place for every message, and the place
    sends a message at all: behind a yes W sits in the tree number (the book's trees in front) +
    `(K1.layOf P').tree 0`, at `(K1.layOf P').part 0`: by `K1.Booked.newer`
    (Johnson/Desc/K1/Law/BookAtRecord.lean).
  `firstEnd_seat`: **kept**: the first chain's last block returns the record.

What is not claimed. That the book in front has a place for every message, or how many trees it
holds. That the seat so made is what a table's numbers name. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.SitsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- **W's seat in the record's book.** -/
def wSeatB (seat : ℕ × ℕ) (s : S) : Bool :=
  (linAt s).any fun l => s.book.place[l.w]? == some seat

/-- Behind a yes W's number is the number of the first message that the block has sent. -/
theorem atM4_w {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s') :
    ∃ l, linAt s' = some l ∧ l.w = s.st.oracles.size := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid h
  obtain ⟨m, hm, hsz, hI⟩ := sendAtS_idsLast P' s s₁ r₁ r₂ g₁ h1
  obtain ⟨m₀, l, hm₀, hl, hmask⟩ := rowsB_mask h2
  rw [hm] at hm₀
  obtain rfl : m = m₀ := by
    injection hm₀
  have hn := sameAll_size (rowsB_same h2)
  have hb := (K1.sendAtS_booked P' s s₁ r₁ r₂ g₁ h1).msgs
  refine ⟨l, hl, ?_⟩
  rw [(hmask hI).1, hsz, hn, hb]
  omega

/-- A plan that passes `planSitsB` sends a message at W's place. -/
theorem PlanSits.pos {P : Where} {P' : K1.Par} (h : PlanSits P P') : 0 < P'.sent.size := by
  have e0 := h.first
  by_contra hn
  rw [Array.getElem?_eq_none (by omega)] at e0
  cases e0

/-- **THE MAKER.** -/
theorem atM4_seat {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s')
    (hfull : s.book.place.size = s.st.oracles.size) (h0 : 0 < P'.sent.size) :
    wSeatB (s.book.trees.size + (K1.layOf P').tree.getD 0 0, (K1.layOf P').part.getD 0 0) s' =
      true := by
  obtain ⟨l, hl, hw⟩ := atM4_w h
  have hp := (atM4_booked h).newer hfull h0
  unfold wSeatB
  rw [hl, Option.any_some, hw, ← Nat.add_zero s.st.oracles.size, hp]
  exact beq_self_eq_true _

/-- **KEPT**: the first chain's last block returns the record. -/
theorem firstEnd_seat (seat : ℕ × ℕ) (piece : ℕ) (front : List (Block S Cl)) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (First.firstEnd piece front).decide s rs gs = .ok s') (hs : wSeatB seat s = true) :
    wSeatB seat s' = true := by
  rw [Keeps.chainEnd_same _ _ _ _ _ h]
  exact hs

end VerifiableInference.Desc.K13.Law
