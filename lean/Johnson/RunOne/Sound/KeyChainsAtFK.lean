-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/KeyChainsAtFK.lean: It stands on Johnson/Desc/Key/Desc.lean.
THE THREE CHAINS' SEATS, GATHERED: "every seat of the chain is filled"
from its parts as the ledger of seats books them; the seats that are filled are paid in.

What is said. L := the number of the plan's lookups.
  `seats_of_parts`: a row of 2 + 6 · n + m pieces: the seats 0 and 1, the seats 2 + (6 · l + j)
    (l < n, j < 6) and the seats 2 + 6 · n + j (j < m) are all its seats.
  `fk_first_length`: the first chain's flat list has 2 + 6 · L + (the length of its back) blocks.
  `fk_chain₁`: at pieces that hold the flat list's blocks: the two sendings in front, six seats a
    lookup and the back's seats but the last give every seat; the last by `fk_end₁`.
  `fk_chain₂`: the shared chain: the seats between the first and the last give every seat; the
    first by `fk_front₂_seat`, the last by `fk_end₂`.
  `fk_chain₃`: the last chain has four seats: 0 and 2 give every seat; 1 by `fk_taken_seat`, 3 by
    `fk_end₃`.

Limits. Book-keeping: no seat is filled here but the five that were.
Terms: lean/GLOSSARY.md.

-/
import Johnson.RunOne.Sound.KeyLaterAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Sound
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.Key (descriptionFromSource Source FirstState Claim lookupsOf)
open _root_.Run (ckP)
open _root_.Iop (Err)

/-- The seats of a row of 2 + 6 · n + m pieces, by parts. -/
theorem seats_of_parts {S Cl W : Type} {F : Frame} (εs : ℝ≥0∞) (A : JointRow S F)
    (ps : List (Piece (ckP .two) F S Cl W)) (rs : List (JointRow S F)) (n m : ℕ)
    (hlen : ps.length = 2 + 6 * n + m) (g0 : ∀ i, i < 2 → SeatGood εs A ps rs i)
    (gl : ∀ l, l < n → ∀ j, j < 6 → SeatGood εs A ps rs (2 + (6 * l + j)))
    (gb : ∀ j, j < m → SeatGood εs A ps rs (2 + 6 * n + j)) :
    ∀ i, i < ps.length → SeatGood εs A ps rs i := by
  intro i hi
  by_cases h1 : i < 2
  · exact g0 i h1
  · by_cases h2 : i < 2 + 6 * n
    · have e : 2 + (6 * ((i - 2) / 6) + (i - 2) % 6) = i := by omega
      exact e ▸ gl ((i - 2) / 6) (by omega) ((i - 2) % 6) (by omega)
    · have e : 2 + 6 * n + (i - (2 + 6 * n)) = i := by omega
      exact e ▸ gb (i - (2 + 6 * n)) (by omega)

variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)

/-- **How many blocks the first chain has.** -/
theorem fk_first_length : (FK X N P).first.blocksInOrder.length =
    2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + ((fkFirst X N).back.length + 1) := by
  have hlen : (bareB (fkFirst X N).first :: (fkFirst X N).front.map bareB ++
      (fkLinks X).flatMap Link.blocksInOrder).length =
      2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length := by
    show ([bareB (fkFirst X N).first, _] ++ (fkLinks X).flatMap Link.blocksInOrder).length = _
    rw [List.length_append, length_flatMap_const Link.blocksInOrder 6 _ (link_six X)]
    simp [fkLinks]
  have h2 : ((bareB (fkFirst X N).first :: (fkFirst X N).front.map bareB ++
      (fkLinks X).flatMap Link.blocksInOrder) ++ fkTail X N).length =
      2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + ((fkFirst X N).back.length + 1) := by
    rw [List.length_append, hlen, List.length_append, List.length_map]
    rfl
  exact (congrArg List.length (fk_flat_eq X N P)).trans h2

/-- **Every seat of the first chain, from its parts.** k: the length of the chain's back; behind it
stands the last block. -/
theorem fk_chain₁ {F : Frame} {W : Type} (εs : ℝ≥0∞)
    (A : JointRow (H₁ X N P × (FK X N P).S₁) F)
    (p₀ : Piece (ckP .two) F (H₁ X N P × (FK X N P).S₁) (FK X N P).Cl W)
    (l : List (Piece (ckP .two) F (H₁ X N P × (FK X N P).S₁) (FK X N P).Cl W))
    (rs : List (JointRow (H₁ X N P × (FK X N P).S₁) F))
    (hbs : (p₀ :: l).map (·.b) =
      ((FK X N P).first.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (k : ℕ) (hk : (fkFirst X N).back.length = k)
    (hrow : keyRowAt A rs (l.length + 1) = (keyRowAt A rs l.length).passed fun t => asks₁ t.2)
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, (p₀ :: l)[l.length]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).rel)
    (g0 : ∀ i, i < 2 → SeatGood εs A (p₀ :: l) rs i)
    (gl : ∀ a, a < (Key.lookupsOf X.Y.k.oneTime).length → ∀ j, j < 6 →
      SeatGood εs A (p₀ :: l) rs (2 + (6 * a + j)))
    (gb : ∀ j, j < k →
      SeatGood εs A (p₀ :: l) rs (2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + j)) :
    ∀ i, i < (p₀ :: l).length → SeatGood εs A (p₀ :: l) rs i := by
  have hlen : (p₀ :: l).length = 2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + (k + 1) := by
    have e := congrArg List.length hbs
    rw [List.length_map, List.length_map, List.length_map, fk_first_length, hk] at e
    exact e
  refine seats_of_parts εs A (p₀ :: l) rs _ (k + 1) hlen g0 gl fun j hj => ?_
  by_cases hjk : j < k
  · exact gb j hjk
  · have e : l.length = 2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + j := by
      rw [List.length_cons] at hlen
      omega
    exact e ▸ fk_end₁ X N P εs A p₀ l rs hbs hrow hnd hp

/-- **Every seat of the shared chain, from the seats between its first and its last.** -/
theorem fk_chain₂ {F : Frame} {W : Type} (εs : ℝ≥0∞)
    (A : JointRow (H₂ X N P × (FK X N P).S₂) F)
    (p₀ : Piece (ckP .two) F (H₂ X N P × (FK X N P).S₂) (FK X N P).Cl W)
    (l : List (Piece (ckP .two) F (H₂ X N P × (FK X N P).S₂) (FK X N P).Cl W))
    (rs : List (JointRow (H₂ X N P × (FK X N P).S₂) F))
    (hbs : (p₀ :: l).map (·.b) =
      ((FK X N P).shared.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hrow₀ : keyRowAt A rs (0 + 1) = (keyRowAt A rs 0).passed fun _ => [])
    (hrow : keyRowAt A rs (l.length + 1) = (keyRowAt A rs l.length).passed fun t => asks₂ t.2)
    (hnd : (F.all.map (·.no)).Nodup)
    (hp₀ : ∀ p, (p₀ :: l)[0]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (0 + 1)).on ∧ ReadsBelow p.base (keyRowAt A rs (0 + 1)).rel)
    (hp : ∀ p, (p₀ :: l)[l.length]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).rel)
    (gm : ∀ i, 0 < i → i < l.length → SeatGood εs A (p₀ :: l) rs i) :
    ∀ i, i < (p₀ :: l).length → SeatGood εs A (p₀ :: l) rs i := by
  intro i hi
  by_cases h0 : i = 0
  · subst h0
    exact fk_front₂_seat X N P εs A (p₀ :: l) rs hbs hrow₀ hnd hp₀
  · by_cases hl : i = l.length
    · subst hl
      exact fk_end₂ X N P εs A p₀ l rs hbs hrow hnd hp
    · rw [List.length_cons] at hi
      exact gm i (by omega) (by omega)

/-- **Every seat of the last chain, from its seats 0 and 2.** -/
theorem fk_chain₃ {F : Frame} {W : Type} (εs : ℝ≥0∞)
    (A : JointRow (H₃ X N P × (FK X N P).S₃) F)
    (p₀ : Piece (ckP .two) F (H₃ X N P × (FK X N P).S₃) (FK X N P).Cl W)
    (l : List (Piece (ckP .two) F (H₃ X N P × (FK X N P).S₃) (FK X N P).Cl W))
    (rs : List (JointRow (H₃ X N P × (FK X N P).S₃) F))
    (hbs : (p₀ :: l).map (·.b) =
      ((FK X N P).second.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hrow₁ : keyRowAt A rs (1 + 1) =
      (keyRowAt A rs 1).passed fun t => asksTaken (Key.ownTest P) t.2)
    (hrow : keyRowAt A rs (l.length + 1) = (keyRowAt A rs l.length).passed fun t => asks₃ t.2)
    (hnd : (F.all.map (·.no)).Nodup)
    (hp₁ : ∀ p, (p₀ :: l)[1]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (1 + 1)).on ∧ ReadsBelow p.base (keyRowAt A rs (1 + 1)).rel)
    (hp : ∀ p, (p₀ :: l)[l.length]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).rel)
    (g0 : SeatGood εs A (p₀ :: l) rs 0) (g2 : SeatGood εs A (p₀ :: l) rs 2) :
    ∀ i, i < (p₀ :: l).length → SeatGood εs A (p₀ :: l) rs i := by
  obtain ⟨a, o, e, hf⟩ := fk_second_at X N P
  have hlen : (p₀ :: l).length = 4 := by
    have e' := congrArg List.length hbs
    rw [List.length_map, List.length_map, List.length_map, hf] at e'
    exact e'
  have hl : l.length = 3 := by
    rw [List.length_cons] at hlen
    omega
  intro i hi
  rw [hlen] at hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · exact g0
  · exact fk_taken_seat X N P εs A (p₀ :: l) rs hbs hrow₁ hnd hp₁
  · exact g2
  · exact hl ▸ fk_end₃ X N P εs A p₀ l rs hbs hrow hnd hp

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.seats_of_parts
#print axioms Johnson.RunOne.Sound.fk_first_length
#print axioms Johnson.RunOne.Sound.fk_chain₁
#print axioms Johnson.RunOne.Sound.fk_chain₂
#print axioms Johnson.RunOne.Sound.fk_chain₃
