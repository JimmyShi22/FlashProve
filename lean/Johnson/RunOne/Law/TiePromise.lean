-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TiePromise.lean: THE
PROMISES' TIE: at every border of the two lookups' links the table's promise with its history gives
the condition of the links' row at the filling of TieStated.lean. The record's half comes from the
history (rec_of_hist, RecOfHist.lean); the decoder's condition is the table's own promise, carried
from the record to the riding part: the table's reading B.h₁ reads, of a record, the instance, the
codes and the messages' records, and by the premise SmReads not their ledgers of mask entries.

Main names:
  smp_atSt, recOf_atSt: the reading at the riding part's record is the reading at the record.
  pin_atSt, pinw_atSt, noColl_atSt, hasSmp_atSt, freeAt_atSt: so for each of the five notions.
  pinned_link: at two lookups, at every border 2 … 14: the open pins are 0 and 1.
  tie_promise: TiePromise l j, l < 2, j ≤ 6.

Object: the links' rows and the table (TieStated.lean); Key.descriptionFromSource X N P through the history.
User: FieldR14.lean, FieldR110.lean and FieldsLayer.lean call tie_promise.
Letters: the table's B (under SmReads), at_, R, coll. Premises: those of rec_of_hist.

Limits. The promise BEHIND a block is not earned here. Nothing on the claims. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieStated
import Johnson.RunOne.Law.RecOfHist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TiePromise
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Source KRead Where FreeAt pinned)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁)
open Johnson.RunOne.KeyRows1 (open₁ n₁ on₁_two)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.Walk
open Johnson.RunOne.Law.WalkAtFK
open Johnson.RunOne.Law.RecOfHist
open Johnson.RunOne.Law.TieStated
open LPFD (On₁')

variable {Cells Mm Smp Rec : Type} {X : Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {D : WholeD} {B : BaseSt Cells Mm Smp Rec}
  {at_ : Where} {R : KRead Cells Mm} {coll : Strs → Rec → Prop}

/-- The sample at the riding part's record is the record's. -/
theorem smp_atSt (hS : B.SmReads) (p₀ : Xi) (i : ℕ) (s : FirstState) (j t : ℕ) :
    B.h₁.smp (atSt (pullK (stK p₀ i s))) j t = B.h₁.smp (p₀, s) j t := by
  show (B.orc₁ (B.arr j t)).bind (B.smAt (stm (stK p₀ i s))) =
    (B.orc₁ (B.arr j t)).bind (B.smAt s.d.st)
  congr 1
  funext o
  show ((s.d.st.oracles.map bareO)[o]?).bind (B.sm s.d.st.codes o) =
    (s.d.st.oracles[o]?).bind (B.sm s.d.st.codes o)
  rw [Array.getElem?_map]
  cases s.d.st.oracles[o]? with
  | none => rfl
  | some x => exact hS s.d.st.codes o x none

/-- The stored table's record likewise. -/
theorem recOf_atSt (p₀ : Xi) (i : ℕ) (s : FirstState) :
    B.h₁.recOf (atSt (pullK (stK p₀ i s))) = B.h₁.recOf (p₀, s) := rfl

theorem pin_atSt (hS : B.SmReads) (p₀ : Xi) (i : ℕ) (s : FirstState) (j t : ℕ) (y : Strs)
    (w : Wit Cells Unit Mm) :
    PIN (Fk X N P) B.h₁ j t (atSt (pullK (stK p₀ i s))) y w ↔ PIN (Fk X N P) B.h₁ j t (p₀, s) y w :=
        by
  unfold PIN
  rw [smp_atSt hS]

theorem pinw_atSt (p₀ : Xi) (i : ℕ) (s : FirstState) (y : Strs) (w : Wit Cells Unit Mm) :
    PINW B.h₁ (atSt (pullK (stK p₀ i s))) y w ↔ PINW B.h₁ (p₀, s) y w := Iff.rfl

theorem noColl_atSt (hS : B.SmReads) (p₀ : Xi) (i : ℕ) (s : FirstState) (j t : ℕ) (y : Strs) :
    NoColl (Fk X N P) B.h₁ j t (atSt (pullK (stK p₀ i s))) y ↔
      NoColl (Fk X N P) B.h₁ j t (p₀, s) y := by
  unfold NoColl
  rw [smp_atSt hS]

theorem hasSmp_atSt (hS : B.SmReads) (p₀ : Xi) (i : ℕ) (s : FirstState) (j t : ℕ) :
    hasSmp B.h₁ j t (atSt (pullK (stK p₀ i s))) = hasSmp B.h₁ j t (p₀, s) := by
  unfold hasSmp
  rw [smp_atSt hS]

theorem freeAt_atSt (p₀ : Xi) (i : ℕ) (s : FirstState) (y : Strs) :
    FreeAt B.h₁ coll (atSt (pullK (stK p₀ i s))) y ↔ FreeAt B.h₁ coll (p₀, s) y := Iff.rfl

/-- At two lookups the open pins at every border of the links are 0 and 1. -/
theorem pinned_link (k : ℕ) (h2 : 2 ≤ k) (h14 : k ≤ 14) : pinned (open₁ 2 k) = [0, 1] := by
  have c : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
      k = 12 ∨ k = 13 ∨ k = 14 := by omega
  rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The decoder's condition is the table's own promise.** -/
theorem cond_of_on (hS : B.SmReads) (k : ℕ) (h2 : 2 ≤ k) (h14 : k ≤ 14) (i : ℕ)
    (b : (Xi × FirstState) × (fr₁ D).E.Str)
    (h : Johnson.RunOne.KeyRows23.On₁ X N P D B at_ R coll k b) :
    condT X N P D B at_ coll (pullK (stK b.1.1 i b.1.2), b.2) := by
  have hn := on₁_two _ _ _ _ _ _ _ k b h
  obtain hm | ⟨-, hs, hf, hc⟩ := h
  · exact absurd rfl hm
  rw [hn, pinned_link k h2 h14] at hs hc
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hs
  exact ⟨⟨(hasSmp_atSt hS _ _ _ _ _).trans hs.1, (hasSmp_atSt hS _ _ _ _ _).trans hs.2⟩,
    hf.1, (noColl_atSt hS _ _ _ _ _ _).2 (hc 0 (by simp)),
    (noColl_atSt hS _ _ _ _ _ _).2 (hc 1 (by simp))⟩

/-- **THE PROMISES' TIE.** -/
theorem tie_promise (hS : B.SmReads) (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (l j : ℕ) (hl : l < 2) (hj : j ≤ 6) :
    TiePromise X N P D B at_ R coll l j := by
  intro b hb
  obtain ⟨⟨p₀, s⟩, y⟩ := b
  have hrec := rec_of_hist D y hp hR ha (2 + 6 * l + j) (by rw [hn]; omega) (p₀, s) hb.2
  show (rowT X N P D B at_ R coll l j).on ((p₀, s), y)
  unfold rowT
  refine (upF_on (Fr := fr₁ D) _ p₀ s y).2 ?_
  refine (rows7_on (Fr := fr₁ D) _ _ _ _ _ _ _ _ _ p₀ _ _ _ _ _ _ l j hj s y).2 ⟨?_, ?_⟩
  · exact cond_of_on hS (2 + 6 * l + j) (by omega) (by omega) _ ((p₀, s), y) hb.1
  rcases Nat.lt_or_ge j 6 with h6 | h6
  · rw [Nat.add_assoc] at hrec
    exact (recAt_link X l j h6 s).1 hrec
  · obtain rfl : j = 6 := by omega
    have e : 2 + 6 * l + 6 = 2 + (6 * (l + 1) + 0) := by omega
    rw [e] at hrec
    exact (recAt_link X (l + 1) 0 (by omega) s).1 hrec

end Johnson.RunOne.Law.TiePromise

#print axioms Johnson.RunOne.Law.TiePromise.smp_atSt
#print axioms Johnson.RunOne.Law.TiePromise.cond_of_on
#print axioms Johnson.RunOne.Law.TiePromise.tie_promise
