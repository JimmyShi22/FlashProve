-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/IndexKept.lean: THE THREE TESTS ON THE INDEX MASKS' MESSAGE
(Johnson/Desc/K1/Law/IndexBools.lean: its number is n; it is there; by the record's book it sits at
a seat) ARE KEPT by kind K13's joined block, by W's commitment with the kind's block behind it, by a
segment's later moment and by the first chain's last block. Statements with their proofs. It names
no table of joints.
Main names:
  `IndexKept s s'`: each of the three, at every n and seat, if it says yes of s says yes of s'.
  `indexKept_of`: it holds wherever "out" is as it was, no message goes, and the older places stay.
  `atM3_index`, `atM4_index`, `commitAtS_index`, `firstEnd_index`: **the four blocks.**

What is not claimed. That other kinds' blocks keep the three. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.K1.Law.IndexBools
import Johnson.Desc.K1.Law.LaterAtRecord
import Johnson.Desc.Tidy.Still

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (indexIsB indexThereB indexSeatB)

variable {Cl : Type}

/-- Each of the three, if it says yes of s, says yes of s'. -/
def IndexKept (s s' : S) : Prop :=
  (∀ n, indexIsB n s = true → indexIsB n s' = true) ∧
    (indexThereB s = true → indexThereB s' = true) ∧
    ∀ seat, indexSeatB seat s = true → indexSeatB seat s' = true

/-- Where "out" is as it was, no message goes, and the older places stay. -/
theorem indexKept_of {s s' : S} (ho : s'.out = s.out)
    (hn : s.st.oracles.size ≤ s'.st.oracles.size)
    (hp : ∀ (i : ℕ) (seat : ℕ × ℕ), s.book.place[i]? = some seat →
      s'.book.place[i]? = some seat) :
    IndexKept s s' := by
  unfold IndexKept indexIsB indexThereB indexSeatB
  rw [ho]
  refine ⟨fun _ h => h, fun h => ?_, fun seat h => ?_⟩
  · have hlt : s.out.indexMasks < s.st.oracles.size := by
      by_contra hx
      rw [Array.getElem?_eq_none (by omega)] at h
      cases h
    rw [Array.getElem?_eq_getElem (by omega)]
    rfl
  · rw [beq_iff_eq] at h ⊢
    exact hp _ _ h

theorem IndexKept.trans {a b c : S} (h : IndexKept a b) (k : IndexKept b c) : IndexKept a c :=
  ⟨fun n x => k.1 n (h.1 n x), fun x => k.2.1 (h.2.1 x), fun t x => k.2.2 t (h.2.2 t x)⟩

/-- **Kind K13's joined block.** -/
theorem atM3_index {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    IndexKept s s' := by
  obtain ⟨e1, e2⟩ := atM3_book h
  obtain ⟨_, _, _, _, e⟩ := atM3_rec h
  refine indexKept_of ?_ (by rw [e2]) fun i seat hs => by rw [e1]; exact hs
  rw [e]

/-- **W's commitment with the kind's block behind it.** -/
theorem atM4_index {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s') : IndexKept s s' := by
  have hb := atM4_booked h
  refine indexKept_of (atM4_rec h).2.2.2.1 (by rw [hb.msgs]; omega) fun i seat hs =>
    hb.seat_kept hs

/-- **A segment's later moment.** -/
theorem commitAtS_index (P : K1.Par) (link moment : ℕ) (arrays : Option (List ℕ)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (K1.commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    IndexKept s s' := by
  have hb := K1.commitAtS_booked P link moment arrays s s' r₁ r₂ gs h
  refine indexKept_of (K1.commitAtS_left P link moment arrays s s' _ gs h).2
    (by rw [hb.msgs]; omega) fun i seat hs => hb.seat_kept hs

/-- **The first chain's last block.** -/
theorem firstEnd_index (piece : ℕ) (front : List (Block S Cl)) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (First.firstEnd piece front).decide s rs gs = .ok s') : IndexKept s s' := by
  rw [Keeps.chainEnd_same _ _ _ _ _ h]
  exact ⟨fun _ x => x, id, fun _ x => x⟩

end VerifiableInference.Desc.K13.Law
