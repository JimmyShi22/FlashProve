-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Pieces.lean: THE PIECES INTO WHICH A CODE SWITCH CUTS A STRETCH OF
THE REST (`switchPieces`, OnBytes/Iop/Cs.lean), AS FAR AS THE GROUND's TEST ON A NEW ROW's RUNS
READS THEM: where the stretch's places rise, each piece holds an entry, ends inside the stretch, has
a step of at least 1, and its last entry stands at the place of the stretch's entry of that number.
Statements and proofs.

  `PieceFits`, `PieceFits.mono`, `close_fits`   these four, of one piece; in a longer stretch; of
                    the open piece, closed
  `step_list`       one step of the loop leaves the closed pieces, or closes the open one
  `loop_fits`       the loop's closed pieces
  `pieces_fit`      the pieces of a stretch whose places rise

By: the loop's state as the library has it (`Inv`, `OpenOK`, `inv_loop`,
OnBytes/Slice/BlkCsStretch.lean; `pieceStep`, `switchPieces_eq`, OnBytes/Slice/BlkCsRows.lean).

Limits. Nothing on any property.

-/
import OnBytes.Slice.BlkCsStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice (pieceStep OpenOK Inv inv_loop switchPieces_eq)

/-- What the ground's test reads of a piece. P: the place of the stretch's entry, by number. n: the
stretch's entries so far. -/
structure PieceFits (P : Nat → Nat) (n : Nat) (p : SwitchPiece) : Prop where
  some : p.start < p.stop
  inside : p.stop ≤ n
  step : 0 < p.step
  last : p.first + p.step * (p.stop - p.start - 1) = P (p.stop - 1)

theorem PieceFits.mono {P : Nat → Nat} {n m : Nat} {p : SwitchPiece} (h : PieceFits P n p)
    (hm : n ≤ m) : PieceFits P m p := ⟨h.some, Nat.le_trans h.inside hm, h.step, h.last⟩

/-- The open piece, closed. -/
theorem close_fits {P : Nat → Nat} {n : Nat} {o : OpenPiece} (h : OpenOK P n o) :
    PieceFits P n (o.close n) := by
  refine ⟨h.lt, Nat.le_refl _, h.pos, ?_⟩
  show o.first + o.step.getD 1 * (n - o.start - 1) = P (n - 1)
  have hl := h.lt
  rw [h.law (n - 1) (by omega) (by omega)]
  congr 2
  omega

/-- One step of the loop leaves the closed pieces, or closes the open one. -/
theorem step_list (places : SwitchPlaces) (first : Nat)
    (s : List SwitchPiece × Option OpenPiece) (i : Nat) :
    (pieceStep places first s i).1 = s.1 ∨
      ∃ o, s.2 = some o ∧ (pieceStep places first s i).1 = o.close i :: s.1 := by
  obtain ⟨L, oo⟩ := s
  unfold pieceStep
  rcases oo with _ | ⟨st, fi, sp, la⟩
  · exact Or.inl rfl
  · rcases sp with _ | d
    · exact Or.inl rfl
    · by_cases c : (places.get (first + i) == la + d) = true
      · left
        simp [c]
      · right
        exact ⟨_, rfl, by simp [c]⟩

/-- The loop's closed pieces. -/
theorem loop_fits (places : SwitchPlaces) (first : Nat) : ∀ n : Nat,
    (∀ i j, i < j → j < n → places.get (first + i) < places.get (first + j)) →
    ∀ p ∈ ((List.range n).foldl (pieceStep places first) ([], none)).1,
      PieceFits (fun i => places.get (first + i)) n p
  | 0, _ => fun _ hp => absurd hp List.not_mem_nil
  | n + 1, hm => by
    intro p hp
    rw [List.range_succ, List.foldl_append] at hp
    have hm' : ∀ i j, i < j → j < n → places.get (first + i) < places.get (first + j) :=
      fun i j h1 h2 => hm i j h1 (by omega)
    have ih := loop_fits places first n hm'
    have hI := inv_loop places first (fun _ => 0) n hm'
    rcases step_list places first ((List.range n).foldl (pieceStep places first) ([], none)) n
      with e | ⟨o, ho, e⟩
    · have hp' : p ∈ ((List.range n).foldl (pieceStep places first) ([], none)).1 := by
        rw [← e]
        exact hp
      exact (ih p hp').mono (Nat.le_succ n)
    · have hp' : p ∈ o.close n :: ((List.range n).foldl (pieceStep places first) ([], none)).1 := by
        rw [← e]
        exact hp
      rcases List.mem_cons.1 hp' with rfl | hp'
      · have hok : OpenOK (fun i => places.get (first + i)) n o := by
          have h := hI.ok
          rw [ho] at h
          exact h
        exact (close_fits hok).mono (Nat.le_succ n)
      · exact (ih p hp').mono (Nat.le_succ n)

/-- **The pieces of a stretch whose places rise.** -/
theorem pieces_fit (places : SwitchPlaces) (first count : Nat)
    (hm : ∀ i j, i < j → j < count → places.get (first + i) < places.get (first + j)) :
    ∀ p ∈ switchPieces places first count,
      PieceFits (fun i => places.get (first + i)) count p := by
  intro p hp
  have hL := loop_fits places first count hm
  have hI := inv_loop places first (fun _ => 0) count hm
  rw [switchPieces_eq] at hp
  generalize (List.range count).foldl (pieceStep places first) ([], none) = s at hp hL hI
  obtain ⟨L, oo⟩ := s
  rcases oo with _ | o
  · exact absurd hp List.not_mem_nil
  · rcases List.mem_cons.1 (List.mem_reverse.1 hp) with rfl | hp
    · exact close_fits hI.ok
    · exact hL p hp

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.pieces_fit
