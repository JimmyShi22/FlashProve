-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PanelsBlocks.lean: a long vector of the verifier's batched sumcheck, written over
the verifier's placed panels (vecOf, Johnson/Road/FormsKeysEnd.lean), is the library's long vector,
written as blocks over the library's panels (blk, nP: Cb/Pv/Lay/At/PanPlace.lean), if the two lists
go member by member, each pair has the same numbers of bits, and each pair's sides agree place by
place.

Main names:
  `window_blk`: one panel: the verifier's "if the place lies in the panel's stretch" is the
    library's block.
  `vecOf_blocks`: all panels. The first places are not asked: they are the library's by
    placed_offP (Johnson/Road/K4/PlaceOff.lean).
Limits. An identity on sums. That a pair of panels has the same bits and the same side is the
premise h2, pair by pair; nothing here shows it of any panel. Nothing on a run, on soundness or on
hiding.


-/
import Johnson.Road.K4.PlaceOff
import Johnson.Road.FormsKeysEnd
import Cb.Pv.Lay.At.PanPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes.Model.Layer (SBlk placePanels)
open Inst.Model.FFSeg (Dim Pan pans offP)
open Cb.Pv.Lay.At (blk blk_eq nP nP_mul)

variable {K : Type} [Field K]

/-- One panel: the verifier's stretch is the library's block. -/
theorem window_blk (D : Dim) {G : ℕ → ℕ → K} {V : ℕ → K} {b : SBlk} {pn : Pan}
    (ho : b.off = offP D pn) (hw : b.w = pn.wid D)
    (hG : ∀ t, t < 2 ^ pn.wid D → G (t / 2 ^ b.wy) (t % 2 ^ b.wy) = V t) (Y : ℕ) :
    (if b.off ≤ Y ∧ Y < b.off + 2 ^ b.w then
      G ((Y - b.off) / 2 ^ b.wy) ((Y - b.off) % 2 ^ b.wy) else 0) =
      blk (pn.wid D) (nP D pn) V Y := by
  rw [blk_eq, nP_mul, ho, hw]
  by_cases h : offP D pn ≤ Y ∧ Y < offP D pn + 2 ^ pn.wid D
  · rw [if_pos h, if_pos h]
    exact hG _ (by omega)
  · rw [if_neg h, if_neg h]

/-- **All panels.** bl: the panels before the placing. -/
theorem vecOf_blocks (D : Dim) (bl : Array SBlk) {G : SBlk → ℕ → ℕ → K} {V : Pan → ℕ → K}
    (h2 : List.Forall₂ (fun (b : SBlk) (pn : Pan) => b.w = pn.wid D ∧
      ∀ t, t < 2 ^ pn.wid D → G b (t / 2 ^ b.wy) (t % 2 ^ b.wy) = V pn t)
      (placePanels bl).1.toList (pans D)) (Y : ℕ) :
    vecOf G (placePanels bl).1.toList Y =
      ((pans D).map fun pn => blk (pn.wid D) (nP D pn) (V pn) Y).sum := by
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h2
  have hsz : bl.size = (pans D).length := by
    rw [← hlen, Array.length_toList, placePanels_size]
  have get : ∀ i (h : i < (placePanels bl).1.toList.length),
      (placePanels bl).1.toList.get ⟨i, h⟩ = (placePanels bl).1.getD i {} := by
    intro i h
    have h' : i < (placePanels bl).1.size := by simpa using h
    simp [Array.getD, h']
  have hw : ∀ j (h : j < (pans D).length), wOf bl j = ((pans D)[j]).wid D := by
    intro j h
    have h1 : j < (placePanels bl).1.toList.length := by rw [hlen]; exact h
    have e := (hget j h1 h).1
    rw [get j h1, ((placePanels_apart bl).1 j (by rw [hsz]; exact h)).1] at e
    exact e
  unfold vecOf
  refine congrArg List.sum ?_
  apply List.ext_get
  · rw [List.length_map, List.length_map, hlen]
  · intro i h1 h2'
    have k1 : i < (placePanels bl).1.toList.length := by simpa using h1
    have k2 : i < (pans D).length := by simpa using h2'
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map, List.getElem_map]
    obtain ⟨e1, e2⟩ := hget i k1 k2
    rw [List.get_eq_getElem, List.get_eq_getElem] at e1 e2
    refine window_blk D ?_ e1 e2 Y
    have g := get i k1
    rw [List.get_eq_getElem] at g
    rw [g]
    exact placed_offP D bl hsz hw k2

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.vecOf_blocks
