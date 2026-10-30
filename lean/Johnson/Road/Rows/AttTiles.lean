-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttTiles.lean: the verifier's weights on tiles and tokens, read in a field.

The tables of the attention sub-proof on queries, keys and values have weights on the tokens that
are made from weights on tiles (OnBytes/Model/AttentionHeard.lean: tileSums;
OnBytes/Model/AttentionTables.lean: tok). The library has the same weights as sums
(Inst/Model/Att/Points.lean: blkRow, blkCol, psiRow, psiCol). This file reads the first in a field,
as sums over the tile slots in the verifier's own letters. That these sums are the library's is
shown in Johnson/Road/Rows/AttEnds14Tiles.lean (tiles_row, tiles_col, tok_psi).

Main theorems.
 - foldl_track: a fold that adds a term to a measure at each step.
 - tileSums_fst, tileSums_snd: the weight of a tile row, of a tile column, as a sum over the tile
   slots.
 - tok_value, tok_size: the weight of a token.

Nothing is said about probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading eqTab)
open OnBytes.Attention (Shape)

variable {K : Type} [Field K]

/-- An entry of an array of which one entry has been changed. -/
theorem getD_modify (a : Array E) (k I : ℕ) (f : E → E) (hI : I < a.size) :
    (a.modify k f).getD I zeroE = if k = I then f (a.getD I zeroE) else a.getD I zeroE := by
  simp [Array.getD, hI, Array.getElem_modify]

/-- The sum of a list of the first n numbers' values. -/
theorem sum_list_range (v : ℕ → K) (n : ℕ) :
    ((List.range n).map v).sum = ∑ i ∈ range n, v i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A fold in which each step keeps a condition and adds g x to a measure: the whole fold keeps the
condition and adds the sum. -/
theorem foldl_track {α β : Type} (f : β → α → β) (μ : β → K) (ok : β → Prop) (g : α → K) :
    ∀ (l : List α) (b : β), ok b →
      (∀ b x, x ∈ l → ok b → ok (f b x) ∧ μ (f b x) = μ b + g x) →
      ok (l.foldl f b) ∧ μ (l.foldl f b) = μ b + (l.map g).sum
  | [], b, hb, _ => ⟨hb, by simp⟩
  | x :: l, b, hb, H => by
    obtain ⟨h1, h2⟩ := H b x List.mem_cons_self hb
    obtain ⟨h3, h4⟩ := foldl_track f μ ok g l (f b x) h1
      (fun b' y hy => H b' y (List.mem_cons_of_mem _ hy))
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons]
    ring

variable (ρ : Reading K)

/-- The weight of tile row I: the sum of the weights of the tile slots whose tile lies in it. -/
theorem tileSums_fst (S : Shape) (eP es : Array E) {I : ℕ} (hI : I < S.nT) :
    ρ.val ((Attention.tileSums S eP es).1.getD I zeroE) =
      ∑ P ∈ range S.hP, ∑ s ∈ range (S.nT - 1),
        if (S.cover P s).1 = I then ρ.val (eP.getD P zeroE) * ρ.val (es.getD s zeroE) else 0 := by
  unfold Attention.tileSums
  dsimp only
  refine Eq.trans (foldl_track _ (fun acc : Array E × Array E => ρ.val (acc.1.getD I zeroE))
    (fun acc => acc.1.size = S.nT ∧ acc.2.size = S.nT)
    (fun P => ∑ s ∈ range (S.nT - 1),
      if (S.cover P s).1 = I then ρ.val (eP.getD P zeroE) * ρ.val (es.getD s zeroE) else 0)
    _ _ ⟨by simp, by simp⟩ ?_).2 ?_
  · intro acc P _ hacc
    obtain ⟨k1, k2⟩ := foldl_track
      (μ := fun acc : Array E × Array E => ρ.val (acc.1.getD I zeroE))
      (ok := fun acc => acc.1.size = S.nT ∧ acc.2.size = S.nT)
      (g := fun s => if (S.cover P s).1 = I then
        ρ.val (eP.getD P zeroE) * ρ.val (es.getD s zeroE) else 0)
      (f := fun x sg =>
        (x.1.modify (S.cover P sg).1 (addE · (mulE (eP.getD P zeroE) (es.getD sg zeroE))),
          x.2.modify (S.cover P sg).2 (addE · (mulE (eP.getD P zeroE) (es.getD sg zeroE)))))
      (List.range (S.nT - 1)) acc hacc
      (by
        intro b s _ hb
        refine ⟨⟨by simp [hb.1], by simp [hb.2]⟩, ?_⟩
        show ρ.val ((b.1.modify (S.cover P s).1
          (addE · (mulE (eP.getD P zeroE) (es.getD s zeroE)))).getD I zeroE) = _
        rw [getD_modify _ _ _ _ (by rw [hb.1]; exact hI)]
        beta_reduce
        by_cases c : (S.cover P s).1 = I
        · rw [if_pos c, if_pos c, ρ.add, ρ.mul]
        · rw [if_neg c, if_neg c, add_zero])
    rw [sum_list_range] at k2
    exact ⟨k1, k2⟩
  · rw [sum_list_range]
    simp [Array.getD, hI, ρ.zero]

/-- The weight of tile column J: the sum of the weights of the tile slots whose tile lies in it. -/
theorem tileSums_snd (S : Shape) (eP es : Array E) {J : ℕ} (hJ : J < S.nT) :
    ρ.val ((Attention.tileSums S eP es).2.getD J zeroE) =
      ∑ P ∈ range S.hP, ∑ s ∈ range (S.nT - 1),
        if (S.cover P s).2 = J then ρ.val (eP.getD P zeroE) * ρ.val (es.getD s zeroE) else 0 := by
  unfold Attention.tileSums
  dsimp only
  refine Eq.trans (foldl_track _ (fun acc : Array E × Array E => ρ.val (acc.2.getD J zeroE))
    (fun acc => acc.1.size = S.nT ∧ acc.2.size = S.nT)
    (fun P => ∑ s ∈ range (S.nT - 1),
      if (S.cover P s).2 = J then ρ.val (eP.getD P zeroE) * ρ.val (es.getD s zeroE) else 0)
    _ _ ⟨by simp, by simp⟩ ?_).2 ?_
  · intro acc P _ hacc
    obtain ⟨k1, k2⟩ := foldl_track
      (μ := fun acc : Array E × Array E => ρ.val (acc.2.getD J zeroE))
      (ok := fun acc => acc.1.size = S.nT ∧ acc.2.size = S.nT)
      (g := fun s => if (S.cover P s).2 = J then
        ρ.val (eP.getD P zeroE) * ρ.val (es.getD s zeroE) else 0)
      (f := fun x sg =>
        (x.1.modify (S.cover P sg).1 (addE · (mulE (eP.getD P zeroE) (es.getD sg zeroE))),
          x.2.modify (S.cover P sg).2 (addE · (mulE (eP.getD P zeroE) (es.getD sg zeroE)))))
      (List.range (S.nT - 1)) acc hacc
      (by
        intro b s _ hb
        refine ⟨⟨by simp [hb.1], by simp [hb.2]⟩, ?_⟩
        show ρ.val ((b.2.modify (S.cover P s).2
          (addE · (mulE (eP.getD P zeroE) (es.getD s zeroE)))).getD J zeroE) = _
        rw [getD_modify _ _ _ _ (by rw [hb.2]; exact hJ)]
        beta_reduce
        by_cases c : (S.cover P s).2 = J
        · rw [if_pos c, if_pos c, ρ.add, ρ.mul]
        · rw [if_neg c, if_neg c, add_zero])
    rw [sum_list_range] at k2
    exact ⟨k1, k2⟩
  · rw [sum_list_range]
    simp [Array.getD, hJ, ρ.zero]

/-- There is a weight for each token. -/
theorem tok_size (S : Shape) (hi lo : Array E) : (Attention.tok S hi lo).size = S.T := by
  simp [Attention.tok]

/-- The weight of token i: its tile's weight times the equality weight of its place in the tile. -/
theorem tok_value (S : Shape) (hi lo : Array E) {i : ℕ} (h : i < S.T) :
    ρ.val ((Attention.tok S hi lo).getD i zeroE) =
      ρ.val (hi.getD (i / S.B) zeroE) * ρ.val ((eqTab lo).getD (i % S.B) zeroE) := by
  have e : (Array.range S.T).getD i 0 = i := by simp [Array.getD, h]
  unfold Attention.tok
  dsimp only
  rw [getD_map_lt (Array.range S.T) _ (by simpa using h) zeroE 0, e, ρ.mul]

end OnBytes.Road.Rows
