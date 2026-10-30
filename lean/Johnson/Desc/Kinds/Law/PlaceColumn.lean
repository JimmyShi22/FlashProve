-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlaceColumn.lean: THE LAYOUT's RULE FOR THE COLUMNS OF A LOOKUP's CALL
(OnBytes/Model/Calls.lean: place) IS THE OUTPUT HEAD's TEXT's (Johnson/Desc/Kinds/HeadIn.lean:
column). Both cut each length into powers of two, the largest first; sort the pieces of all
segments by decreasing size; keep the segments' order among pieces of one size; lay them from column
0 on. Arithmetic on lists of numbers; no kind, no state. Statements and proofs.

  bits_cut, bits_above   the sizes of a length's pieces above 2^b add up to the text's "above".
  aboveL_above, cntL_filter   so the two terms of FormsKeysPos.lean's formula are the text's two.
  place_column     MAIN: entry x of segment number a of a placed call lies in column
                   column ‹the lengths› a x: every length below 2^41, x below the segment's length.

BY Johnson/Road/FormsKeysPos.lean (place_columns · columnsOf_piece) and
Law/FromLookup.lean (piece_spec · column_eq).
WHAT IT IS NOT. Nothing on which calls a layout has. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Road.FormsKeysPos
import Johnson.Desc.Kinds.Law.FromLookup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open Finset
open OnBytes.Model (SegAsk topBit piecesBelow columnsOf place)
open OnBytes.Road (bitW cntL aboveL cntL_cons columnsOf_piece place_columns)
open Inst.Model.FFSeg (pieceStart)
open Inst.Model.FFSeg.IndexFacts (sum_bits)

/-- The bits from b + 1 on, and the bits up to b. -/
theorem bits_cut (n b : Nat) : ∀ m : Nat, ∑ b' ∈ range (b + 1 + m), bitW n b' =
    (∑ b' ∈ range (b + 1 + m), if b < b' then bitW n b' else 0) + ∑ b' ∈ range (b + 1), bitW n b'
  | 0 => by
    have h0 : (∑ b' ∈ range (b + 1 + 0), if b < b' then bitW n b' else 0) = 0 :=
      sum_eq_zero fun b' hb' => by
        have := mem_range.1 hb'
        rw [if_neg (by omega)]
    rw [h0, Nat.zero_add]
  | m + 1 => by
    have e : b + 1 + (m + 1) = b + 1 + m + 1 := rfl
    rw [e, sum_range_succ, sum_range_succ, bits_cut n b m, if_pos (by omega)]
    omega

/-- The sizes of a length's pieces above 2^b add up to the text's "above". -/
theorem bits_above {n k b : Nat} (hb : b < k) (hn : n < 2 ^ k) :
    (∑ b' ∈ range k, if b < b' then bitW n b' else 0) = above b n := by
  obtain ⟨m, rfl⟩ : ∃ m, k = b + 1 + m := ⟨k - (b + 1), by omega⟩
  have h1 : ∑ b' ∈ range (b + 1 + m), bitW n b' = n % 2 ^ (b + 1 + m) := sum_bits n _
  have h2 : ∑ b' ∈ range (b + 1), bitW n b' = n % 2 ^ (b + 1) := sum_bits n _
  have h3 := bits_cut n b m
  rw [h1, h2, Nat.mod_eq_of_lt hn] at h3
  have h4 := Nat.div_add_mod n (2 ^ (b + 1))
  unfold above
  rw [Nat.mul_comm] at h4
  omega

/-- So for a list of lengths. -/
theorem aboveL_above {k b : Nat} (hb : b < k) : ∀ ns : List Nat, (∀ n ∈ ns, n < 2 ^ k) →
    aboveL ns k b = (ns.map (above b)).sum
  | [], _ => by simp [aboveL, cntL]
  | n :: ns, h => by
    have ih := aboveL_above hb ns fun x hx => h x (List.mem_cons_of_mem _ hx)
    have e : aboveL (n :: ns) k b =
        (∑ b' ∈ range k, if b < b' then bitW n b' else 0) + aboveL ns k b := by
      unfold aboveL
      rw [← sum_add_distrib]
      refine sum_congr rfl fun b' _ => ?_
      rw [cntL_cons]
      split <;> rfl
    rw [e, ih, bits_above hb (h n List.mem_cons_self), List.map_cons, List.sum_cons]

/-- The pieces of one size. -/
theorem cntL_filter (b : Nat) : ∀ l : List Nat,
    cntL b l = (l.filter (·.testBit b)).length * 2 ^ b
  | [] => by simp [cntL]
  | n :: l => by
    rw [cntL_cons, cntL_filter b l]
    by_cases h : n.testBit b = true
    · rw [OnBytes.Road.bitW_true h]
      simp only [List.filter_cons, h, if_true, List.length_cons]
      ring
    · rw [OnBytes.Road.bitW_false (by simpa using h), Nat.zero_add]
      simp only [List.filter_cons, h, Bool.false_eq_true, if_false]

/-- **THE LAYOUT's RULE FOR A CALL's COLUMNS IS THE OUTPUT HEAD's TEXT's.** -/
theorem place_column (name kind : String) (asks : List SegAsk) (fl a x : Nat)
    (ha : a < asks.length) (hall : ∀ n ∈ asks.map (·.2.1), n < 2 ^ 41)
    (hx : x < (asks.map (·.2.1)).getD a 0) :
    ((place name kind asks fl).segs.getD a default).pos.getD x 0 =
      column (asks.map (·.2.1)) a x := by
  have hn : (asks.map (·.2.1)).getD a 0 < 2 ^ 41 := by
    refine hall _ ?_
    rw [List.getD_eq_getElem _ _ (by simpa using ha)]
    exact List.getElem_mem _
  obtain ⟨p1, p2, p3⟩ := Came.piece_spec hx hn
  have hb : Came.piece ((asks.map (·.2.1)).getD a 0) x < 41 := OnBytes.Road.lt_of_testBit p1 hn
  have ex : x = pieceStart ((asks.map (·.2.1)).getD a 0)
      (Came.piece ((asks.map (·.2.1)).getD a 0) x) +
      (x - above (Came.piece ((asks.map (·.2.1)).getD a 0) x)
        ((asks.map (·.2.1)).getD a 0)) := by
    show x = above _ _ + _
    omega
  rw [place_columns name kind asks fl a ha, Came.column_eq]
  conv_lhs => rw [ex]
  rw [columnsOf_piece (asks.map (·.2.1)) a (topBit + 1) _ _ hn p1 (by omega),
    aboveL_above (k := topBit + 1) hb _ hall, cntL_filter]

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.place_column
