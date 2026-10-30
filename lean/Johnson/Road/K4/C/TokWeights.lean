-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TokWeights.lean: CONDITIONAL.

Not shown here. That the families of the verifier's list are of the sorts that TokAsk names: a
hypothesis on public names. Nothing on places or on cells. No example is known. No property is
claimed.

A FAMILY's WEIGHTS AT A TOKEN POINT ARE THE COMBINATION, UNDER THE POINT's EQUALITY WEIGHTS, OF ITS
WEIGHTS AT THE TOKENS. The second token sumcheck of the sub-protocol K4 ends at a point z of the
tokens' cube. The honest side lays the reads at the tokens' corners (Sides.readsTok,
Johnson/Desc/K4/Honest/Sides.lean: the short tables at the point "rt", the long ones at "Y"). Here,
for the weights that the verifier's function gives a family (phiOf, OnBytes/Model/Layer.lean): read
in the field, weight j at z is the sum over the tokens t of eq(z, t) times weight j at the corner
t.

  tokPts         the two named points at a token point.
  TokAsk         a family bears one of the three names on the lookup's planes; or it is short at
                 "rt"; or long at "Y"; or its point is neither.
  cornerAt_size, cornerAt_pt, eqTab_cornerAt   the corner of a token as a point.
  find_rt, find_Y, find_none   what is found in tokPts under a name.
  tok_short, tok_long   the law for the two sorts of weights.
-/
import Johnson.Road.K4.C.Weights
import Johnson.Road.FormsKeysCalls
import Johnson.Road.Rows.AttEnds14Below

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay TableAsk phiOf)
open OnBytes.Desc.First.K4.Honest (wtsFit)

/-- The honest side's corner of the cube as a point (Johnson/Desc/K4/Honest/Cells.lean), pinned by
its full name: under this namespace the bare name is another function's. -/
local notation "cornerAt" => OnBytes.Desc.First.K4.Honest.bitsOf

/-- The two named points at a token point z: readsTok's list. -/
def tokPts (zlow z : Array E) : List (String × Array E) := [("rt", z), ("Y", longPoint zlow z)]

/-- The sorts of family. This defines a hypothesis; the definition claims nothing. -/
def TokAsk (a : TableAsk) : Prop :=
  ¬ Named a ∨ (a.point = "rt" ∧ a.lng = false) ∨ (a.point = "Y" ∧ a.lng = true) ∨
    (a.point ≠ "rt" ∧ a.point ≠ "Y")

/-- A corner has as many coordinates as the cube has variables. -/
theorem cornerAt_size (n t : ℕ) : (cornerAt n t).size = n := by
  unfold OnBytes.Desc.First.K4.Honest.bitsOf
  rw [Array.size_map, Array.size_range]

/-- A coordinate of a corner. -/
theorem cornerAt_pt (n t s : ℕ) (hs : s < n) :
    pt Reading.gl (cornerAt n t) (0 + s) = if t.testBit (n - 1 - s) then 1 else 0 := by
  unfold pt OnBytes.Desc.First.K4.Honest.bitsOf
  rw [Nat.zero_add, getD_map_lt (Array.range n) _ (by rw [Array.size_range]; exact hs) zeroE 0]
  have e : (Array.range n).getD s 0 = s := by simp [Array.getD, hs]
  rw [e]
  cases t.testBit (n - 1 - s)
  · simp [Reading.gl.zero]
  · simp [Reading.gl.one]

/-- The table of equality weights at a corner. -/
theorem eqTab_cornerAt {n t i : ℕ} (ht : t < 2 ^ n) (hi : i < 2 ^ n) :
    Reading.gl.val ((eqTab (cornerAt n t)).getD i zeroE) = if i = t then 1 else 0 := by
  rw [eqTab_value Reading.gl _ i (by rw [cornerAt_size]; exact hi), cornerAt_size]
  exact eqN_bool n 0 _ ht hi fun s hs => cornerAt_pt n t s hs

/-- What is found under "rt". -/
theorem find_rt (zlow z : Array E) :
    ((tokPts zlow z).find? fun q => q.1 == "rt") = some ("rt", z) := rfl

/-- What is found under "Y". -/
theorem find_Y (zlow z : Array E) :
    ((tokPts zlow z).find? fun q => q.1 == "Y") = some ("Y", longPoint zlow z) := rfl

/-- Nothing is found under another name. -/
theorem find_none (zlow z : Array E) {n : String} (h1 : n ≠ "rt") (h2 : n ≠ "Y") :
    ((tokPts zlow z).find? fun q => q.1 == n) = none := by
  unfold tokPts
  rw [List.find?_cons_of_neg (by
      show ¬ (("rt" : String) == n) = true
      rw [beq_iff_eq]
      exact fun e => h1 e.symm),
    List.find?_cons_of_neg (by
      show ¬ (("Y" : String) == n) = true
      rw [beq_iff_eq]
      exact fun e => h2 e.symm), List.find?_nil]

/-- **A short table's weights.** -/
theorem tok_short {lt : ℕ} {z : Array E} (hz : z.size = lt) {j : ℕ} (hj : j < 2 ^ lt) :
    Reading.gl.val ((eqTab z).getD j zeroE) =
      ∑ t ∈ range (2 ^ lt), Blocks.eqN lt 0 (pt Reading.gl z) t *
        Reading.gl.val ((eqTab (cornerAt lt t)).getD j zeroE) := by
  have hin : ∀ t ∈ range (2 ^ lt), Blocks.eqN lt 0 (pt Reading.gl z) t *
      Reading.gl.val ((eqTab (cornerAt lt t)).getD j zeroE) =
      if t = j then Blocks.eqN lt 0 (pt Reading.gl z) t else 0 := by
    intro t ht
    rw [eqTab_cornerAt (mem_range.mp ht) hj]
    by_cases c : t = j
    · rw [if_pos c, if_pos c.symm, mul_one]
    · rw [if_neg c, if_neg fun e => c e.symm, mul_zero]
  rw [sum_congr rfl hin, Finset.sum_ite_eq', if_pos (mem_range.mpr hj),
    eqTab_value Reading.gl z j (by rw [hz]; exact hj), hz]

/-- **A long table's weights.** -/
theorem tok_long {ls lt : ℕ} {zlow z : Array E} (hlow : zlow.size = ls) (hz : z.size = lt) {j : ℕ}
    (hj : j < 2 ^ (ls + lt)) :
    Reading.gl.val ((longPhi (longPoint zlow z) ls lt).getD j zeroE) =
      ∑ t ∈ range (2 ^ lt), Blocks.eqN lt 0 (pt Reading.gl z) t *
        Reading.gl.val ((longPhi (longPoint zlow (cornerAt lt t)) ls lt).getD j zeroE) := by
  have hpos : 0 < 2 ^ lt := Nat.two_pow_pos lt
  have hr : j / 2 ^ lt < 2 ^ ls := by
    rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add]
    exact hj
  have hi : j % 2 ^ lt < 2 ^ lt := Nat.mod_lt _ hpos
  have ej : j = j / 2 ^ lt * 2 ^ lt + j % 2 ^ lt := (Nat.div_add_mod' j (2 ^ lt)).symm
  have val : ∀ x : Array E, x.size = lt →
      Reading.gl.val ((longPhi (longPoint zlow x) ls lt).getD j zeroE) =
        Blocks.eqN ls 0 (pt Reading.gl zlow) (j / 2 ^ lt) *
          Blocks.eqN lt 0 (pt Reading.gl x) (j % 2 ^ lt) := by
    intro x hx
    have hs : (longPoint zlow x).size = ls + lt := by
      unfold longPoint
      rw [Array.size_append, hlow, hx]
    have e := longPhi_value Reading.gl hs hr hi
    rw [← ej] at e
    rw [e]
    congr 1
    · refine eqN_congr' ls 0 (fun s hs' => ?_) _
      unfold longPoint
      rw [Rows.pt_append, if_pos (by rw [hlow]; omega)]
    · refine eqN_congr' lt 0 (fun s _ => ?_) _
      show pt Reading.gl (longPoint zlow x) (ls + (0 + s)) = _
      unfold longPoint
      rw [Rows.pt_append, if_neg (by rw [hlow]; omega), hlow, Nat.add_sub_cancel_left]
  rw [val z hz]
  have hin : ∀ t ∈ range (2 ^ lt), Blocks.eqN lt 0 (pt Reading.gl z) t *
      Reading.gl.val ((longPhi (longPoint zlow (cornerAt lt t)) ls lt).getD j zeroE) =
      if t = j % 2 ^ lt then Blocks.eqN ls 0 (pt Reading.gl zlow) (j / 2 ^ lt) *
        Blocks.eqN lt 0 (pt Reading.gl z) t else 0 := by
    intro t ht
    rw [val _ (cornerAt_size lt t),
      eqN_bool lt 0 _ (mem_range.mp ht) hi fun s hs' => cornerAt_pt lt t s hs']
    by_cases c : t = j % 2 ^ lt
    · rw [if_pos c, if_pos c.symm]
      ring
    · rw [if_neg c, if_neg fun e => c e.symm]
      ring
  rw [sum_congr rfl hin, Finset.sum_ite_eq', if_pos (mem_range.mpr hi)]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.cornerAt_size
#print axioms OnBytes.Road.K4.C.cornerAt_pt
#print axioms OnBytes.Road.K4.C.eqTab_cornerAt
#print axioms OnBytes.Road.K4.C.find_rt
#print axioms OnBytes.Road.K4.C.find_Y
#print axioms OnBytes.Road.K4.C.find_none
#print axioms OnBytes.Road.K4.C.tok_short
#print axioms OnBytes.Road.K4.C.tok_long
