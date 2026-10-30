-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsSpecPoints.lean: the honest side of the kind "lookup" (K3): the
one translation of points (`byBit`, Honest/K3/JobsSpec.lean) carries the verifier's own ways with a
point to the specification's. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md ("points", "specification"). In this file: the verifier's text keeps a
point as an array, the highest bit first; the specification (Johnson/HonestTrace/LookDefs.lean,
after Cb/Pv/Lookup/Out/TwV.lean) keeps it as a list, coordinate i with bit i. `byBit` reverses the
array and reads each element in the library's field.

What is shown.
  1 `up_down`, `ups_downs`, `byBit_length`, `byBit_getD`: the small facts.
  2 `byBit_stepDown`: the step down lays the line's sample in front: in the list it comes last.
  3 `byBit_reverse`: samples that the verifier reads in reverse are the list as sampled.
  4 `pointsOf_map`, `inRounds_down`, `points_level`, `points_leaves`, `points_bits`: the points at
    which the verifier's calls sum their variables, by round, are `TwV.inRounds` of the order and
    the translated point.
  5 `byBit_layBack` (helper: `layBack_loop`): the point that a level hands back, translated, is
    `TwV.byVar` of the order and the challenges.
  6 `keyJob_zs`, `tabJob_zs`: so the specification's jobs for the levels sum at the verifier's
    points.
  7 `specJobsF_places`: the filling at a proof file's lookup does not depend on the numbers lm and
    jLK, which say where hidden values lie.

Hypotheses that remain.
  `hz`: (in `points_level`, `points_leaves`, `keyJob_zs`, `tabJob_zs`) the point has as many
    coordinates as the stage has variables. `ho`: (in `points_level`, `keyJob_zs`, `tabJob_zs`)
    every member of the order lies below the number of variables.
  `h`: in `byBit_getD`: b lies within the array; in `byBit_layBack`: the verifier's own test on the
    order accepts. `hc`: (in `byBit_layBack`) there are m challenges at least. `ht`: (in
    `layBack_loop`) t < m; there, without a name, in front of arrows: the array has m entries; every
    member of the order lies below m; no member stands twice.

Limits. These are facts on lists and arrays. Nothing here says what a job sums, and nothing is
played or heard. `byBit_layBack` assumes the verifier's own test on the order
(`First.ProdV.orderOk`); the challenges may be more than the variables (a further variable's comes
last and is not read).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsSpec
import Johnson.Desc.First.ProdV.LevelKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE oneE)
open OnBytes.HonestTrace.Look (Data keyJob tabJob leavesJob bitsJob)
open VerifiableInference.Desc.First.ProdV (layBack levelVars orderOk)
open VerifiableInference.Desc.K3 (leafVars bitsCall)

/-! ## 1 The small facts -/

/-- Down and up again changes nothing. -/
theorem up_down (x : KE) : up (down x) = x := by
  unfold up down
  rw [OnBytes.Slice.readE_ofTriple, OnBytes.Slice.toE_ofE]

/-- The same on lists. -/
theorem ups_downs (l : List KE) : ups (downs l) = l := by
  unfold ups downs
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun x _ => up_down x

/-- A translated point has as many coordinates as the array has places. -/
theorem byBit_length (z : Array E) : (byBit z).length = z.size := by
  simp [byBit, ups]

/-- **Coordinate b of the translated point is the array's place size - 1 - b.** -/
theorem byBit_getD (z : Array E) (b : Nat) (h : b < z.size) :
    (byBit z).getD b 0 = up (z.getD (z.size - 1 - b) zeroE) := by
  have h1 : b < (byBit z).length := by rw [byBit_length]; exact h
  rw [List.getD_eq_getElem _ _ h1]
  simp only [byBit, ups, List.getElem_map, List.getElem_reverse, Array.length_toList]
  congr 1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
  simp

/-! ## 2 The step down -/

/-- **The step down** (`First.ProdV.stepDown`) lays the line's sample in front of the array, as the
coordinate of the new highest bit: in the list it comes last. -/
theorem byBit_stepDown (xi : E) (r : Array E) : byBit (#[xi] ++ r) = byBit r ++ [up xi] := by
  simp [byBit, ups]

/-! ## 3 Samples read in reverse -/

/-- **Samples that the verifier's text reads in reverse** (JOIN's, ZERO's) are, translated, the list
as it was sampled: bit 0's coordinate first. -/
theorem byBit_reverse (ds : Array E) : byBit ds.reverse = ups ds.toList := by
  simp [byBit, ups]

/-! ## 4 The points of the verifier's calls -/

/-- The points of a list of variables that are all summed at a point. -/
theorem pointsOf_map {α : Type} (l : List α) (g : α → E) (d : α → Nat) :
    pointsOf (l.map fun b => .point (g b) (d b)) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    unfold pointsOf at ih ⊢
    simp only [List.map_cons, List.filterMap_cons]
    rw [ih]

/-- **A level's variables** (`First.ProdV.levelVars`) are summed, round by round, at the coordinates
that the specification reads off the translated point. -/
theorem points_level (m : Nat) (z : Array E) (o : List Nat) (hz : z.size = m)
    (ho : ∀ b ∈ o, b < m) : ups (pointsOf (levelVars m z o)) = TwV.inRounds o (byBit z) := by
  unfold levelVars
  rw [pointsOf_map]
  unfold TwV.inRounds ups
  rw [List.map_map]
  refine List.map_congr_left fun b hb => ?_
  rw [byBit_getD z b (by rw [hz]; exact ho b hb), hz]
  rfl

/-- The translated point, read in the order that counts down, is the array as it lies. -/
theorem inRounds_down (z : Array E) :
    TwV.inRounds (OnBytes.Model.orderDefault z.size) (byBit z) = ups z.toList := by
  rw [← countDown_eq]
  unfold TwV.inRounds ups FoNums.placeOf
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hj : j < z.size := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Function.comp]
    rw [byBit_getD z _ (by omega)]
    have e : z.size - 1 - (z.size - 1 - j) = j := by omega
    rw [e, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp

/-- **The leaves' variables** (`K3.leafVars`): variable j at the array's place j: the order that
counts down. -/
theorem points_leaves (f : LFace) (z : Array E) (hz : z.size = f.mu + f.d) :
    ups (pointsOf (leafVars f z)) =
      TwV.inRounds (OnBytes.Model.orderDefault (f.mu + f.d)) (byBit z) := by
  rw [← hz, inRounds_down]
  unfold leafVars
  rw [pointsOf_map, ← hz]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hj : j < z.size := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp

/-- **The bits' variables** (`K3.bitsCall`): likewise. -/
theorem points_bits (z : Array E) :
    ups (pointsOf (bitsCall z.toList).vs) =
      TwV.inRounds (OnBytes.Model.orderDefault z.size) (byBit z) := by
  rw [inRounds_down]
  unfold bitsCall
  show ups (pointsOf (z.toList.map fun x => .point x 3)) = _
  rw [pointsOf_map, List.map_id']

/-! ## 5 The point that a level hands back -/

/-- What the loop of `layBack` leaves at the place of bit t. -/
theorem layBack_loop (m t : Nat) (ht : t < m) : ∀ (o : List Nat) (cs : List E) (r : Array E),
    r.size = m → (∀ b ∈ o, b < m) → o.Nodup →
    ((o.zip cs).foldl (fun (r : Array E) x => r.set! (m - 1 - x.1) x.2) r).getD (m - 1 - t) zeroE =
      if o.idxOf t < min o.length cs.length then cs.getD (o.idxOf t) zeroE
      else r.getD (m - 1 - t) zeroE
  | [], cs, r, _, _, _ => by simp
  | b :: o, [], r, _, _, _ => by simp
  | b :: o, c :: cs, r, hr, hb, hn => by
    have hbm : b < m := hb b (by simp)
    have hn' := List.nodup_cons.1 hn
    have ih := layBack_loop m t ht o cs (r.set! (m - 1 - b) c)
      (by rw [VerifiableInference.Desc.First.ProdV.size_set]; exact hr)
      (fun x hx => hb x (by simp [hx])) hn'.2
    simp only [List.zip_cons_cons, List.foldl_cons]
    rw [ih]
    by_cases htb : b = t
    · subst htb
      have e1 : o.idxOf b = o.length := List.idxOf_eq_length_iff.2 hn'.1
      have e2 : (b :: o).idxOf b = 0 := by simp
      rw [e1, e2, if_neg (by omega), if_pos (by simp)]
      simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, hr]
      omega
    · have e2 : (b :: o).idxOf t = o.idxOf t + 1 := by
        rw [List.idxOf_cons_ne _ htb]
      have e3 : (r.set! (m - 1 - b) c).getD (m - 1 - t) zeroE = r.getD (m - 1 - t) zeroE := by
        have : m - 1 - b ≠ m - 1 - t := by omega
        simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, this]
      rw [e2, e3]
      simp only [List.length_cons, List.getD_cons_succ]
      by_cases hlt : o.idxOf t < min o.length cs.length
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- **The point that a level hands back** (`First.ProdV.layBack`), translated, is the
specification's point by coordinate (`TwV.byVar`): coordinate c is the challenge of the round that
binds bit c. -/
theorem byBit_layBack (m : Nat) (o : List Nat) (cs : List E) (h : orderOk m o = true)
    (hc : m ≤ cs.length) : byBit (layBack m o cs) = TwV.byVar o (ups cs) := by
  obtain ⟨hl, hlt, hcnt⟩ := VerifiableInference.Desc.First.ProdV.orderOk_facts h
  have hn : o.Nodup := List.nodup_iff_count_le_one.mpr fun a => by
    by_cases ha : a ∈ o
    · rw [hcnt a (hlt a ha)]
    · rw [List.count_eq_zero_of_not_mem ha]
      omega
  have hs := VerifiableInference.Desc.First.ProdV.layBack_size m o cs
  apply List.ext_getElem
  · rw [byBit_length, hs]
    simp [TwV.byVar, hl]
  · intro t h1 h2
    have ht : t < m := by rw [byBit_length, hs] at h1; exact h1
    have hmem : t ∈ o := List.count_pos_iff.1 (by rw [hcnt t ht]; omega)
    have hidx : o.idxOf t < o.length := List.idxOf_lt_length_iff.2 hmem
    rw [← List.getD_eq_getElem _ 0 h1, byBit_getD _ _ (by rw [hs]; exact ht), hs]
    unfold layBack
    rw [layBack_loop m t ht o cs _ (by simp) hlt hn, if_pos (by omega)]
    simp only [TwV.byVar, List.getElem_map, List.getElem_range, ups]
    rw [← OnBytes.Slice.readE_zero, List.getD_map]

/-! ## 6 The specification's jobs sum at the verifier's points -/

variable {P : Type}

/-- The key tree's level with m variables. -/
theorem keyJob_zs (D : Data P KE) (m : Nat) (z : Array E) (hz : z.size = m)
    (ho : ∀ b ∈ D.N.oK m, b < m) :
    (keyJob D m (byBit z)).zs = ups (pointsOf (levelVars m z (D.N.oK m))) :=
  (points_level m z _ hz ho).symm

/-- The table side's level number l. -/
theorem tabJob_zs (D : Data P KE) (l : Nat) (z : Array E) (hz : z.size = D.N.w + l)
    (ho : ∀ b ∈ D.N.oT l, b < D.N.w + l) :
    (tabJob D l (byBit z)).zs = ups (pointsOf (levelVars (D.N.w + l) z (D.N.oT l))) :=
  (points_level _ z _ hz ho).symm

/-! ## 7 What the filling does not read -/

/-- **The filling does not depend on lm or jLK**: the filling at a proof file's lookup is the same
at any two pairs. Of what a part sends nothing is said here. -/
theorem specJobsF_places (h : OnBytes.Model.Forest.Shape) (lm jLK lm' jLK' : Nat) :
    specJobsF h lm jLK = specJobsF h lm' jLK' := by
  unfold specJobsF specJobs
  congr 1

#print axioms ProofFile.Honest.K3.specJobsF_places
#print axioms ProofFile.Honest.K3.up_down
#print axioms ProofFile.Honest.K3.ups_downs
#print axioms ProofFile.Honest.K3.byBit_length
#print axioms ProofFile.Honest.K3.byBit_getD
#print axioms ProofFile.Honest.K3.byBit_stepDown
#print axioms ProofFile.Honest.K3.byBit_reverse
#print axioms ProofFile.Honest.K3.pointsOf_map
#print axioms ProofFile.Honest.K3.inRounds_down
#print axioms ProofFile.Honest.K3.points_level
#print axioms ProofFile.Honest.K3.points_leaves
#print axioms ProofFile.Honest.K3.points_bits
#print axioms ProofFile.Honest.K3.layBack_loop
#print axioms ProofFile.Honest.K3.byBit_layBack
#print axioms ProofFile.Honest.K3.keyJob_zs
#print axioms ProofFile.Honest.K3.tabJob_zs

end ProofFile.Honest.K3
