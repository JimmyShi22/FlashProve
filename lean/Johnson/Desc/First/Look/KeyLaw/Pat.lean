-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Pat.lean: bookkeeping on lists: K3Key's pattern of the hidden values
(fromKeys) and the lookup's shape (shapeG), cut stretch by stretch; K3Key's table of homes as a list
of the two messages' entries.

Main names:
  levelsPat_keys, levelsPat_table, fromKeys_cut: the pattern.
  levelsShape_eq, degs_eq, shape_cut: the shape.
  homesFrom_hs: K3Key's homes out of two lists that are long enough are the pattern's entries.

Limits. Lists alone.

-/
import Johnson.Desc.First.Look.KeyLaw.Open

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (RoundName)

/-! ## The pattern -/

theorem levelsPat_keys : ∀ (n l : ℕ), levelsPat true 0 n l =
    (List.range' l n).flatMap fun k =>
      if k + 1 == l + n then own (2 * k + 3) ++ [true, true] else own (2 * k + 5)
  | 0, _ => rfl
  | n + 1, l => by
    rw [List.range'_succ, List.flatMap_cons]
    show (if (true && n == 0) = true then own (1 + 2 * (0 + l) + 2 + 2 - 2) ++ [true, true]
      else own (1 + 2 * (0 + l) + 2 + 2)) ++ levelsPat true 0 n (l + 1) = _
    rw [levelsPat_keys n (l + 1), show l + 1 + n = l + (n + 1) by omega]
    congr 1
    by_cases h : n = 0
    · subst h
      simp
      congr 1
      omega
    · have h1 : (true && n == 0) = false := by simpa using h
      have h2 : (l + 1 == l + (n + 1)) = false := by simp; omega
      rw [h1, h2]
      simp
      congr 1
      omega

theorem levelsPat_table (more : ℕ) : ∀ (n l : ℕ), levelsPat false more n l =
    own (((List.range' l n).map fun i => 2 * (more + i) + 5).sum)
  | 0, _ => rfl
  | n + 1, l => by
    rw [List.range'_succ, List.map_cons, List.sum_cons, own_add, ← levelsPat_table more n (l + 1)]
    show own (1 + 2 * (more + l) + 2 + 2) ++ _ = _
    congr 2
    omega

theorem degs_sum (mu d : ℕ) :
    (((List.range (mu + d)).map fun j => (if j < d then 2 else 1 : ℕ))).sum = 2 * d + mu := by
  induction mu with
  | zero =>
    rw [Nat.zero_add]
    have : ((List.range d).map fun j => (if j < d then 2 else 1 : ℕ)) =
        (List.range d).map fun _ => 2 :=
      List.map_congr_left fun j hj => by rw [if_pos (List.mem_range.1 hj)]
    rw [this, sum_const, List.length_range]
    omega
  | succ mu ih =>
    rw [show mu + 1 + d = (mu + d) + 1 by omega, List.range_succ, List.map_append, List.sum_append,
      ih]
    simp
    omega

theorem degs_eq (mu d : ℕ) :
    ((List.range (mu + d)).map fun j => (if j < d then 2 else 1 : ℕ)) =
      List.replicate d 2 ++ List.replicate mu 1 := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    by_cases h : i < d
    · rw [if_pos h, List.getElem_append_left (by simpa using h)]
      simp
    · rw [if_neg h, List.getElem_append_right (by simpa using h)]
      simp

/-- **K3Key's pattern, cut stretch by stretch.** -/
theorem fromKeys_cut (f : Face) : fromKeys f =
    own (7 + 6 * (f.planes - 2)) ++ (own (5 * (f.parts.length - 1)) ++ (keysPat f.parts ++
      (levelsPat false f.mu f.d 0 ++ (own (1 + (2 * f.d + f.mu)) ++
        (own (1 + 2 * (f.mu + f.d) + 2 + 1) ++ []))))) := by
  unfold fromKeys keysPat
  rw [levelsPat_table, ← List.range_eq_range', own_add, own_add, own_add, List.append_nil]
  have e : (f.parts.flatMap fun v => (List.range v).flatMap fun k =>
      if k + 1 == v then own (2 * k + 3) ++ [true, true] else own (2 * k + 5)) =
      f.parts.flatMap fun v => levelsPat true 0 v 0 := by
    refine List.flatMap_congr fun v _ => ?_
    rw [levelsPat_keys, ← List.range_eq_range', Nat.zero_add]
  rw [e, show 1 + f.mu + 2 * f.d = 1 + (2 * f.d + f.mu) by omega]
  simp only [own_add, List.append_assoc]

/-! ## The shape -/

theorem levelsShape_eq (more : ℕ) : ∀ (n l : ℕ), levelsShape more n l =
    (List.range' l n).flatMap fun i =>
      pscShape (List.replicate (more + i) 2) (some (2, 2)) ++ [(RoundName.line.name, 0, 1, 0)]
  | 0, _ => rfl
  | n + 1, l => by
    rw [List.range'_succ, List.flatMap_cons, ← levelsShape_eq more n (l + 1)]
    rfl

theorem levelsShape_tree (more n : ℕ) : levelsShape more n 0 = treeShape more n := by
  rw [levelsShape_eq, ← List.range_eq_range']
  rfl

/-- **The lookup's shape, cut stretch by stretch.** -/
theorem shape_cut (f : Face) : shapeG f =
    [(RoundName.lkp.name, 0, 1, 0)] ++ ((pscShape [] (some (3, 3)) ++
        (List.range (f.planes - 2)).flatMap fun _ => pscShape [] (some (3, 2))) ++
      (((List.range (f.parts.length - 1)).flatMap fun _ => pscShape [] (some (2, 2))) ++
        ([(RoundName.lkpPlanes.name, 0, f.mu, 0)] ++ (keysShape f.parts ++
          (levelsShape f.mu f.d 0 ++
            (pscShape ((List.range (f.mu + f.d)).map fun j => (if j < f.d then 2 else 1 : ℕ)) none
                ++
              ([(RoundName.zero.name, 0, f.mu + f.d, 0)] ++
                pscShape (List.replicate (f.mu + f.d) 2) (some (2, 1))))))))) := by
  unfold shapeG keysShape
  rw [levelsShape_tree, degs_eq]
  have e : (f.parts.flatMap fun v => levelsShape 0 v 0) = f.parts.flatMap fun v => treeShape 0 v :=
    List.flatMap_congr fun v _ => levelsShape_tree 0 v
  rw [e]
  simp only [List.append_assoc]

/-! ## The table of homes -/

/-- K3Key's homes out of two lists are the pattern's entries, where the lists are long enough. -/
theorem homesFrom_hs (o k : ℕ → Slot) : ∀ (pat : List Bool) (a b N : ℕ), a + pat.length ≤ N →
    b + pat.length ≤ N →
    homesFrom pat (((List.range N).map o).drop a) (((List.range N).map k).drop b) = hs o k pat a b
  | [], _, _, _, _, _ => by cases h : (((List.range _).map o).drop _) <;> rfl
  | false :: bs, a, b, N, ha, hb => by
    have ha' : a < N := by simp at ha; omega
    have e : ((List.range N).map o).drop a = o a :: ((List.range N).map o).drop (a + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using ha')]
      simp
    rw [e]
    show o a :: homesFrom bs _ _ = o a :: hs o k bs (a + 1) b
    rw [homesFrom_hs o k bs (a + 1) b N (by simp at ha; omega) (by simp at hb; omega)]
  | true :: bs, a, b, N, ha, hb => by
    have hb' : b < N := by simp at hb; omega
    have e : ((List.range N).map k).drop b = k b :: ((List.range N).map k).drop (b + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hb')]
      simp
    rw [e]
    have : homesFrom (true :: bs) (((List.range N).map o).drop a)
        (k b :: ((List.range N).map k).drop (b + 1)) =
        k b :: homesFrom bs (((List.range N).map o).drop a) (((List.range N).map k).drop (b + 1)) :=
            by
      cases h : (((List.range N).map o).drop a) <;> rfl
    rw [this, homesFrom_hs o k bs a (b + 1) N (by simp at ha; omega) (by simp at hb; omega)]
    rfl

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.fromKeys_cut
#print axioms VerifiableInference.Desc.K3.KeyLaw.shape_cut
#print axioms VerifiableInference.Desc.K3.KeyLaw.homesFrom_hs
