-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyTreeMaps.lean: the maps of a product tree meet what a level asks, for every table.

OnBytes/Slice/KeyLevel.lean proves the soundness of a level of a product tree under conditions on
the level's map and the next level's (LevelMaps). This file shows that the conditions hold, at the
order of rounds from the highest variable down, for the multilinear extensions of any two tables of
which the first is, entry by entry, the product of the two halves of the second. No hypothesis is
left but that and the number of variables.

A table is a function on lists; only its values at lists of 0 and 1 are read. ext n t is the
multilinear extension of the table t in n variables, by recursion on the first coordinate. In that
recursion the first coordinate is the variable that the sumcheck binds first, the highest. A level's
map takes its point by variable, the lowest first, so it is the extension at the reversed point
(treeMap).

Main definitions: PscF.ext, treeMap.

Main theorems: PscF.order_map_default, PscF.byVariable_default (at the order from the highest
variable down, the weights' points and the point put back by variable are reversed lists),
PscF.ml_ext, PscF.cubeEq_ext, levelMaps_default, levelMaps_tables, tree_tables_sem.

Not claimed. That a given verifier's tree has these tables. Nothing on another order of rounds.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyLevel

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

namespace PscF

/-! ## The order from the highest variable down -/

/-- The order has n members. -/
theorem defaultOrder_length (n : ℕ) : (defaultOrder n).length = n := by
  unfold defaultOrder
  rw [List.length_reverse, List.length_range]

/-- The coordinates of a point, taken in the order from the highest variable down, are the reversed
point. -/
theorem order_map_default (l : List GE) (n : ℕ) (h : l.length = n) :
    (defaultOrder n).map (fun t => l.getD t 0) = l.reverse := by
  unfold defaultOrder
  rw [List.map_reverse]
  congr 1
  refine List.ext_getElem (by rw [List.length_map, List.length_range, h]) fun i _ h2 => ?_
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]

/-- Where a variable's coordinate stands in a point given round by round. -/
theorem lookup_default : ∀ (p : List GE) (t : ℕ), t < p.length →
    ((List.range p.length).reverse.zip p).lookup t = p[p.length - 1 - t]?
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: p, t, h => by
    rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.zip_cons_cons, List.lookup_cons]
    by_cases ht : t = p.length
    · subst ht
      simp
    · have hlt : t < p.length := by
        rw [List.length_cons] at h
        omega
      rw [show (t == p.length) = false from beq_false_of_ne ht, lookup_default p t hlt,
        show p.length + 1 - 1 - t = (p.length - 1 - t) + 1 by omega, List.getElem?_cons_succ]

/-- A point given round by round, from the highest variable down, and put back by variable, is the
reversed point. -/
theorem byVariable_default (p : List GE) (n : ℕ) (h : p.length = n) :
    byVariable p (defaultOrder n) = p.reverse := by
  subst h
  unfold byVariable defaultOrder
  refine List.ext_getElem (by rw [List.length_map, List.length_range, List.length_reverse])
    fun i h1 h2 => ?_
  have hi : i < p.length := by rwa [List.length_reverse] at h2
  rw [List.getElem_map, List.getElem_range, lookup_default p i hi, List.getElem_reverse,
    List.getElem?_eq_getElem (by omega), Option.getD_some]

/-! ## The multilinear extension of a table -/

/-- The multilinear extension of the table t in n variables. A missing coordinate counts as
0. -/
def ext : ℕ → (List GE → GE) → List GE → GE
  | 0, t, _ => t []
  | n + 1, t, [] => ext n (fun q => t (0 :: q)) []
  | n + 1, t, z :: zs =>
    (1 - z) * ext n (fun q => t (0 :: q)) zs + z * ext n (fun q => t (1 :: q)) zs

/-- The extension with its first coordinate at 0 is the extension of the first half. -/
theorem ext_zero (n : ℕ) (t : List GE → GE) :
    (fun q => ext (n + 1) t (0 :: q)) = ext n fun q => t (0 :: q) := by
  funext q
  show (1 - 0) * ext n (fun q => t (0 :: q)) q + 0 * ext n (fun q => t (1 :: q)) q = _
  ring

/-- The extension with its first coordinate at 1 is the extension of the second half. -/
theorem ext_one (n : ℕ) (t : List GE → GE) :
    (fun q => ext (n + 1) t (1 :: q)) = ext n fun q => t (1 :: q) := by
  funext q
  show (1 - 1) * ext n (fun q => t (0 :: q)) q + 1 * ext n (fun q => t (1 :: q)) q = _
  ring

/-- The extension is affine in its first coordinate, at lists of any length. -/
theorem ext_line (n : ℕ) (t : List GE → GE) (x : GE) (q : List GE) :
    ext (n + 1) t (x :: q) = (1 - x) * ext (n + 1) t (0 :: q) + x * ext (n + 1) t (1 :: q) := by
  rw [congrFun (ext_zero n t) q, congrFun (ext_one n t) q]
  rfl

/-- A combination of two multilinear maps is multilinear. -/
theorem ML.lin (a b : GE) : ∀ {n : ℕ} {F G : List GE → GE}, ML n F → ML n G →
    ML n fun q => a * F q + b * G q
  | 0, _, _, _, _ => trivial
  | _ + 1, _, _, hF, hG =>
    ⟨fun x q hq => by
        beta_reduce
        rw [hF.1 x q hq, hG.1 x q hq]
        ring,
      fun x => ML.lin a b (hF.2 x) (hG.2 x)⟩

/-- The extension is multilinear. -/
theorem ml_ext : ∀ (n : ℕ) (t : List GE → GE), ML n (ext n t)
  | 0, _ => trivial
  | n + 1, t => ⟨fun x q _ => ext_line n t x q, fun x => ML.lin (1 - x) x (ml_ext n _) (ml_ext n _)⟩

/-- If a table is the product of two tables on the cube, so is its extension of theirs. -/
theorem cubeEq_ext : ∀ (n : ℕ) (t f0 f1 : List GE → GE), CubeEq n t f0 f1 →
    CubeEq n (ext n t) (ext n f0) (ext n f1)
  | 0, _, _, _, h => h
  | n + 1, t, f0, f1, h => by
    show CubeEq n (fun q => ext (n + 1) t (0 :: q)) (fun q => ext (n + 1) f0 (0 :: q))
        (fun q => ext (n + 1) f1 (0 :: q)) ∧
      CubeEq n (fun q => ext (n + 1) t (1 :: q)) (fun q => ext (n + 1) f0 (1 :: q))
        fun q => ext (n + 1) f1 (1 :: q)
    rw [ext_zero, ext_zero, ext_zero, ext_one, ext_one, ext_one]
    exact ⟨cubeEq_ext n _ _ _ h.1, cubeEq_ext n _ _ _ h.2⟩

end PscF

/-! ## What a level asks, at the order from the highest variable down -/

/-- What a level asks of its two maps, from facts on the maps round by round. R, R': the level's
map and the next level's, as functions of the point with the highest variable first. -/
theorem levelMaps_default (n : ℕ) (R R' : List GE → GE) (hR : PscF.ML n R)
    (hR' : PscF.ML (n + 1) R')
    (hline : ∀ x q, R' (x :: q) = (1 - x) * R' (0 :: q) + x * R' (1 :: q))
    (hc : PscF.CubeEq n R (fun q => R' (0 :: q)) fun q => R' (1 :: q)) :
    LevelMaps (PscF.defaultOrder n) (fun z => R z.reverse) fun z => R' z.reverse := by
  have hl := PscF.defaultOrder_length n
  have hb : ∀ (x : GE) (q : List GE), q.length = n →
      R' (x :: q) = R' (PscF.byVariable q (PscF.defaultOrder n) ++ [x]).reverse := by
    intro x q hq
    rw [PscF.byVariable_default q n hq, List.reverse_append, List.reverse_reverse]
    rfl
  refine ⟨?_, ?_, fun z hz => ?_, fun q ρ => ?_⟩
  · rw [hl]
    exact PscF.ML.congr (hb 0) (hR'.2 0)
  · rw [hl]
    exact PscF.ML.congr (hb 1) (hR'.2 1)
  · rw [hl] at hz
    have hzl : z.reverse.length = n := by rw [List.length_reverse, hz]
    rw [PscF.order_map_default z n hz,
      ← PscF.bil_congr z.reverse (fun q hq => hb 0 q (hq.trans hzl))
        fun q hq => hb 1 q (hq.trans hzl)]
    exact PscF.ml_eq_bil z.reverse R _ _ (by rwa [hzl]) (by rwa [hzl])
  · simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
    exact hline ρ q.reverse

/-- The map of a level with n variables and the table t: the extension, at the point by
variable. -/
def treeMap (n : ℕ) (t : List GE → GE) (z : List GE) : GE := PscF.ext n t z.reverse

/-- The maps of two levels meet what a level asks, for every pair of tables of which the first
is, on the cube, the product of the two halves of the second. -/
theorem levelMaps_tables (n : ℕ) (t t' : List GE → GE)
    (h : PscF.CubeEq n t (fun q => t' (0 :: q)) fun q => t' (1 :: q)) :
    LevelMaps (PscF.defaultOrder n) (treeMap n t) (treeMap (n + 1) t') :=
  levelMaps_default n (PscF.ext n t) (PscF.ext (n + 1) t') (PscF.ml_ext n t)
    (PscF.ml_ext (n + 1) t') (PscF.ext_line n t') (by
      rw [PscF.ext_zero, PscF.ext_one]
      exact PscF.cubeEq_ext n _ _ _ h)

/-- Soundness of a tree, for every family of tables of which each is, on the cube, the product
of the two halves of the next. The top level has n₀ variables, and each level binds its variables
from the highest down. -/
theorem tree_tables_sem {dEps dRound dY dVals dLine : PQ.RD} (n₀ k oM oK : ℕ) (keys : ℕ → Bool)
    (W : PscF.World) (t : ℕ → List GE → GE)
    (h : ∀ i, i < k →
      PscF.CubeEq (n₀ + i) (t i) (fun q => t (i + 1) (0 :: q)) fun q => t (i + 1) (1 :: q))
    (hE : OneEl dEps) (hR : OneEl dRound) (hY : OneEl dY) (hL : OneEl dLine) :
    (treeStep dEps dRound dY dVals dLine (fun i => PscF.defaultOrder (n₀ + i)) oM oK keys k).Sem
      (LvSt.Good W (treeMap n₀ (t 0))) (LvSt.Good W (treeMap (n₀ + k) (t k))) :=
  tree_sem _ oM oK keys k W (fun i => treeMap (n₀ + i) (t i))
    (fun i hi => levelMaps_tables (n₀ + i) (t i) (t (i + 1)) (h i hi)) hE hR hY hL

end OnBytes.Slice
