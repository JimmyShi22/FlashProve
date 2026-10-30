-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/CubeKitB.lean: CONDITIONAL. Six definitions, and statements with their
proofs.

What is here. Tools for the laws on a sum over a cube: the program's tables, weights and loops, read
in a commutative ring.

  `rdT`, `rdM`   a table, and one of some tables, as a function on the numbers; 0 beyond the end
  `sumT`   the summand on such functions
  `weights_sum`, `eqTab_sum`   the sum under `weightsOf`, and under the library's equality table
  `foldRange`, `fold3`, `fold3_read`   the loops over the numbers below N
  `termsAt_rd`, `lineAt_rd`   the summand at an entry; between two entries, at X
  `bindAt_size`, `bindAt_read`, `rdM_bind`   a table with one variable set
  Beside these, smaller steps: `rdT_empty`, `getD_mapL`, `getD_mapA`, `stepW` (a definition),
  `stepArr_toList`, `weightsOf_toList`, `stepW_map`, `foldW_map`, `stepL_map`, `foldL_map`,
  `tab_sum`, `fold3_succ`, `lineStep` (a definition), `lineAt_eq`, `ofFnE_getD`.

Limits. Each law is an equation between readings, but for `stepArr_toList`, `weightsOf_toList`,
`fold3_succ`, `lineAt_eq` and `ofFnE_getD`, which are on words, and `bindAt_size`, which counts.
Hypotheses: the table reads as the table made of the pairs (`tab_sum`); i below half the table's
size (`bindAt_read`); each table has 2 ^ (L + 1) entries and i < 2 ^ L (`rdM_bind`); i < n
(`ofFnE_getD`).

Kin. `getD_mapL` IS IN THE LIBRARY AT THE SAME READINGS, the written statement the same
but for its binders: `getD_read` (OnBytes/Tie/Pv/Lookup/Forest/FoTieInv.lean);
this file does not build on that one.
The library's equality table entry by entry: `eqTab_value`
(Johnson/Road/FormsKeysEq.lean, on which this file builds); `eqTab_sum` here is the sum under that
table, in the terms of `sumOver`. `foldRange` IS IN THE LIBRARY IN THREE OTHER SPELLINGS, at the
same `addE`: `val_fold` (Johnson/HonestTrace/Reads.lean: from 0), `read_sum`
(OnBytes/Tie/Pv/Att/Flat.lean: the sum over Fin n, at readings into a field), `foldAdd_read`
(Johnson/Desc/K11/Honest/Law/Tables.lean: a loop over any list, against the sum of a list); this
file builds on none of them.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Law.CubeKitA
import Johnson.Road.FormsKeysEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading eqTab)
open OnBytes.Road (stepL eqTab_toList getD_map_lt getD_ge)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## 1 Tables as functions -/

/-- A table as a function on the numbers; 0 beyond its end. -/
def rdT (t : Tab) : ℕ → K := fun i => ρ.val (t.getD i zeroE)

/-- One of some tables as a function; the zero function where there is no such table. -/
def rdM (ms : Array Tab) (a : ℕ) : ℕ → K := rdT ρ (ms.getD a #[])

/-- The summand on tables that are given as functions. -/
def sumT (pairs : List (E × Nat × Nat)) (A : ℕ → ℕ → K) (i : ℕ) : K :=
  (pairs.map fun x => ρ.val x.1 * (A x.2.1 i * A x.2.2 i)).sum

theorem rdT_empty (i : ℕ) : rdT ρ #[] i = 0 := by
  unfold rdT
  rw [getD_ge #[] (Nat.zero_le i) zeroE, ρ.zero]

theorem getD_mapL : ∀ (l : List E) (i : ℕ), (l.map ρ.val).getD i 0 = ρ.val (l.getD i zeroE)
  | [], i => by simp [ρ.zero]
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_mapL l i

theorem getD_mapA (a : Array E) (i : ℕ) :
    (a.toList.map ρ.val).getD i 0 = ρ.val (a.getD i zeroE) := by
  rw [getD_mapL, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-! ## 2 Tables of weights -/

/-- One more pair, on the program's elements. -/
def stepW (t : List E) (w : E × E) : List E := t.flatMap fun a => [mulE a w.1, mulE a w.2]

theorem stepArr_toList (t : Array E) (w : E × E) :
    (t.foldl (fun u a => (u.push (mulE a w.1)).push (mulE a w.2))
      (Array.emptyWithCapacity (2 * t.size))).toList = stepW t.toList w := by
  have key : ∀ (l : List E) (acc : Array E),
      (l.foldl (fun u a => (u.push (mulE a w.1)).push (mulE a w.2)) acc).toList =
        acc.toList ++ stepW l w := by
    intro l
    induction l with
    | nil => intro acc; simp [stepW]
    | cons a l ih => intro acc; rw [List.foldl_cons, ih]; simp [stepW]
  rw [← Array.foldl_toList]
  exact (key t.toList _).trans (by simp)

theorem weightsOf_toList (ws : List (E × E)) : (weightsOf ws).toList = ws.foldl stepW [oneE] := by
  have key : ∀ (l : List (E × E)) (acc : Array E),
      (l.foldl (fun t w => t.foldl (fun u a => (u.push (mulE a w.1)).push (mulE a w.2))
        (Array.emptyWithCapacity (2 * t.size))) acc).toList = l.foldl stepW acc.toList := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons a l ih => intro acc; rw [List.foldl_cons, List.foldl_cons, ih, stepArr_toList]
  unfold weightsOf
  exact key ws _

theorem stepW_map (w : E × E) : ∀ t : List E,
    (stepW t w).map ρ.val = stepK (t.map ρ.val) (ρ.val w.1, ρ.val w.2)
  | [] => rfl
  | a :: t => by
    have e : stepW (a :: t) w = mulE a w.1 :: mulE a w.2 :: stepW t w := by simp [stepW]
    rw [e, List.map_cons, List.map_cons, List.map_cons, stepK_cons, stepW_map w t, ρ.mul, ρ.mul]

theorem foldW_map : ∀ (ws : List (E × E)) (t : List E),
    (ws.foldl stepW t).map ρ.val =
      (ws.map fun w => (ρ.val w.1, ρ.val w.2)).foldl stepK (t.map ρ.val)
  | [], _ => rfl
  | w :: ws, t => by
    rw [List.foldl_cons, foldW_map ws, stepW_map, List.map_cons, List.foldl_cons]

theorem stepL_map (zv : E) : ∀ t : List E,
    (stepL t zv).map ρ.val = stepK (t.map ρ.val) (1 - ρ.val zv, ρ.val zv)
  | [] => rfl
  | a :: t => by
    have e : stepL (a :: t) zv = subE a (mulE a zv) :: mulE a zv :: stepL t zv := by simp [stepL]
    have h1 : ρ.val (subE a (mulE a zv)) = ρ.val a * (1 - ρ.val zv) := by
      rw [ρ.sub, ρ.mul]
      ring
    rw [e, List.map_cons, List.map_cons, List.map_cons, stepK_cons, stepL_map zv t, h1, ρ.mul]

theorem foldL_map : ∀ (zs t : List E),
    (zs.foldl stepL t).map ρ.val =
      (zs.map fun zv => (1 - ρ.val zv, ρ.val zv)).foldl stepK (t.map ρ.val)
  | [], _ => rfl
  | zv :: zs, t => by
    rw [List.foldl_cons, foldL_map zs, stepL_map, List.map_cons, List.foldl_cons]

/-- The sum under a table that reads as the table made of the pairs q, the last at bit 0. -/
theorem tab_sum (a : Array E) (q : List (K × K))
    (h : a.toList.map ρ.val = q.foldl stepK [1]) (F : ℕ → K) :
    ∑ i ∈ Finset.range (2 ^ q.length), ρ.val (a.getD i zeroE) * F i = sumOver q.reverse F := by
  have hl : (a.toList.map ρ.val).length = 2 ^ q.length := by
    rw [h, tab_length]
    simp
  rw [← dotK_tab, List.reverse_reverse, ← h, dotK_sum, hl]
  exact Finset.sum_congr rfl fun i _ => by rw [getD_mapA]

/-- **The sum under `weightsOf`.** -/
theorem weights_sum (ws : List (E × E)) (F : ℕ → K) :
    ∑ i ∈ Finset.range (2 ^ ws.length), ρ.val ((weightsOf ws).getD i zeroE) * F i =
      sumOver (ws.map fun w => (ρ.val w.1, ρ.val w.2)).reverse F := by
  have h : (weightsOf ws).toList.map ρ.val =
      (ws.map fun w => (ρ.val w.1, ρ.val w.2)).foldl stepK [1] := by
    rw [weightsOf_toList, foldW_map, List.map_cons, List.map_nil, ρ.one]
  have := tab_sum ρ (weightsOf ws) _ h F
  rwa [List.length_map] at this

/-- **The sum under the library's equality table.** -/
theorem eqTab_sum (z : Array E) (F : ℕ → K) :
    ∑ i ∈ Finset.range (2 ^ z.size), ρ.val ((eqTab z).getD i zeroE) * F i =
      sumOver (z.toList.map fun zv => (1 - ρ.val zv, ρ.val zv)).reverse F := by
  have h : (eqTab z).toList.map ρ.val =
      (z.toList.map fun zv => (1 - ρ.val zv, ρ.val zv)).foldl stepK [1] := by
    rw [eqTab_toList, foldL_map, List.map_cons, List.map_nil, ρ.one]
  have := tab_sum ρ (eqTab z) _ h F
  rwa [List.length_map, Array.length_toList] at this

/-! ## 3 The loops -/

theorem foldRange (h : ℕ → E) (a : E) : ∀ N : ℕ,
    ρ.val ((List.range N).foldl (fun t i => addE t (h i)) a) =
      ρ.val a + ∑ i ∈ Finset.range N, ρ.val (h i)
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ρ.add, foldRange h a N,
      Finset.sum_range_succ]
    ring

/-- The loop of `Cube.round`: three sums at once. -/
def fold3 (k : ℕ → E) (g : ℕ → E × E × E) (N : ℕ) : E × E × E :=
  (List.range N).foldl
    (fun q i => (addE q.1 (mulE (k i) (g i).1), addE q.2.1 (mulE (k i) (g i).2.1),
      addE q.2.2 (mulE (k i) (g i).2.2)))
    (zeroE, zeroE, zeroE)

theorem fold3_succ (k : ℕ → E) (g : ℕ → E × E × E) (N : ℕ) :
    fold3 k g (N + 1) = (addE (fold3 k g N).1 (mulE (k N) (g N).1),
      addE (fold3 k g N).2.1 (mulE (k N) (g N).2.1),
      addE (fold3 k g N).2.2 (mulE (k N) (g N).2.2)) := by
  unfold fold3
  rw [List.range_succ, List.foldl_append]
  rfl

theorem fold3_read (k : ℕ → E) (g : ℕ → E × E × E) (X : K) : ∀ N : ℕ,
    ρ.val (fold3 k g N).1 + ρ.val (fold3 k g N).2.1 * X + ρ.val (fold3 k g N).2.2 * X ^ 2 =
      ∑ i ∈ Finset.range N,
        ρ.val (k i) * (ρ.val (g i).1 + ρ.val (g i).2.1 * X + ρ.val (g i).2.2 * X ^ 2)
  | 0 => by simp [fold3, ρ.zero]
  | N + 1 => by
    rw [fold3_succ, Finset.sum_range_succ, ← fold3_read k g X N]
    simp only [ρ.add, ρ.mul]
    ring

/-! ## 4 The summand -/

theorem termsAt_rd (pairs : List (E × Nat × Nat)) (ms : Array Tab) (j : ℕ) :
    ρ.val (termsAt pairs ms j) = sumT ρ pairs (rdM ρ ms) j := by
  have gen : ∀ (ps : List (E × Nat × Nat)) (q : E),
      ρ.val (ps.foldl (fun q x => addE q (mulE x.1
        (mulE ((ms.getD x.2.1 #[]).getD j zeroE) ((ms.getD x.2.2 #[]).getD j zeroE)))) q) =
        ρ.val q + sumT ρ ps (rdM ρ ms) j := by
    intro ps
    induction ps with
    | nil => intro q; simp [sumT]
    | cons x ps ih =>
      intro q
      rw [List.foldl_cons, ih, ρ.add, ρ.mul, ρ.mul]
      simp only [sumT, List.map_cons, List.sum_cons, rdM, rdT]
      ring
  unfold termsAt
  rw [gen, ρ.zero, zero_add]

/-- One turn of `lineAt`'s loop. -/
def lineStep (ms : Array Tab) (j s : ℕ) (q : E × E × E) (x : E × Nat × Nat) : E × E × E :=
  (addE q.1 (mulE x.1 (mulE ((ms.getD x.2.1 #[]).getD j zeroE) ((ms.getD x.2.2 #[]).getD j zeroE))),
    addE q.2.1 (mulE x.1 (addE
      (mulE ((ms.getD x.2.1 #[]).getD j zeroE)
        (subE ((ms.getD x.2.2 #[]).getD (j + s) zeroE) ((ms.getD x.2.2 #[]).getD j zeroE)))
      (mulE (subE ((ms.getD x.2.1 #[]).getD (j + s) zeroE) ((ms.getD x.2.1 #[]).getD j zeroE))
        ((ms.getD x.2.2 #[]).getD j zeroE)))),
    addE q.2.2 (mulE x.1 (mulE
      (subE ((ms.getD x.2.1 #[]).getD (j + s) zeroE) ((ms.getD x.2.1 #[]).getD j zeroE))
      (subE ((ms.getD x.2.2 #[]).getD (j + s) zeroE) ((ms.getD x.2.2 #[]).getD j zeroE)))))

theorem lineAt_eq (pairs : List (E × Nat × Nat)) (ms : Array Tab) (j s : ℕ) :
    lineAt pairs ms j s = pairs.foldl (lineStep ms j s) (zeroE, zeroE, zeroE) := rfl

/-- **The three coefficients between two entries, at X: the summand on the tables with the variable
set to X.** -/
theorem lineAt_rd (pairs : List (E × Nat × Nat)) (ms : Array Tab) (s i : ℕ) (X : K) :
    ρ.val (lineAt pairs ms (lowAt s i) s).1 + ρ.val (lineAt pairs ms (lowAt s i) s).2.1 * X +
      ρ.val (lineAt pairs ms (lowAt s i) s).2.2 * X ^ 2 =
      sumT ρ pairs (fun a => bindK s X (rdM ρ ms a)) i := by
  have gen : ∀ (ps : List (E × Nat × Nat)) (q : E × E × E),
      ρ.val (ps.foldl (lineStep ms (lowAt s i) s) q).1 +
        ρ.val (ps.foldl (lineStep ms (lowAt s i) s) q).2.1 * X +
        ρ.val (ps.foldl (lineStep ms (lowAt s i) s) q).2.2 * X ^ 2 =
        (ρ.val q.1 + ρ.val q.2.1 * X + ρ.val q.2.2 * X ^ 2) +
          sumT ρ ps (fun a => bindK s X (rdM ρ ms a)) i := by
    intro ps
    induction ps with
    | nil => intro q; simp [sumT]
    | cons x ps ih =>
      intro q
      rw [List.foldl_cons, ih]
      simp only [lineStep, sumT, List.map_cons, List.sum_cons, rdM, rdT, bindK, ρ.add, ρ.mul, ρ.sub]
      ring
  rw [lineAt_eq, gen]
  simp [ρ.zero]

/-! ## 5 A variable set -/

theorem bindAt_size (p : ℕ) (r : E) (t : Tab) : (bindAt p r t).size = t.size / 2 := by
  simp [bindAt]

/-- An array made of a function, entry by entry. On words. -/
theorem ofFnE_getD {n : ℕ} (f : Fin n → E) (i : ℕ) (h : i < n) :
    (Array.ofFn f).getD i zeroE = f ⟨i, h⟩ := by
  simp [Array.getD, h]

theorem bindAt_read (p : ℕ) (r : E) (t : Tab) (i : ℕ) (h : i < t.size / 2) :
    rdT ρ (bindAt p r t) i = bindK (2 ^ p) (ρ.val r) (rdT ρ t) i := by
  show ρ.val ((Array.ofFn (n := t.size / 2) fun i : Fin (t.size / 2) =>
    addE (t.getD (lowAt (2 ^ p) i.val) zeroE) (mulE r (subE
      (t.getD (lowAt (2 ^ p) i.val + 2 ^ p) zeroE) (t.getD (lowAt (2 ^ p) i.val) zeroE)))).getD i
        zeroE) = _
  rw [ofFnE_getD _ i h, ρ.add, ρ.mul, ρ.sub]
  rfl

/-- All tables with one variable set, where each has 2 ^ (L + 1) entries. -/
theorem rdM_bind (ms : Array Tab) (p : ℕ) (r : E) (L : ℕ)
    (hs : ∀ a, a < ms.size → (ms.getD a #[]).size = 2 ^ (L + 1)) (a i : ℕ) (hi : i < 2 ^ L) :
    rdM ρ (ms.map (bindAt p r)) a i = bindK (2 ^ p) (ρ.val r) (rdM ρ ms a) i := by
  unfold rdM
  by_cases h : a < ms.size
  · rw [getD_map_lt ms (bindAt p r) h #[] #[]]
    exact bindAt_read ρ p r _ i (by rw [hs a h, pow_succ]; omega)
  · have h' : ms.size ≤ a := Nat.le_of_not_lt h
    rw [getD_ge ms h' #[], getD_ge (ms.map (bindAt p r)) (by rw [Array.size_map]; exact h') #[]]
    simp [bindK, rdT_empty]

end OnBytes.Desc.First.K4.Honest.CubeLaw

#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.rdT
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.rdM
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sumT
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.rdT_empty
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.getD_mapL
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.getD_mapA
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.stepW
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.stepArr_toList
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.weightsOf_toList
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.stepW_map
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.foldW_map
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.stepL_map
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.foldL_map
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.tab_sum
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.weights_sum
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.eqTab_sum
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.foldRange
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.fold3
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.fold3_succ
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.fold3_read
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.termsAt_rd
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.lineStep
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.lineAt_eq
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.lineAt_rd
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.bindAt_size
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.ofFnE_getD
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.bindAt_read
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.rdM_bind
