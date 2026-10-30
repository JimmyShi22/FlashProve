-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/FixLaws.lean: what fixing the lowest variables of a structured vector does to its
entries.

Tensor.fixLow and Form.fixLow (OnBytes/Iop/Tensor.lean) fix the lowest variables of a vector at the
coordinates of a point g. The law: under any reading of the program's field elements in a
commutative ring (Reading, OnBytes/Model/HideLaws.lean), entry p of the result reads as the sum,
over the numbers b below 2^|g|, of the weight of b at g (eqVal, OnBytes/Iop/SymbolReads.lean) times
entry b + 2^|g| p of the vector; Form.fixLow multiplies the sum by its factor times. Two conditions:
every tensor has at least |g| variables, and every tensor is in order (Tensor.InOrder: each dense
variable is named once and has the pair (1, 1)). Tensor.ok tests the second; Form.fits tests both if
|g| is at most its number of variables. The law holds also for a tensor with a written-out factor,
whose slice is folded.

Tensor, form, pair, dense variable, slice and written-out factor are explained at the head of
Tensor.lean. x reads as y: the reading takes x to y.

Form.fixLow lets tensors that have the same slice share one folded slice; the law covers that, and
the merging of single entries.

Main definitions: wVal, wSum, keptVars, foldedVal, lowWeights, Tensor.sliceVal, Tensor.InOrder,
ServesSlice, SlicesOk, entSum, lowSum.
Main theorems: sum_dense, fixPairs_val, Tensor.sum_low, foldBit_val, Tensor.foldedSlice_val,
Tensor.fixLowWith_val, Tensor.fixLow_val, eqWeight_val, entSum_mergeEntries, fixLowShared_val,
Form.fixLow_val, Form.fixLowPlain_val, Form.fixLow_val_of_fits, Tensor.fixLow_shape,
Form.fixLow_shape.

What is not claimed. That Form.fixLow and Form.fixLowPlain return the same words; shown is only that
both read as the same sums. Nothing for a point with more coordinates than a tensor has variables.
That the result passes Form.fits. That the forms which the program fixes meet the two conditions.
Nothing on soundness. The program does not import this file, and no other file uses its theorems.
-/
import OnBytes.Iop.SymbolReads
import OnBytes.Iop.DotLaws

namespace OnBytes

open Model (Reading)

variable {K : Type} [CommRing K]

/-! ## Weights that are products over the bits of a number -/

/-- The product, over the pairs, of the half that the bits of b pick, the lowest bit first. -/
def wVal : List (K × K) → Nat → K
  | [], _ => 1
  | w :: ws, b => (if b % 2 = 1 then w.2 else w.1) * wVal ws (b / 2)

/-- The product of the pairs' sums. -/
def wSum : List (K × K) → K
  | [] => 1
  | w :: ws => (w.1 + w.2) * wSum ws

/-- A sum over the numbers below 2^(n+1), by the lowest bit. -/
theorem sum_low_bit (n : Nat) (F : Nat → K) :
    ((List.range (2 ^ (n + 1))).map F).sum =
      ((List.range (2 ^ n)).map fun b => F (2 * b) + F (2 * b + 1)).sum := by
  rw [Nat.pow_succ, Nat.mul_comm, sum_range_pairs]

/-- The weights of the numbers below 2 to the number of pairs add up to the product of the pairs'
sums. -/
theorem sum_wVal : ∀ ws : List (K × K),
    ((List.range (2 ^ ws.length)).map (wVal ws)).sum = wSum ws
  | [] => by simp [wVal, wSum]
  | w :: ws => by
    rw [List.length_cons, sum_low_bit]
    have e : ∀ b,
        wVal (w :: ws) (2 * b) + wVal (w :: ws) (2 * b + 1) = (w.1 + w.2) * wVal ws b := by
      intro b
      simp only [wVal]
      rw [if_neg (by omega : ¬ 2 * b % 2 = 1), if_pos (by omega : (2 * b + 1) % 2 = 1),
        show 2 * b / 2 = b by omega, show (2 * b + 1) / 2 = b by omega]
      ring
    simp only [e]
    rw [List.sum_map_mul_left, sum_wVal ws, wSum]

/-- A weight is the sum of the two weights in which one half of the pair number d is 0. -/
theorem wVal_split : ∀ (ws : List (K × K)) (d : Nat) (w : K × K), ws[d]? = some w → ∀ b,
    wVal ws b = wVal (ws.set d (w.1, 0)) b + wVal (ws.set d (0, w.2)) b
  | [], _, _, h, _ => by simp at h
  | u :: ws, 0, w, h, b => by
    have e : u = w := by simpa using h
    subst e
    simp only [List.set_cons_zero, wVal]
    split <;> ring
  | u :: ws, d + 1, w, h, b => by
    have h' : ws[d]? = some w := by simpa using h
    simp only [List.set_cons_succ, wVal]
    rw [wVal_split ws d w h' (b / 2)]
    ring

/-- If the high half of pair number d is 0, a number whose bit d is 1 has the weight 0. -/
theorem wVal_low : ∀ (ws : List (K × K)) (d : Nat) (a : K), d < ws.length → ∀ b,
    b / 2 ^ d % 2 = 1 → wVal (ws.set d (a, 0)) b = 0
  | [], _, _, h, _, _ => by simp at h
  | u :: ws, 0, a, _, b, hb => by
    simp only [List.set_cons_zero, wVal]
    rw [if_pos (by simpa using hb)]
    ring
  | u :: ws, d + 1, a, h, b, hb => by
    simp only [List.set_cons_succ, wVal]
    rw [wVal_low ws d a (by simpa using h) (b / 2)
      (by rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']; exact hb)]
    ring

/-- If the low half of pair number d is 0, a number whose bit d is 0 has the weight 0. -/
theorem wVal_high : ∀ (ws : List (K × K)) (d : Nat) (a : K), d < ws.length → ∀ b,
    b / 2 ^ d % 2 = 0 → wVal (ws.set d (0, a)) b = 0
  | [], _, _, h, _, _ => by simp at h
  | u :: ws, 0, a, _, b, hb => by
    simp only [List.set_cons_zero, wVal]
    rw [if_neg (by
      have : b % 2 = 0 := by simpa using hb
      omega)]
    ring
  | u :: ws, d + 1, a, h, b, hb => by
    simp only [List.set_cons_succ, wVal]
    rw [wVal_high ws d a (by simpa using h) (b / 2)
      (by rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']; exact hb)]
    ring

/-- The product of the sums with another pair in the place of one whose halves add up to 1. -/
theorem wSum_set : ∀ (ws : List (K × K)) (d : Nat) (w u : K × K), ws[d]? = some w →
    w.1 + w.2 = 1 → wSum (ws.set d u) = wSum ws * (u.1 + u.2)
  | [], _, _, _, h, _ => by simp at h
  | v :: ws, 0, w, u, h, h1 => by
    have e : v = w := by simpa using h
    subst e
    simp only [List.set_cons_zero, wSum, h1]
    ring
  | v :: ws, d + 1, w, u, h, h1 => by
    simp only [List.set_cons_succ, wSum]
    rw [wSum_set ws d w u (by simpa using h) h1]
    ring

/-! ## The index within a slice -/

/-- One place higher, the index within a slice doubles. -/
theorem denseIndex_succ : ∀ (ds : List Nat) (i j : Nat),
    denseIndex ds (i + 1) j = 2 * denseIndex ds i j
  | [], _, _ => rfl
  | d :: ds, i, j => by
    simp only [denseIndex]
    rw [denseIndex_succ ds (i + 1) j, Nat.pow_succ]
    ring

/-- A bit from m on of b + 2^m p, for b below 2^m, is a bit of p. -/
theorem bit_high (m d b p : Nat) (hb : b < 2 ^ m) (hd : m ≤ d) :
    (b + 2 ^ m * p) / 2 ^ d % 2 = p / 2 ^ (d - m) % 2 := by
  have e : 2 ^ d = 2 ^ m * 2 ^ (d - m) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m),
    Nat.div_eq_of_lt hb, Nat.zero_add]

/-- A bit below m of b + 2^m p is a bit of b. -/
theorem bit_low (m d b p : Nat) (hd : d < m) :
    (b + 2 ^ m * p) / 2 ^ d % 2 = b / 2 ^ d % 2 := by
  have e : 2 ^ m * p = 2 ^ d * (2 * (2 ^ (m - d - 1) * p)) := by
    have : 2 ^ m = 2 ^ d * (2 * 2 ^ (m - d - 1)) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]
      congr 1
      omega
    rw [this]
    ring
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos d)]
  omega

/-- The dense variables that are left when the lowest m variables are fixed, renumbered. -/
def keptVars (m : Nat) (ds : List Nat) : List Nat := (ds.filter (m ≤ ·)).map (· - m)

/-- What a slice becomes when the dense variables below m are fixed. A: the slice, as a function of
the index within it. x d: the coordinate at which variable d is fixed. The list is what is left of
the dense variables, and its first element belongs to bit number i of the index within the slice.
low: the bits below i. hk: the index within the new slice, from the bit of the list's first kept
variable on. -/
def foldedVal (A : Nat → K) (m : Nat) (x : Nat → K) : List Nat → Nat → Nat → Nat → K
  | [], _, low, _ => A low
  | d :: ds, i, low, hk =>
    if d < m then
      (1 - x d) * foldedVal A m x ds (i + 1) low hk +
        x d * foldedVal A m x ds (i + 1) (low + 2 ^ i) hk
    else foldedVal A m x ds (i + 1) (low + hk % 2 * 2 ^ i) (hk / 2)

/-- The sum, over the low bits b, of the weight of b times a factor read off a slice A is the
product of the pairs' sums times the folded slice (foldedVal) at the index that p gives. ws: the
weights of the low bits; at each dense variable d below their number the pair must be
(1 - x d, x d). No dense variable may be named twice. -/
theorem sum_dense (A : Nat → K) (x : Nat → K) (p : Nat) :
    ∀ (ds : List Nat) (ws : List (K × K)) (i low : Nat), ds.Nodup →
    (∀ d ∈ ds, d < ws.length → ws[d]? = some (1 - x d, x d)) →
    ((List.range (2 ^ ws.length)).map fun b =>
      wVal ws b * A (low + denseIndex ds i (b + 2 ^ ws.length * p))).sum =
      wSum ws * foldedVal A ws.length x ds i low (denseIndex (keptVars ws.length ds) 0 p)
  | [], ws, i, low, _, _ => by
    simp only [denseIndex, Nat.add_zero, foldedVal]
    rw [List.sum_map_mul_right, sum_wVal]
  | d :: ds, ws, i, low, hn, hw => by
    obtain ⟨hd, hn'⟩ := List.nodup_cons.1 hn
    by_cases hm : d < ws.length
    · -- the variable is fixed: the sum splits by its bit
      have hwd := hw d (by simp) hm
      have keep : ∀ (u : K × K), ∀ d' ∈ ds, d' < (ws.set d u).length →
          (ws.set d u)[d']? = some (1 - x d', x d') := by
        intro u d' hd' hl
        rw [List.length_set] at hl
        have hne : d ≠ d' := fun e => hd (e ▸ hd')
        rw [List.getElem?_set_ne hne]
        exact hw d' (by simp [hd']) hl
      have i0 := sum_dense A x p ds (ws.set d (1 - x d, 0)) (i + 1) low hn' (keep _)
      have i1 := sum_dense A x p ds (ws.set d (0, x d)) (i + 1) (low + 2 ^ i) hn' (keep _)
      rw [List.length_set] at i0 i1
      have term : ∀ b, wVal ws b * A (low + denseIndex (d :: ds) i (b + 2 ^ ws.length * p)) =
          wVal (ws.set d (1 - x d, 0)) b *
              A (low + denseIndex ds (i + 1) (b + 2 ^ ws.length * p)) +
            wVal (ws.set d (0, x d)) b *
              A (low + 2 ^ i + denseIndex ds (i + 1) (b + 2 ^ ws.length * p)) := by
        intro b
        rw [wVal_split ws d _ hwd b]
        simp only [denseIndex]
        rw [bit_low _ _ _ _ hm]
        rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ d) with h0 | h1
        · rw [h0, wVal_high ws d _ hm b h0]
          simp
        · rw [h1, wVal_low ws d _ hm b h1, Nat.one_mul, Nat.add_assoc]
          simp
      simp only [term]
      rw [List.sum_map_add, i0, i1, wSum_set ws d _ _ hwd (by ring),
        wSum_set ws d _ _ hwd (by ring)]
      have hk : keptVars ws.length (d :: ds) = keptVars ws.length ds := by
        unfold keptVars
        rw [List.filter_cons_of_neg (by simpa using hm)]
      rw [hk, foldedVal, if_pos hm]
      ring
    · -- the variable stays: its bit is a bit of p
      have hm' : ws.length ≤ d := Nat.le_of_not_lt hm
      have ih := sum_dense A x p ds ws (i + 1) (low + p / 2 ^ (d - ws.length) % 2 * 2 ^ i) hn'
        (fun d' hd' => hw d' (by simp [hd']))
      have term : ∀ b ∈ List.range (2 ^ ws.length),
          wVal ws b * A (low + denseIndex (d :: ds) i (b + 2 ^ ws.length * p)) =
          wVal ws b * A (low + p / 2 ^ (d - ws.length) % 2 * 2 ^ i +
            denseIndex ds (i + 1) (b + 2 ^ ws.length * p)) := by
        intro b hb
        simp only [denseIndex]
        rw [bit_high _ _ _ _ (List.mem_range.1 hb) hm', Nat.add_assoc]
      rw [List.map_congr_left term, ih]
      have hk : keptVars ws.length (d :: ds) = (d - ws.length) :: keptVars ws.length ds := by
        unfold keptVars
        rw [List.filter_cons_of_pos (by simpa using hm'), List.map_cons]
      rw [hk, foldedVal, if_neg hm]
      simp only [denseIndex, Nat.pow_zero, Nat.mul_one]
      rw [denseIndex_succ]
      have b2 := Nat.mod_lt (p / 2 ^ (d - ws.length)) (by decide : 0 < 2)
      rw [show (p / 2 ^ (d - ws.length) % 2 + 2 * denseIndex (keptVars ws.length ds) 0 p) % 2 =
          p / 2 ^ (d - ws.length) % 2 by omega,
        show (p / 2 ^ (d - ws.length) % 2 + 2 * denseIndex (keptVars ws.length ds) 0 p) / 2 =
          denseIndex (keptVars ws.length ds) 0 p by omega]

/-! ## The pairs of a tensor, fixed at a point -/

variable (ρ : Reading K)

/-- The weights of the low bits: for each coordinate x of the point and the pair (lo, hi) of its
variable, ((1 - x) lo, x hi). -/
def lowWeights : List (E × E) → List E → List (K × K)
  | p :: ps, x :: xs => ((1 - ρ.val x) * ρ.val p.1, ρ.val x * ρ.val p.2) :: lowWeights ps xs
  | _, _ => []

/-- There are as many weights as coordinates, if there are at least as many pairs. -/
theorem lowWeights_length : ∀ (ps : List (E × E)) (g : List E), g.length ≤ ps.length →
    (lowWeights ρ ps g).length = g.length
  | _, [], _ => by cases ‹List (E × E)› <;> rfl
  | [], _ :: _, h => by simp at h
  | _ :: ps, _ :: xs, h => by
    simp only [lowWeights, List.length_cons]
    rw [lowWeights_length ps xs (by simpa using h)]

/-- One step of fixPairs, as an equation between functions of the factor (why so: pairsAt_cons_fun,
OnBytes/Iop/TensorLaws.lean). -/
theorem fixPairs_cons_fun (p : E × E) (ps : List (E × E)) (x : E) (xs : List E) :
    fixPairs (p :: ps) (x :: xs) =
      fun s => fixPairs ps xs (mulE s (addE p.1 (mulE x (subE p.2 p.1)))) := rfl

/-- Without pairs fixPairs returns the factor. -/
theorem fixPairs_nil_left_fun (g : List E) : fixPairs [] g = fun s => (s, []) := by
  cases g <;> rfl

/-- Without coordinates fixPairs returns the factor and the pairs. -/
theorem fixPairs_nil_right_fun (ps : List (E × E)) : fixPairs ps [] = fun s => (s, ps) := by
  cases ps <;> rfl

/-- fixPairs: the factor is multiplied by the sums of the low bits' weights, and the pairs of the
variables that were fixed are dropped. -/
theorem fixPairs_val : ∀ (ps : List (E × E)) (g : List E) (s : E),
    ρ.val (fixPairs ps g s).1 = ρ.val s * wSum (lowWeights ρ ps g) ∧
      (fixPairs ps g s).2 = ps.drop g.length
  | [], g, s => by
    rw [fixPairs_nil_left_fun]
    cases g <;> simp [lowWeights, wSum]
  | p :: ps, [], s => by
    rw [fixPairs_nil_right_fun]
    simp [lowWeights, wSum]
  | p :: ps, x :: xs, s => by
    rw [fixPairs_cons_fun]
    obtain ⟨h1, h2⟩ := fixPairs_val ps xs (mulE s (addE p.1 (mulE x (subE p.2 p.1))))
    refine ⟨?_, by rw [h2]; rfl⟩
    rw [h1, ρ.mul, ρ.add, ρ.mul, ρ.sub]
    simp only [lowWeights, wSum]
    ring

/-- The pairs that fixPairs leaves. -/
theorem fixPairs_drop : ∀ (ps : List (E × E)) (g : List E) (s : E),
    (fixPairs ps g s).2 = ps.drop g.length
  | [], g, s => by
    rw [fixPairs_nil_left_fun]
    simp
  | p :: ps, [], s => by
    rw [fixPairs_nil_right_fun]
    rfl
  | p :: ps, x :: xs, s => by
    rw [fixPairs_cons_fun]
    exact fixPairs_drop ps xs _

/-- The weight of b at the point times the pairs' product at b + 2^|g| p. -/
theorem eqVal_mul_pairsVal : ∀ (g : List E) (ps : List (E × E)) (b p : Nat),
    g.length ≤ ps.length → b < 2 ^ g.length →
    eqVal ρ g b * pairsVal ρ ps (b + 2 ^ g.length * p) =
      wVal (lowWeights ρ ps g) b * pairsVal ρ (ps.drop g.length) p
  | [], ps, b, p, _, hb => by
    have b0 : b = 0 := by simpa using hb
    subst b0
    cases ps <;> simp [eqVal_nil, lowWeights, wVal]
  | _ :: _, [], _, _, h, _ => by simp at h
  | x :: xs, q :: qs, b, p, h, hb => by
    have hb' : b / 2 < 2 ^ xs.length := by
      rw [List.length_cons, Nat.pow_succ] at hb
      omega
    have e0 : 2 ^ (x :: xs).length * p = 2 * (2 ^ xs.length * p) := by
      rw [List.length_cons, Nat.pow_succ]
      ring
    have e1 : (b + 2 ^ (x :: xs).length * p) % 2 = b % 2 := by
      rw [e0]
      omega
    have e2 : (b + 2 ^ (x :: xs).length * p) / 2 = b / 2 + 2 ^ xs.length * p := by
      rw [e0]
      omega
    have ih := eqVal_mul_pairsVal xs qs (b / 2) p (by simpa using h) hb'
    rw [eqVal_cons, pairsVal, e1, e2]
    simp only [lowWeights, wVal, List.length_cons, List.drop_succ_cons]
    by_cases hb2 : b % 2 = 1
    · simp only [hb2, if_true, beq_self_eq_true]
      linear_combination (ρ.val x * ρ.val q.2) * ih
    · have : (b % 2 == 1) = false := by simpa using hb2
      simp only [hb2, if_false, this, Bool.false_eq_true]
      linear_combination ((1 - ρ.val x) * ρ.val q.1) * ih

/-- The weights at a variable whose pair is (1, 1). -/
theorem lowWeights_get : ∀ (ps : List (E × E)) (g : List E) (d : Nat), d < g.length →
    ps[d]? = some (oneE, oneE) →
    (lowWeights ρ ps g)[d]? = some (1 - ρ.val (g.getD d zeroE), ρ.val (g.getD d zeroE))
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | p :: ps, x :: xs, 0, _, h => by
    have e : p = (oneE, oneE) := by simpa using h
    subst e
    simp [lowWeights, ρ.one]
  | p :: ps, x :: xs, d + 1, hd, h => by
    have ih := lowWeights_get ps xs d (by simpa using hd) (by simpa using h)
    simpa [lowWeights] using ih

/-! ## A tensor, summed over its lowest variables -/

/-- The written-out factor of a tensor as a function of the index within the slice; 1 for a tensor
without such a factor. -/
def Tensor.sliceVal (v : Tensor) (low : Nat) : K :=
  if v.denseVars.isEmpty then 1 else ρ.val (v.values.getD (v.first + low) zeroE)

/-- The written-out factor at an index of the vector, read off the slice. -/
theorem Tensor.denseVal_eq (v : Tensor) (j : Nat) :
    v.denseVal ρ j = v.sliceVal ρ (denseIndex v.denseVars 0 j) := rfl

/-- The sum, over the numbers b below 2^|g|, of the weight of b at g times entry b + 2^|g| p. It
reads as the scalar, times the product of the low weights' sums, times the remaining pairs at p,
times the folded slice at p. Conditions: at least |g| variables; each dense variable named once,
with the pair (1, 1). -/
theorem Tensor.sum_low (v : Tensor) (g : List E) (hg : g.length ≤ v.vars)
    (hn : v.denseVars.Nodup) (h1 : ∀ d ∈ v.denseVars, v.pairs[d]? = some (oneE, oneE)) (p : Nat) :
    ((List.range (2 ^ g.length)).map fun b =>
      eqVal ρ g b * ρ.val (v.entry (b + 2 ^ g.length * p))).sum =
      ρ.val v.scalar * wSum (lowWeights ρ v.pairs g) * pairsVal ρ (v.pairs.drop g.length) p *
        foldedVal (v.sliceVal ρ) g.length (fun d => ρ.val (g.getD d zeroE)) v.denseVars 0 0
          (denseIndex (keptVars g.length v.denseVars) 0 p) := by
  have hl := lowWeights_length ρ v.pairs g hg
  have hs := sum_dense (v.sliceVal ρ) (fun d => ρ.val (g.getD d zeroE)) p v.denseVars
    (lowWeights ρ v.pairs g) 0 0 hn (fun d hd hlt =>
      lowWeights_get ρ v.pairs g d (by rw [← hl]; exact hlt) (h1 d hd))
  rw [hl] at hs
  have term : ∀ b ∈ List.range (2 ^ g.length),
      eqVal ρ g b * ρ.val (v.entry (b + 2 ^ g.length * p)) =
      (ρ.val v.scalar * pairsVal ρ (v.pairs.drop g.length) p) *
        (wVal (lowWeights ρ v.pairs g) b *
          v.sliceVal ρ (0 + denseIndex v.denseVars 0 (b + 2 ^ g.length * p))) := by
    intro b hb
    have e := eqVal_mul_pairsVal ρ g v.pairs b p hg (List.mem_range.1 hb)
    rw [Tensor.entry_val, Tensor.denseVal_eq, Nat.zero_add]
    linear_combination
      (ρ.val v.scalar * v.sliceVal ρ (denseIndex v.denseVars 0 (b + 2 ^ g.length * p))) * e
  rw [List.map_congr_left term, List.sum_map_mul_left, hs]
  ring

/-- The index within a slice, counted from bit i: with 2^i added it is at most 2^(i + the number of
dense variables). -/
theorem denseIndex_bound : ∀ (ds : List Nat) (i j : Nat),
    denseIndex ds i j + 2 ^ i ≤ 2 ^ (i + ds.length)
  | [], i, _ => by simp [denseIndex]
  | d :: ds, i, j => by
    have ih := denseIndex_bound ds (i + 1) j
    have hb := Nat.mod_lt (j / 2 ^ d) (by decide : 0 < 2)
    have e : i + (d :: ds).length = i + 1 + ds.length := by simp; omega
    have hm : j / 2 ^ d % 2 * 2 ^ i ≤ 2 ^ i := by
      calc j / 2 ^ d % 2 * 2 ^ i ≤ 1 * 2 ^ i := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ i := Nat.one_mul _
    rw [Nat.pow_succ] at ih
    simp only [denseIndex]
    rw [e]
    omega

/-- The index within a slice, counted from bit 0, is within the slice. -/
theorem denseIndex_lt (ds : List Nat) (j : Nat) : denseIndex ds 0 j < 2 ^ ds.length := by
  have h := denseIndex_bound ds 0 j
  simp only [Nat.pow_zero, Nat.zero_add] at h
  omega

/-- If no dense variable is fixed, the slice stays: its entries are read at the same places. -/
theorem foldedVal_uncut (A : Nat → K) (m : Nat) (x : Nat → K) :
    ∀ (ds : List Nat) (i low hk : Nat), (∀ d ∈ ds, m ≤ d) →
    foldedVal A m x ds i low hk = A (low + hk % 2 ^ ds.length * 2 ^ i)
  | [], _, low, hk, _ => by simp [foldedVal, Nat.mod_one]
  | d :: ds, i, low, hk, h => by
    have hd : ¬ d < m := Nat.not_lt.2 (h d (by simp))
    rw [foldedVal, if_neg hd, foldedVal_uncut A m x ds (i + 1) _ _ (fun e he => h e (by simp [he]))]
    congr 1
    have e : hk % 2 ^ (d :: ds).length = hk % 2 + 2 * (hk / 2 % 2 ^ ds.length) := by
      rw [List.length_cons, Nat.pow_succ', mod_two_mul]
    rw [e, Nat.pow_succ]
    ring

/-! ## The conditions on a tensor -/

/-- distinctNats says that no number occurs twice. -/
theorem nodup_of_distinctNats : ∀ l : List Nat, distinctNats l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [distinctNats, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact List.nodup_cons.2 ⟨h.1, nodup_of_distinctNats l h.2⟩

/-- What Tensor.ok says of the dense variables. -/
theorem Tensor.dense_of_ok (v : Tensor) (h : v.ok = true) :
    v.denseVars.Nodup ∧ (∀ d ∈ v.denseVars, v.pairs[d]? = some (oneE, oneE)) ∧
      (v.denseVars.isEmpty = false → v.first + 2 ^ v.denseVars.length ≤ v.values.size) := by
  unfold Tensor.ok at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨_, h2⟩, h3⟩, h4⟩ := h
  refine ⟨nodup_of_distinctNats _ h4, h3, fun he => ?_⟩
  rcases h2 with h2 | h2
  · rw [he] at h2
    cases h2
  · exact h2

/-- What the laws below need of a tensor: no dense variable is named twice, and each has the pair
(1, 1). Tensor.ok tests it. -/
def Tensor.InOrder (v : Tensor) : Prop :=
  v.denseVars.Nodup ∧ ∀ d ∈ v.denseVars, v.pairs[d]? = some (oneE, oneE)

/-- A tensor that passes Tensor.ok is in order. -/
theorem Tensor.inOrder_of_ok (v : Tensor) (h : v.ok = true) : v.InOrder :=
  ⟨(v.dense_of_ok h).1, (v.dense_of_ok h).2.1⟩

/-- A multiple of a tensor has the same dense variables. -/
theorem Tensor.denseVars_scale (v : Tensor) (x : E) : (v.scale x).denseVars = v.denseVars := by
  unfold Tensor.scale
  rfl

/-- A multiple of a tensor has the same pairs. -/
theorem Tensor.pairs_scale (v : Tensor) (x : E) : (v.scale x).pairs = v.pairs := by
  unfold Tensor.scale
  rfl

/-- A multiple of a tensor is in order if the tensor is. -/
theorem Tensor.InOrder.scale {v : Tensor} (h : v.InOrder) (x : E) : (v.scale x).InOrder := by
  unfold Tensor.InOrder
  rw [Tensor.denseVars_scale, Tensor.pairs_scale]
  exact h

/-! ## Fixing the lowest variables where the slice is not cut -/

/-- Fixing the lowest variables of a tensor none of whose dense variables is among them. -/
theorem Tensor.fixLow_val_uncut (v : Tensor) (g : List E) (hg : g.length ≤ v.vars)
    (hok : v.InOrder) (hc : v.sliceIsCut g.length = false) (p : Nat) :
    ρ.val ((v.fixLow g).entry p) =
      ((List.range (2 ^ g.length)).map fun b =>
        eqVal ρ g b * ρ.val (v.entry (b + 2 ^ g.length * p))).sum := by
  obtain ⟨hn, h1⟩ := hok
  have hall : ∀ d ∈ v.denseVars, g.length ≤ d := by
    intro d hd
    unfold Tensor.sliceIsCut at hc
    have := List.any_eq_false.1 hc d hd
    simpa using this
  have hk : keptVars g.length v.denseVars = v.denseVars.map (· - g.length) := by
    unfold keptVars
    rw [List.filter_eq_self.2 (fun d hd => by simpa using hall d hd)]
  obtain ⟨f1, f2⟩ := fixPairs_val ρ v.pairs g v.scalar
  rw [Tensor.sum_low ρ v g hg hn h1 p, foldedVal_uncut _ _ _ _ _ _ _ hall, hk]
  have hlt := denseIndex_lt (v.denseVars.map (· - g.length)) p
  rw [List.length_map] at hlt
  rw [Nat.mod_eq_of_lt hlt, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  unfold Tensor.fixLow
  simp only [hc, Bool.false_eq_true, if_false]
  rw [Tensor.entry_val]
  show ρ.val (fixPairs v.pairs g v.scalar).1 * pairsVal ρ (fixPairs v.pairs g v.scalar).2 p *
    (if (v.denseVars.map (· - g.length)).isEmpty then 1
      else ρ.val (v.values.getD (v.first + denseIndex (v.denseVars.map (· - g.length)) 0 p)
        zeroE)) = _
  rw [f1, f2]
  unfold Tensor.sliceVal
  rw [List.isEmpty_map]

/-! ## A bit folded out of a slice -/

/-- A loop that appends f 0, f 1, .. to an array. -/
theorem fold_push (f : Nat → E) : ∀ (n : Nat) (init : Array E),
    (Nat.fold n (fun idx _ (out : Array E) => out.push (f idx)) init).toList =
      init.toList ++ (List.range n).map f
  | 0, init => by simp
  | n + 1, init => by
    rw [Nat.fold_succ, Array.toList_push, fold_push f n init, List.range_succ, List.map_append,
      List.append_assoc]
    rfl

/-- An entry of an array that was made by such a loop from the empty array. -/
theorem getD_fold_push (f : Nat → E) (n cap k : Nat) :
    (Nat.fold n (fun idx _ (out : Array E) => out.push (f idx)) (Array.mkEmpty cap)).getD k zeroE =
      if k < n then f k else zeroE := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, fold_push]
  by_cases h : k < n
  · simp [h]
  · simp [h]

/-- Entry idx of foldBit, for idx below size / 2, reads as 1 - x times the entry whose bit i is 0
plus x times the entry whose bit i is 1. -/
theorem foldBit_val (a : Array E) (start size i : Nat) (x : E) (idx : Nat) (h : idx < size / 2) :
    ρ.val ((foldBit a start size i x).getD idx zeroE) =
      (1 - ρ.val x) * ρ.val (a.getD (start + idx % 2 ^ i + 2 * 2 ^ i * (idx / 2 ^ i)) zeroE) +
        ρ.val x *
          ρ.val (a.getD (start + idx % 2 ^ i + 2 * 2 ^ i * (idx / 2 ^ i) + 2 ^ i) zeroE) := by
  unfold foldBit
  dsimp only
  rw [getD_fold_push, if_pos h, foldPairE_def, ρ.add, ρ.mul, ρ.sub]
  ring

/-- An entry of a stretch that was cut out of an array. -/
theorem getD_extract (a : Array E) (s n k : Nat) :
    (a.extract s (s + n)).getD k zeroE = if k < n then a.getD (s + k) zeroE else zeroE := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  by_cases h : k < n
  · by_cases h2 : s + k < a.size
    · have : k < min (s + n) a.size - s := by omega
      simp [h, this]
    · have : ¬ k < min (s + n) a.size - s := by omega
      simp [h, this, Array.getElem?_eq_none (Nat.le_of_not_lt h2)]
  · have : ¬ k < min (s + n) a.size - s := by omega
    simp [h, this]

/-! ## The folded slice -/

/-- One step of the loop of Tensor.foldedSlice. -/
def sliceStep (v : Tensor) (g : List E) (s : Array E × Nat × Nat) (i : Nat) : Array E × Nat × Nat :=
  match v.denseVars[i]? with
  | some d =>
    if d < g.length then (foldBit s.1 s.2.1 s.2.2 i (g.getD d zeroE), 0, s.2.2 / 2) else s
  | none => s

/-- Tensor.foldedSlice, with the step of its loop written as sliceStep. -/
theorem Tensor.foldedSlice_eq (v : Tensor) (g : List E) :
    v.foldedSlice g =
      (let s := (List.range v.denseVars.length).reverse.foldl (sliceStep v g)
        (v.values, v.first, 2 ^ v.denseVars.length)
      if s.2.1 == 0 && s.1.size == s.2.2 then s.1 else s.1.extract s.2.1 (s.2.1 + s.2.2)) := rfl

/-- What holds of the loop's state when the bits from i on of the index within the slice have been
looked at: its size, and what each of its entries reads as. -/
structure SliceAt (A : Nat → K) (v : Tensor) (g : List E) (i : Nat) (s : Array E × Nat × Nat) :
    Prop where
  size : s.2.2 = 2 ^ (i + (keptVars g.length (v.denseVars.drop i)).length)
  entry : ∀ low hk, low < 2 ^ i → hk < 2 ^ (keptVars g.length (v.denseVars.drop i)).length →
    ρ.val (s.1.getD (s.2.1 + (low + 2 ^ i * hk)) zeroE) =
      foldedVal A g.length (fun d => ρ.val (g.getD d zeroE)) (v.denseVars.drop i) i low hk

/-- One step of the loop keeps what holds of the state. -/
theorem sliceStep_at (A : Nat → K) (v : Tensor) (g : List E) (i : Nat)
    (hi : i < v.denseVars.length) (s : Array E × Nat × Nat) (h : SliceAt ρ A v g (i + 1) s) :
    SliceAt ρ A v g i (sliceStep v g s i) := by
  have hd : v.denseVars[i]? = some v.denseVars[i] := List.getElem?_eq_getElem hi
  have hdrop : v.denseVars.drop i = v.denseVars[i] :: v.denseVars.drop (i + 1) :=
    List.drop_eq_getElem_cons hi
  unfold sliceStep
  rw [hd]
  dsimp only
  by_cases hm : v.denseVars[i] < g.length
  · -- the bit is folded out
    have hk : keptVars g.length (v.denseVars.drop i) =
        keptVars g.length (v.denseVars.drop (i + 1)) := by
      rw [hdrop]
      unfold keptVars
      rw [List.filter_cons_of_neg (by simpa using hm)]
    rw [if_pos hm]
    have hsz : s.2.2 / 2 = 2 ^ (i + (keptVars g.length (v.denseVars.drop (i + 1))).length) := by
      rw [h.size, show i + 1 + (keptVars g.length (v.denseVars.drop (i + 1))).length =
        i + (keptVars g.length (v.denseVars.drop (i + 1))).length + 1 by omega, Nat.pow_succ,
        Nat.mul_div_cancel _ (by decide : 0 < 2)]
    refine ⟨by rw [hk]; exact hsz, fun low hkk hl hh => ?_⟩
    rw [hk] at hh
    have hp := Nat.two_pow_pos i
    have hidx : low + 2 ^ i * hkk < s.2.2 / 2 := by
      rw [hsz, Nat.pow_add]
      calc low + 2 ^ i * hkk < 2 ^ i + 2 ^ i * hkk := by omega
        _ = 2 ^ i * (hkk + 1) := by ring
        _ ≤ 2 ^ i * 2 ^ (keptVars g.length (v.denseVars.drop (i + 1))).length :=
          Nat.mul_le_mul_left _ hh
    have m1 : (low + 2 ^ i * hkk) % 2 ^ i = low := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
    have m2 : (low + 2 ^ i * hkk) / 2 ^ i = hkk := by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hl, Nat.zero_add]
    show ρ.val ((foldBit s.1 s.2.1 s.2.2 i (g.getD v.denseVars[i] zeroE)).getD
      (0 + (low + 2 ^ i * hkk)) zeroE) = _
    rw [Nat.zero_add, foldBit_val ρ _ _ _ _ _ _ hidx, m1, m2, hdrop, foldedVal, if_pos hm]
    have l1 : low < 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
    have l2 : low + 2 ^ i < 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
    have a0 := h.entry low hkk l1 hh
    have a1 := h.entry (low + 2 ^ i) hkk l2 hh
    rw [show s.2.1 + low + 2 * 2 ^ i * hkk = s.2.1 + (low + 2 ^ (i + 1) * hkk) by
        rw [Nat.pow_succ]; ring, a0,
      show s.2.1 + (low + 2 ^ (i + 1) * hkk) + 2 ^ i = s.2.1 + (low + 2 ^ i + 2 ^ (i + 1) * hkk) by
        ring, a1]
  · -- the bit stays
    have hm' : g.length ≤ v.denseVars[i] := Nat.le_of_not_lt hm
    have hk : (keptVars g.length (v.denseVars.drop i)).length =
        (keptVars g.length (v.denseVars.drop (i + 1))).length + 1 := by
      rw [hdrop]
      unfold keptVars
      rw [List.filter_cons_of_pos (by simpa using hm'), List.map_cons, List.length_cons]
    rw [if_neg hm]
    refine ⟨by rw [h.size, hk]; congr 1; omega, fun low hkk hl hh => ?_⟩
    rw [hk, Nat.pow_succ] at hh
    have hb := Nat.mod_lt hkk (by decide : 0 < 2)
    have hmul : hkk % 2 * 2 ^ i ≤ 2 ^ i := by
      calc hkk % 2 * 2 ^ i ≤ 1 * 2 ^ i := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ i := Nat.one_mul _
    have l1 : low + hkk % 2 * 2 ^ i < 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
    have a0 := h.entry (low + hkk % 2 * 2 ^ i) (hkk / 2) l1 (by omega)
    rw [hdrop, foldedVal, if_neg hm, ← a0]
    congr 3
    have e : hkk = hkk % 2 + 2 * (hkk / 2) := by omega
    calc low + 2 ^ i * hkk = low + 2 ^ i * (hkk % 2 + 2 * (hkk / 2)) := by rw [← e]
      _ = low + hkk % 2 * 2 ^ i + 2 ^ (i + 1) * (hkk / 2) := by rw [Nat.pow_succ]; ring

/-- The loop, from the bit i down. -/
theorem sliceLoop_at (A : Nat → K) (v : Tensor) (g : List E) :
    ∀ (i : Nat), i ≤ v.denseVars.length → ∀ s, SliceAt ρ A v g i s →
    SliceAt ρ A v g 0 ((List.range i).reverse.foldl (sliceStep v g) s)
  | 0, _, s, h => h
  | i + 1, hi, s, h => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    exact sliceLoop_at A v g i (by omega) _ (sliceStep_at ρ A v g i (by omega) s h)

/-- Entry hk of the folded slice of a tensor with dense variables reads as foldedVal at hk, for hk
below 2 to the number of dense variables that are left. -/
theorem Tensor.foldedSlice_val (v : Tensor) (g : List E) (he : v.denseVars.isEmpty = false)
    (hk : Nat) (hh : hk < 2 ^ (keptVars g.length v.denseVars).length) :
    ρ.val ((v.foldedSlice g).getD hk zeroE) =
      foldedVal (v.sliceVal ρ) g.length (fun d => ρ.val (g.getD d zeroE)) v.denseVars 0 0 hk := by
  have h0 : SliceAt ρ (v.sliceVal ρ) v g v.denseVars.length
      (v.values, v.first, 2 ^ v.denseVars.length) := by
    refine ⟨by simp [keptVars], fun low hkk _ hh' => ?_⟩
    rw [List.drop_length] at hh' ⊢
    have z : hkk = 0 := by simpa [keptVars] using hh'
    subst z
    simp only [foldedVal, Nat.mul_zero, Nat.add_zero]
    unfold Tensor.sliceVal
    rw [he]
    simp
  have h := sliceLoop_at ρ (v.sliceVal ρ) v g v.denseVars.length (Nat.le_refl _) _ h0
  have hs := h.size
  have hen := h.entry 0 hk (by simp) (by simpa using hh)
  simp only [List.drop_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hs hen
  rw [Tensor.foldedSlice_eq]
  dsimp only
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [hc.1, Nat.zero_add] at hen
    exact hen
  · rw [getD_extract, hs, if_pos hh]
    exact hen

/-! ## Fixing the lowest variables of a tensor -/

/-- What a folded slice must read as, to serve the tensor v at the point g. -/
def ServesSlice (v : Tensor) (g : List E) (slice : Array E) : Prop :=
  ∀ hk, hk < 2 ^ (keptVars g.length v.denseVars).length →
    ρ.val (slice.getD hk zeroE) =
      foldedVal (v.sliceVal ρ) g.length (fun d => ρ.val (g.getD d zeroE)) v.denseVars 0 0 hk

/-- Tensor.fixLowWith with a slice that serves v at g (ServesSlice): entry p reads as the sum of
Tensor.fixLow_val, under the same two conditions. -/
theorem Tensor.fixLowWith_val (v : Tensor) (g : List E) (hg : g.length ≤ v.vars)
    (hok : v.InOrder) (slice : Array E) (hs : ServesSlice ρ v g slice) (p : Nat) :
    ρ.val ((v.fixLowWith g slice).entry p) =
      ((List.range (2 ^ g.length)).map fun b =>
        eqVal ρ g b * ρ.val (v.entry (b + 2 ^ g.length * p))).sum := by
  obtain ⟨hn, h1⟩ := hok
  obtain ⟨f1, f2⟩ := fixPairs_val ρ v.pairs g v.scalar
  rw [Tensor.sum_low ρ v g hg hn h1 p, ← hs _ (denseIndex_lt _ p)]
  unfold Tensor.fixLowWith
  dsimp only
  have hkv : (v.denseVars.filter (g.length ≤ ·)).map (· - g.length) =
      keptVars g.length v.denseVars := rfl
  rw [hkv]
  by_cases he : (keptVars g.length v.denseVars).isEmpty = true
  · have e0 : keptVars g.length v.denseVars = [] := by simpa using he
    rw [if_pos he, Tensor.entry_val, e0]
    show ρ.val (mulE (fixPairs v.pairs g v.scalar).1 (slice.getD 0 zeroE)) *
      pairsVal ρ (fixPairs v.pairs g v.scalar).2 p * 1 = _
    rw [ρ.mul, f1, f2]
    simp only [denseIndex]
    ring
  · rw [if_neg he, Tensor.entry_val]
    show ρ.val (fixPairs v.pairs g v.scalar).1 * pairsVal ρ (fixPairs v.pairs g v.scalar).2 p *
      (if (keptVars g.length v.denseVars).isEmpty then 1
        else ρ.val (slice.getD (0 + denseIndex (keptVars g.length v.denseVars) 0 p) zeroE)) = _
    rw [if_neg he, f1, f2, Nat.zero_add]

/-- A tensor's own folded slice serves it. -/
theorem Tensor.foldedSlice_serves (v : Tensor) (g : List E) (he : v.denseVars.isEmpty = false) :
    ServesSlice ρ v g (v.foldedSlice g) :=
  fun hk hh => Tensor.foldedSlice_val ρ v g he hk hh

/-- A tensor whose slice is cut has dense variables. -/
theorem Tensor.dense_of_cut (v : Tensor) (n : Nat) (h : v.sliceIsCut n = true) :
    v.denseVars.isEmpty = false := by
  unfold Tensor.sliceIsCut at h
  cases hd : v.denseVars with
  | nil => rw [hd] at h; cases h
  | cons _ _ => rfl

/-- Fixing the lowest variables of a tensor at the point g: entry p of the result reads as the sum,
over the numbers b below 2^|g|, of the weight of b at g times entry b + 2^|g| p of the tensor. The
tensor must have at least |g| variables and be in order (Tensor.InOrder). -/
theorem Tensor.fixLow_val (v : Tensor) (g : List E) (hg : g.length ≤ v.vars) (hok : v.InOrder)
    (p : Nat) :
    ρ.val ((v.fixLow g).entry p) =
      ((List.range (2 ^ g.length)).map fun b =>
        eqVal ρ g b * ρ.val (v.entry (b + 2 ^ g.length * p))).sum := by
  by_cases hc : v.sliceIsCut g.length = true
  · have e : v.fixLow g = v.fixLowWith g (v.foldedSlice g) := by
      unfold Tensor.fixLow
      rw [if_pos hc]
    rw [e]
    exact Tensor.fixLowWith_val ρ v g hg hok _
      (Tensor.foldedSlice_serves ρ v g (v.dense_of_cut _ hc)) p
  · exact Tensor.fixLow_val_uncut ρ v g hg hok (by simpa using hc) p

/-! ## Single entries -/

/-- One step of eqWeight, as an equation between functions of the index and the factor (why so:
pairsAt_cons_fun, OnBytes/Iop/TensorLaws.lean). -/
theorem eqWeight_cons_fun (x : E) (xs : List E) :
    eqWeight (x :: xs) =
      fun j r => eqWeight xs (j / 2) (mulE r (if j % 2 == 1 then x else subE oneE x)) := rfl

/-- Without coordinates eqWeight returns the factor. -/
theorem eqWeight_nil_fun : eqWeight [] = fun _ r => r := rfl

/-- eqWeight reads as the factor times the weight of the index at the point. -/
theorem eqWeight_val : ∀ (g : List E) (j : Nat) (r : E),
    ρ.val (eqWeight g j r) = ρ.val r * eqVal ρ g j
  | [], j, r => by
    rw [eqWeight_nil_fun, eqVal_nil, mul_one]
  | x :: xs, j, r => by
    rw [eqWeight_cons_fun]
    dsimp only
    rw [eqWeight_val xs, ρ.mul, eqVal_cons]
    by_cases h : j % 2 = 1
    · simp only [h, beq_self_eq_true, if_true]
      ring
    · have : (j % 2 == 1) = false := by simpa using h
      simp only [h, this, Bool.false_eq_true, if_false, ρ.sub, ρ.one]
      ring

/-- The weight of an index at a point depends only on its low |g| bits. -/
theorem eqVal_mod (g : List E) (j : Nat) : eqVal ρ g (j % 2 ^ g.length) = eqVal ρ g j := by
  have h := pairsVal_mod ρ (g.map fun x => (subE oneE x, x)) j
  rw [List.length_map] at h
  exact h

/-- What the single entries of a list read as, together, at an index. -/
def entSum (j : Nat) (l : List (Nat × E)) : K :=
  (l.map fun e => if e.1 = j then ρ.val e.2 else 0).sum

/-- One step of the loop of mergeEntries. -/
def mergeStep (acc : List (Nat × E)) (a : Nat × E) : List (Nat × E) :=
  match acc with
  | b :: r => if a.1 == b.1 then (b.1, addE b.2 a.2) :: r else a :: acc
  | [] => [a]

/-- mergeEntries, with the step of its loop written as mergeStep. -/
theorem mergeEntries_eq (l : List (Nat × E)) :
    mergeEntries l = ((l.mergeSort fun a b => a.1 ≤ b.1).foldl mergeStep []).reverse := rfl

/-- The loop of mergeEntries keeps what the entries read as at every index. -/
theorem entSum_mergeLoop (j : Nat) : ∀ (l acc : List (Nat × E)),
    entSum ρ j (l.foldl mergeStep acc) = entSum ρ j acc + entSum ρ j l
  | [], acc => by simp [entSum]
  | a :: l, acc => by
    rw [List.foldl_cons, entSum_mergeLoop j l]
    cases acc with
    | nil => simp [entSum, mergeStep]
    | cons b r =>
      by_cases h : a.1 = b.1
      · simp only [mergeStep, h, beq_self_eq_true, if_true, entSum, List.map_cons, List.sum_cons,
          ρ.add]
        split <;> ring
      · have : (a.1 == b.1) = false := by simpa using h
        simp only [mergeStep, this, Bool.false_eq_true, if_false, entSum, List.map_cons,
          List.sum_cons]
        ring

/-- mergeEntries keeps what the entries read as at every index. -/
theorem entSum_mergeEntries (j : Nat) (l : List (Nat × E)) :
    entSum ρ j (mergeEntries l) = entSum ρ j l := by
  rw [mergeEntries_eq]
  have hp : (l.mergeSort fun a b => a.1 ≤ b.1).Perm l := List.mergeSort_perm _ _
  have e1 : ∀ m : List (Nat × E), entSum ρ j m.reverse = entSum ρ j m := by
    intro m
    unfold entSum
    rw [List.map_reverse, List.sum_reverse]
  rw [e1, entSum_mergeLoop]
  unfold entSum
  rw [(hp.map _).sum_eq]
  simp

/-! ## Slices that are folded once and shared -/

/-- What a slice becomes depends only on the slice's own entries. -/
theorem foldedVal_congr (A A' : Nat → K) (m : Nat) (x : Nat → K) :
    ∀ (ds : List Nat) (i low hk : Nat), low < 2 ^ i →
    (∀ t, t < 2 ^ (i + ds.length) → A t = A' t) →
    foldedVal A m x ds i low hk = foldedVal A' m x ds i low hk
  | [], i, low, _, hl, h => h low (by simpa using hl)
  | d :: ds, i, low, hk, hl, h => by
    have h' : ∀ t, t < 2 ^ (i + 1 + ds.length) → A t = A' t := by
      intro t ht
      exact h t (by rw [List.length_cons, show i + (ds.length + 1) = i + 1 + ds.length by omega]
                    exact ht)
    have hb := Nat.mod_lt hk (by decide : 0 < 2)
    have hmul : hk % 2 * 2 ^ i ≤ 2 ^ i := by
      calc hk % 2 * 2 ^ i ≤ 1 * 2 ^ i := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ i := Nat.one_mul _
    simp only [foldedVal]
    rw [foldedVal_congr A A' m x ds (i + 1) low hk (by rw [Nat.pow_succ]; omega) h',
      foldedVal_congr A A' m x ds (i + 1) (low + 2 ^ i) hk (by rw [Nat.pow_succ]; omega) h',
      foldedVal_congr A A' m x ds (i + 1) (low + hk % 2 * 2 ^ i) (hk / 2)
        (by rw [Nat.pow_succ]; omega) h']

/-- A condition that holds of all numbers below n. -/
theorem all_below : ∀ (n : Nat) (f : Nat → Bool), (Nat.all n fun i _ => f i) = true →
    ∀ i, i < n → f i = true
  | 0, _, _, _, h => by omega
  | n + 1, f, h, i, hi => by
    rw [Nat.all_succ, Bool.and_eq_true] at h
    by_cases e : i = n
    · rw [e]; exact h.2
    · exact all_below n f h.1 i (by omega)

/-- If w has the same key and the same slice as v, and has dense variables, then w's folded slice
serves v. -/
theorem serves_of_same (v w : Tensor) (g : List E) (hk : w.sliceKey = v.sliceKey)
    (hs : v.sameSlice w = true) (he : w.denseVars.isEmpty = false) :
    ServesSlice ρ v g (w.foldedSlice g) := by
  unfold Tensor.sliceKey at hk
  dsimp only at hk
  have h1 : w.first = v.first := congrArg Prod.fst hk
  have h2 : w.denseVars = v.denseVars := congrArg (fun q => q.2.1) hk
  intro t ht
  rw [← h2] at ht
  rw [Tensor.foldedSlice_val ρ w g he t ht, h2]
  apply foldedVal_congr _ _ _ _ _ _ _ _ (by simp)
  intro u hu
  rw [Nat.zero_add] at hu
  unfold Tensor.sameSlice at hs
  have e := all_below _ (fun i => v.values.getD (v.first + i) zeroE ==
    w.values.getD (v.first + i) zeroE) hs u hu
  unfold Tensor.sliceVal
  rw [h2, h1, beq_iff_eq.1 e]

/-- What holds of the table of folded slices during a call of Form.fixLow: each stored tensor is
under its own key, has dense variables, and is stored with its own slice folded at g. -/
def SlicesOk (g : List E) (M : Form.FoldedSlices) : Prop :=
  ∀ key (c : Tensor × Array E), M[key]? = some c → c.1.sliceKey = key ∧ c.2 = c.1.foldedSlice g ∧
    c.1.denseVars.isEmpty = false

/-- One step of the loop of Form.fixLow, from a table that is SlicesOk and for a tensor that meets
the conditions of Tensor.fixLow_val: the table stays SlicesOk, and one tensor is added, whose entry
p reads as the sum of Tensor.fixLow_val. -/
theorem fixLowShared_val (g : List E) (s : List Tensor × Form.FoldedSlices) (v : Tensor)
    (hM : SlicesOk g s.2) (hg : g.length ≤ v.vars) (hok : v.InOrder) (p : Nat) :
    SlicesOk g (Form.fixLowShared g s v).2 ∧
      ∃ t, (Form.fixLowShared g s v).1 = t :: s.1 ∧
        ρ.val (t.entry p) = ((List.range (2 ^ g.length)).map fun b =>
          eqVal ρ g b * ρ.val (v.entry (b + 2 ^ g.length * p))).sum := by
  unfold Form.fixLowShared
  by_cases hc : v.sliceIsCut g.length = true
  · rw [if_pos hc]
    dsimp only
    cases hf : s.2[v.sliceKey]? with
    | some c =>
      obtain ⟨k1, k2, k3⟩ := hM _ c hf
      refine ⟨hM, _, rfl, ?_⟩
      by_cases hsame : v.sameSlice c.1 = true
      · rw [if_pos hsame, k2]
        exact Tensor.fixLowWith_val ρ v g hg hok _ (serves_of_same ρ v c.1 g k1 hsame k3) p
      · rw [if_neg hsame]
        exact Tensor.fixLowWith_val ρ v g hg hok _
          (Tensor.foldedSlice_serves ρ v g (v.dense_of_cut _ hc)) p
    | none =>
      refine ⟨?_, _, rfl, Tensor.fixLowWith_val ρ v g hg hok _
        (Tensor.foldedSlice_serves ρ v g (v.dense_of_cut _ hc)) p⟩
      intro key c hcm
      rw [Std.HashMap.getElem?_insertIfNew] at hcm
      split at hcm
      · rename_i hk
        have ek : v.sliceKey = key := by simpa using hk.1
        have ec : (v, v.foldedSlice g) = c := by simpa using hcm
        rw [← ec]
        exact ⟨ek, rfl, v.dense_of_cut _ hc⟩
      · exact hM key c hcm
  · rw [if_neg hc]
    exact ⟨hM, _, rfl, Tensor.fixLow_val ρ v g hg hok p⟩

/-! ## Fixing the lowest variables of a form -/

/-- The sum, over the numbers b below 2^|g|, of the weight of b at g times F (b + 2^|g| p). -/
def lowSum (g : List E) (p : Nat) (F : Nat → K) : K :=
  ((List.range (2 ^ g.length)).map fun b => eqVal ρ g b * F (b + 2 ^ g.length * p)).sum

/-- The sum over the low bits is additive. -/
theorem lowSum_add (g : List E) (p : Nat) (F G : Nat → K) :
    lowSum ρ g p (fun j => F j + G j) = lowSum ρ g p F + lowSum ρ g p G := by
  unfold lowSum
  rw [← List.sum_map_add]
  exact congrArg List.sum (List.map_congr_left fun b _ => by ring)

/-- A constant factor comes out of the sum over the low bits. -/
theorem lowSum_mul (g : List E) (p : Nat) (F : Nat → K) (c : K) :
    lowSum ρ g p (fun j => F j * c) = lowSum ρ g p F * c := by
  unfold lowSum
  rw [← List.sum_map_mul_right]
  exact congrArg List.sum (List.map_congr_left fun b _ => by ring)

/-- The sum over the low bits of 0 is 0. -/
theorem lowSum_zero (g : List E) (p : Nat) : lowSum ρ g p (fun _ => 0) = 0 := by
  unfold lowSum
  simp

/-- The loop of Form.fixLow over the tensors. -/
theorem fixLow_loop (g : List E) (times : E) (p : Nat) :
    ∀ (l : List Tensor) (s : List Tensor × Form.FoldedSlices), SlicesOk g s.2 →
    (∀ v ∈ l, g.length ≤ v.vars ∧ v.InOrder) →
    (((l.foldl (fun s v => Form.fixLowShared g s (v.scale times)) s).1).map fun t =>
      ρ.val (t.entry p)).sum =
      (s.1.map fun t => ρ.val (t.entry p)).sum +
        lowSum ρ g p (fun j => (l.map fun v => ρ.val (v.entry j)).sum) * ρ.val times
  | [], s, _, _ => by simp [lowSum_zero]
  | v :: l, s, hM, hl => by
    obtain ⟨hg, hok⟩ := hl v (by simp)
    obtain ⟨hM', t, e1, e2⟩ := fixLowShared_val ρ g s (v.scale times) hM
      (by rw [Tensor.vars_scale]; exact hg) (hok.scale times) p
    rw [List.foldl_cons, fixLow_loop g times p l _ hM' (fun w hw => hl w (by simp [hw])), e1,
      List.map_cons, List.sum_cons, e2]
    simp only [List.map_cons, List.sum_cons, Tensor.entry_scale]
    rw [lowSum_add]
    have e3 : ((List.range (2 ^ g.length)).map fun b =>
        eqVal ρ g b * (ρ.val (v.entry (b + 2 ^ g.length * p)) * ρ.val times)).sum =
        lowSum ρ g p (fun j => ρ.val (v.entry j)) * ρ.val times := by
      rw [← lowSum_mul]
      rfl
    rw [e3]
    ring

/-- One single entry, summed over the low bits of the index. -/
theorem lowSum_single (g : List E) (p idx : Nat) (c : K) :
    lowSum ρ g p (fun j => if idx = j then c else 0) =
      if idx / 2 ^ g.length = p then eqVal ρ g idx * c else 0 := by
  unfold lowSum
  have hp := Nat.two_pow_pos g.length
  have term : ∀ b ∈ List.range (2 ^ g.length),
      eqVal ρ g b * (if idx = b + 2 ^ g.length * p then c else 0) =
      if b = idx % 2 ^ g.length then
        (if idx / 2 ^ g.length = p then eqVal ρ g b * c else 0) else 0 := by
    intro b hb
    have hb' := List.mem_range.1 hb
    have d := Nat.mod_add_div idx (2 ^ g.length)
    by_cases h : idx = b + 2 ^ g.length * p
    · have e1 : idx % 2 ^ g.length = b := by
        rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb']
      have e2 : idx / 2 ^ g.length = p := by
        rw [h, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hb', Nat.zero_add]
      rw [if_pos h, if_pos e1.symm, if_pos e2]
    · rw [if_neg h, mul_zero]
      by_cases e1 : b = idx % 2 ^ g.length
      · rw [if_pos e1]
        have e2 : ¬ idx / 2 ^ g.length = p := by
          intro e2
          apply h
          rw [e1, ← e2]
          exact d.symm
        rw [if_neg e2]
      · rw [if_neg e1]
  rw [List.map_congr_left term, sum_range_single, if_pos (Nat.mod_lt _ hp), eqVal_mod]

/-- The single entries of a form, fixed at g. -/
theorem entSum_fixed (g : List E) (times : E) (p : Nat) : ∀ l : List (Nat × E),
    entSum ρ p (l.map fun e => (e.1 / 2 ^ g.length, mulE (eqWeight g e.1 e.2) times)) =
      lowSum ρ g p (fun j => entSum ρ j l) * ρ.val times
  | [] => by simp [entSum, lowSum_zero]
  | e :: l => by
    have ih := entSum_fixed g times p l
    unfold entSum at ih ⊢
    simp only [List.map_cons, List.sum_cons]
    rw [ih, lowSum_add, lowSum_single, ρ.mul, eqWeight_val]
    split <;> ring

/-- Fixing the lowest variables of a form at the point g, with the factor times: entry p of the
result reads as times times the sum, over the numbers b below 2^|g|, of the weight of b at g times
entry b + 2^|g| p of the form. Every tensor of the form must be in order and have at least |g|
variables (Form.fixLow_val_of_fits: a form that fits has such tensors). -/
theorem Form.fixLow_val (f : Form) (g : List E) (times : E)
    (hf : ∀ v ∈ f.tensors, g.length ≤ v.vars ∧ v.InOrder) (p : Nat) :
    ρ.val ((f.fixLow g times).entry p) =
      lowSum ρ g p (fun j => ρ.val (f.entry j)) * ρ.val times := by
  rw [Form.entry_val]
  unfold Form.fixLow
  dsimp only
  have h0 : SlicesOk g ({} : Form.FoldedSlices) := by
    intro key c hc
    simp at hc
  have ht := fixLow_loop ρ g times p f.tensors ([], {}) h0 hf
  have he := entSum_mergeEntries ρ p
    (f.entries.map fun e => (e.1 / 2 ^ g.length, mulE (eqWeight g e.1 e.2) times))
  rw [entSum_fixed] at he
  unfold entSum at he
  rw [List.map_reverse, List.sum_reverse, ht, he]
  simp only [Form.entry_val, List.map_nil, List.sum_nil, zero_add]
  rw [lowSum_add]
  ring

/-- The tensors of a form, each fixed by itself. -/
theorem fixLowPlain_loop (g : List E) (times : E) (p : Nat) : ∀ l : List Tensor,
    (∀ v ∈ l, g.length ≤ v.vars ∧ v.InOrder) →
    ((l.map fun v => (v.scale times).fixLow g).map fun t => ρ.val (t.entry p)).sum =
      lowSum ρ g p (fun j => (l.map fun v => ρ.val (v.entry j)).sum) * ρ.val times
  | [], _ => by simp [lowSum_zero]
  | v :: l, hl => by
    obtain ⟨hg, hok⟩ := hl v (by simp)
    simp only [List.map_cons, List.sum_cons]
    rw [fixLowPlain_loop g times p l (fun w hw => hl w (by simp [hw])),
      Tensor.fixLow_val ρ (v.scale times) g (by rw [Tensor.vars_scale]; exact hg)
        (hok.scale times) p, lowSum_add]
    simp only [Tensor.entry_scale]
    have e3 : ((List.range (2 ^ g.length)).map fun b =>
        eqVal ρ g b * (ρ.val (v.entry (b + 2 ^ g.length * p)) * ρ.val times)).sum =
        lowSum ρ g p (fun j => ρ.val (v.entry j)) * ρ.val times := by
      rw [← lowSum_mul]
      rfl
    rw [e3]
    ring

/-- Form.fixLowPlain reads as the same sum as Form.fixLow (Form.fixLow_val), under the same
condition: every tensor of the form is in order and has at least |g| variables. -/
theorem Form.fixLowPlain_val (f : Form) (g : List E) (times : E)
    (hf : ∀ v ∈ f.tensors, g.length ≤ v.vars ∧ v.InOrder) (p : Nat) :
    ρ.val ((f.fixLowPlain g times).entry p) =
      lowSum ρ g p (fun j => ρ.val (f.entry j)) * ρ.val times := by
  rw [Form.entry_val]
  unfold Form.fixLowPlain
  dsimp only
  have he := entSum_mergeEntries ρ p
    (f.entries.map fun e => (e.1 / 2 ^ g.length, mulE (eqWeight g e.1 e.2) times))
  rw [entSum_fixed] at he
  unfold entSum at he
  rw [fixLowPlain_loop ρ g times p f.tensors hf, he]
  simp only [Form.entry_val]
  rw [lowSum_add]
  ring

/-- Form.fixLow_val for a form that fits a vector of 2^n entries (Form.fits), with |g| at most n. -/
theorem Form.fixLow_val_of_fits (f : Form) (n : Nat) (h : f.fits n = true) (g : List E)
    (hg : g.length ≤ n) (times : E) (p : Nat) :
    ρ.val ((f.fixLow g times).entry p) =
      lowSum ρ g p (fun j => ρ.val (f.entry j)) * ρ.val times := by
  apply Form.fixLow_val
  intro v hv
  unfold Form.fits at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨e1, e2⟩ := h.1 v hv
  exact ⟨by rw [e1]; exact hg, v.inOrder_of_ok e2⟩

/-! ## The result of fixing: so that the laws can be used one after the other -/

/-- The dense variables that are left are named once each. -/
theorem nodup_keptVars (m : Nat) (ds : List Nat) (h : ds.Nodup) : (keptVars m ds).Nodup := by
  unfold keptVars
  refine List.Nodup.map_on ?_ (h.filter _)
  intro a ha b hb e
  have ha' : m ≤ a := by simpa using (List.mem_filter.1 ha).2
  have hb' : m ≤ b := by simpa using (List.mem_filter.1 hb).2
  omega

/-- A dense variable that is left was a dense variable, m higher. -/
theorem mem_keptVars (m : Nat) (ds : List Nat) (d : Nat) (h : d ∈ keptVars m ds) : d + m ∈ ds := by
  unfold keptVars at h
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
  have ha' : m ≤ a := by simpa using (List.mem_filter.1 ha).2
  rw [Nat.sub_add_cancel ha']
  exact (List.mem_filter.1 ha).1

/-- If v is in order, so is v fixed with any slice; it has |g| variables fewer (none if it had fewer
than |g|). The slice plays no part in this. -/
theorem Tensor.fixLowWith_shape (v : Tensor) (g : List E) (slice : Array E) (hok : v.InOrder) :
    (v.fixLowWith g slice).vars = v.vars - g.length ∧ (v.fixLowWith g slice).InOrder := by
  have f2 : (fixPairs v.pairs g v.scalar).2 = v.pairs.drop g.length := by
    cases hg : g with
    | nil => rw [fixPairs_nil_right_fun]; rfl
    | cons x xs => exact (fixPairs_drop v.pairs (x :: xs) v.scalar)
  unfold Tensor.fixLowWith
  dsimp only
  have hkv : (v.denseVars.filter (g.length ≤ ·)).map (· - g.length) =
      keptVars g.length v.denseVars := rfl
  rw [hkv]
  by_cases he : (keptVars g.length v.denseVars).isEmpty = true
  · rw [if_pos he]
    refine ⟨?_, List.nodup_nil, fun d hd => by cases hd⟩
    show (fixPairs v.pairs g v.scalar).2.length = _
    rw [f2, List.length_drop]
    rfl
  · rw [if_neg he]
    refine ⟨?_, nodup_keptVars _ _ hok.1, fun d hd => ?_⟩
    · show (fixPairs v.pairs g v.scalar).2.length = _
      rw [f2, List.length_drop]
      rfl
    · show (fixPairs v.pairs g v.scalar).2[d]? = _
      rw [f2, List.getElem?_drop, Nat.add_comm]
      exact hok.2 _ (mem_keptVars _ _ _ hd)

/-- If v is in order, so is v with its lowest variables fixed; it has |g| variables fewer (none if
it had fewer than |g|). -/
theorem Tensor.fixLow_shape (v : Tensor) (g : List E) (hok : v.InOrder) :
    (v.fixLow g).vars = v.vars - g.length ∧ (v.fixLow g).InOrder := by
  by_cases hc : v.sliceIsCut g.length = true
  · have e : v.fixLow g = v.fixLowWith g (v.foldedSlice g) := by
      unfold Tensor.fixLow
      rw [if_pos hc]
    rw [e]
    exact Tensor.fixLowWith_shape v g _ hok
  · have hc' : v.sliceIsCut g.length = false := by simpa using hc
    have hall : ∀ d ∈ v.denseVars, g.length ≤ d := by
      intro d hd
      unfold Tensor.sliceIsCut at hc'
      have := List.any_eq_false.1 hc' d hd
      simpa using this
    have hk : v.denseVars.map (· - g.length) = keptVars g.length v.denseVars := by
      unfold keptVars
      rw [List.filter_eq_self.2 (fun d hd => by simpa using hall d hd)]
    unfold Tensor.fixLow
    simp only [hc', Bool.false_eq_true, if_false]
    refine ⟨?_, ?_, fun d hd => ?_⟩
    · show (fixPairs v.pairs g v.scalar).2.length = _
      rw [fixPairs_drop, List.length_drop]
      rfl
    · show (v.denseVars.map (· - g.length)).Nodup
      rw [hk]
      exact nodup_keptVars _ _ hok.1
    · have hd' : d ∈ keptVars g.length v.denseVars := by
        rw [← hk]
        exact hd
      show (fixPairs v.pairs g v.scalar).2[d]? = _
      rw [fixPairs_drop, List.getElem?_drop, Nat.add_comm]
      exact hok.2 _ (mem_keptVars _ _ _ hd')

/-- One step of the loop of Form.fixLow, for a tensor in order: it adds one tensor, which has |g|
variables fewer and is in order. -/
theorem fixLowShared_shape (g : List E) (s : List Tensor × Form.FoldedSlices) (v : Tensor)
    (hok : v.InOrder) :
    ∃ t, (Form.fixLowShared g s v).1 = t :: s.1 ∧ t.vars = v.vars - g.length ∧ t.InOrder := by
  unfold Form.fixLowShared
  by_cases hc : v.sliceIsCut g.length = true
  · rw [if_pos hc]
    dsimp only
    cases s.2[v.sliceKey]? with
    | some c => exact ⟨_, rfl, Tensor.fixLowWith_shape v g _ hok⟩
    | none => exact ⟨_, rfl, Tensor.fixLowWith_shape v g _ hok⟩
  · rw [if_neg hc]
    exact ⟨_, rfl, Tensor.fixLow_shape v g hok⟩

/-- The loop of Form.fixLow keeps a condition on shapes. -/
theorem fixLow_loop_shape (g : List E) (times : E) (n : Nat) :
    ∀ (l : List Tensor) (s : List Tensor × Form.FoldedSlices),
    (∀ v ∈ l, v.vars = n ∧ v.InOrder) → (∀ t ∈ s.1, t.vars = n - g.length ∧ t.InOrder) →
    ∀ t ∈ (l.foldl (fun s v => Form.fixLowShared g s (v.scale times)) s).1,
      t.vars = n - g.length ∧ t.InOrder
  | [], _, _, hs => hs
  | v :: l, s, hl, hs => by
    obtain ⟨hv, hok⟩ := hl v (by simp)
    obtain ⟨t, e1, e2, e3⟩ := fixLowShared_shape g s (v.scale times) (hok.scale times)
    rw [List.foldl_cons]
    apply fixLow_loop_shape g times n l _ (fun w hw => hl w (by simp [hw]))
    intro u hu
    rw [e1] at hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ⟨by rw [e2, Tensor.vars_scale, hv], e3⟩
    · exact hs u hu

/-- The tensors of a form with its lowest variables fixed: if all tensors of the form have n
variables and are in order, all tensors of the result have n - |g| variables and are in order.
These are the conditions of Form.dot_val (at n - |g| variables) and, for a further point of at most
n - |g| coordinates, of Form.fixLow_val: so the laws can be used on the result. Not shown: that the
result passes Form.fits, which also asks that each slice is inside its vector and each single
entry's index is below 2 to the number of variables. -/
theorem Form.fixLow_shape (f : Form) (g : List E) (times : E) (n : Nat)
    (hf : ∀ v ∈ f.tensors, v.vars = n ∧ v.InOrder) :
    ∀ t ∈ (f.fixLow g times).tensors, t.vars = n - g.length ∧ t.InOrder := by
  intro t ht
  unfold Form.fixLow at ht
  dsimp only at ht
  exact fixLow_loop_shape g times n f.tensors ([], {}) hf (by simp) t (List.mem_reverse.1 ht)

end OnBytes

#print axioms OnBytes.Tensor.fixLow_val
#print axioms OnBytes.Form.fixLow_val
#print axioms OnBytes.Form.fixLowPlain_val
#print axioms OnBytes.Form.fixLow_val_of_fits
#print axioms OnBytes.Form.fixLow_shape
