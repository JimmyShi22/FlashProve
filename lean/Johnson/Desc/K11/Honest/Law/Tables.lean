-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K11/Honest/Law/Tables.lean: the lists of Johnson/Desc/K11/Honest/Summand.lean, READ:
what `productRound`, `roundAt`, `endAt` and `claimedSum` are worth under a reading, in terms of the
plain product sum of two tables. Lemmas with their proofs. No frame, no verifier's text.

A reading (`Reading K`, OnBytes/Model/HideLaws.lean) takes the program's 0, 1, sum, difference and
product to K's.

The chief names:
  `tableDot ρ a b`     the sum of the products of two tables' entries, as read
  `termsDot ρ ts rs`   over all terms: the coefficient times `tableDot` of the tables, bound at rs
  `foldAdd_read`       a fold of sums, read
  `dot_halves`         `tableDot` of two tables of one even length, over their halves' pairs
  `dot_bindTop`        `tableDot` of two tables bound at r, over their halves' pairs
  `productRound_read`  `productRound` is a list of three; its sum; its value at r
  `roundAt_read`       `roundAt` is a list of three; twice the first and the two others add up to
                       `termsDot` at rs; the polynomial at r is `termsDot` at rs ++ [r]
  `claimedSum_read`, `endAt_read`   the two ends: `termsDot` at no challenge; at all
  `bindTop_length`, `bindAll_length`   the lengths

Limits. The tables' lengths are premises. Nothing on any property.

-/
import Johnson.Desc.K11.Honest.Summand
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Honest
open OnBytes (E addE subE mulE zeroE)
open OnBytes.Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The sum of the products of two tables' entries, as read. -/
def tableDot (a b : List E) : K := ((a.zip b).map fun y => ρ.val y.1 * ρ.val y.2).sum

/-- Over all terms: the coefficient times the product sum of the term's two tables, bound at rs. -/
def termsDot (ts : List Term) (rs : List E) : K :=
  (ts.map fun t => ρ.val t.coef * tableDot ρ (bindAll rs t.a) (bindAll rs t.b)).sum

/-- A fold of sums, read. -/
theorem foldAdd_read {α : Type} (f : α → E) : ∀ (l : List α) (z : E),
    ρ.val (l.foldl (fun s t => addE s (f t)) z) = ρ.val z + (l.map fun t => ρ.val (f t)).sum
  | [], z => by simp
  | x :: l, z => by
    rw [List.foldl_cons, foldAdd_read f l, ρ.add, List.map_cons, List.sum_cons]
    ring

/-- The halves of a table, pair by pair. -/
def tableHalves (a : List E) : List (E × E) := (a.take (a.length / 2)).zip (a.drop (a.length / 2))

/-- Four lists of one length: two product sums are one sum over the pairs of pairs. -/
theorem four_lists (F : E × E → K) : ∀ (l1 l2 l3 l4 : List E), l1.length = l2.length →
    l1.length = l3.length → l1.length = l4.length →
    ((l1.zip l3).map F).sum + ((l2.zip l4).map F).sum =
      (((l1.zip l2).zip (l3.zip l4)).map fun y => F (y.1.1, y.2.1) + F (y.1.2, y.2.2)).sum
  | [], [], [], [], _, _, _ => by simp
  | x1 :: l1, x2 :: l2, x3 :: l3, x4 :: l4, h2, h3, h4 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h2 h3 h4
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    rw [← four_lists F l1 l2 l3 l4 h2 h3 h4]
    ring
  | [], _ :: _, _, _, h, _, _ => by simp at h
  | [], [], _ :: _, _, _, h, _ => by simp at h
  | [], [], [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, h, _ => by simp at h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => by simp at h

/-- The product sum of two tables of one even length, over their halves' pairs. -/
theorem dot_halves (a b : List E) (h : Nat) (ha : a.length = 2 * h) (hb : b.length = 2 * h) :
    tableDot ρ a b = (((tableHalves a).zip (tableHalves b)).map fun y =>
      ρ.val y.1.1 * ρ.val y.2.1 + ρ.val y.1.2 * ρ.val y.2.2).sum := by
  have ea : a.length / 2 = h := by omega
  have eb : b.length / 2 = h := by omega
  have h1 : (a.take h).length = h := by rw [List.length_take]; omega
  have h2 : (a.drop h).length = h := by rw [List.length_drop]; omega
  have h3 : (b.take h).length = h := by rw [List.length_take]; omega
  have h4 : (b.drop h).length = h := by rw [List.length_drop]; omega
  unfold tableDot tableHalves
  rw [ea, eb]
  have key := four_lists (fun y : E × E => ρ.val y.1 * ρ.val y.2) (a.take h) (a.drop h) (b.take h)
    (b.drop h) (by rw [h1, h2]) (by rw [h1, h3]) (by rw [h1, h4])
  rw [← key, ← List.sum_append, ← List.map_append, ← List.zip_append (by rw [h1, h3]),
    List.take_append_drop, List.take_append_drop]

/-- The product sum of two tables bound at r, over their halves' pairs. -/
theorem dot_bindTop (r : E) (a b : List E) :
    tableDot ρ (bindTop r a) (bindTop r b) = (((tableHalves a).zip (tableHalves b)).map fun y =>
      (ρ.val y.1.1 + ρ.val r * (ρ.val y.1.2 - ρ.val y.1.1)) *
        (ρ.val y.2.1 + ρ.val r * (ρ.val y.2.2 - ρ.val y.2.1))).sum := by
  unfold tableDot bindTop
  show (((((tableHalves a).map _).zip ((tableHalves b).map _))).map _).sum = _
  rw [List.zip_map, List.map_map]
  congr 1
  refine List.map_congr_left fun y _ => ?_
  simp only [Function.comp, Prod.map, ρ.add, ρ.mul, ρ.sub]

/-- Three sums over one list, under three factors, are one sum. -/
theorem sums_under_three {α : Type} (f0 f1 f2 : α → K) (c0 c1 c2 : K) : ∀ l : List α,
    c0 * (l.map f0).sum + c1 * (l.map f1).sum + c2 * (l.map f2).sum =
      (l.map fun y => c0 * f0 y + c1 * f1 y + c2 * f2 y).sum
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons]
    rw [← sums_under_three f0 f1 f2 c0 c1 c2 l]
    ring

/-- One step of `productRound`'s fold. -/
def productStep (g : List E) (y : (E × E) × (E × E)) : List E :=
  [addE (g.getD 0 zeroE) (mulE y.1.1 y.2.1),
   addE (g.getD 1 zeroE)
     (addE (mulE y.1.1 (subE y.2.2 y.2.1)) (mulE (subE y.1.2 y.1.1) y.2.1)),
   addE (g.getD 2 zeroE) (mulE (subE y.1.2 y.1.1) (subE y.2.2 y.2.1))]

/-- `productRound` as a fold of `productStep` over the halves' pairs. -/
theorem productRound_eq (a b : List E) :
    productRound a b =
      ((tableHalves a).zip (tableHalves b)).foldl productStep [zeroE, zeroE, zeroE] := rfl

/-- The fold of `productRound`, from any three coefficients on. -/
theorem productFold_read : ∀ (z : List ((E × E) × (E × E))) (g0 g1 g2 : E),
    ∃ x0 x1 x2 : E, z.foldl productStep [g0, g1, g2] = [x0, x1, x2] ∧
      ρ.val x0 = ρ.val g0 + (z.map fun y => ρ.val y.1.1 * ρ.val y.2.1).sum ∧
      ρ.val x1 = ρ.val g1 + (z.map fun y => ρ.val y.1.1 * (ρ.val y.2.2 - ρ.val y.2.1) +
        (ρ.val y.1.2 - ρ.val y.1.1) * ρ.val y.2.1).sum ∧
      ρ.val x2 = ρ.val g2 + (z.map fun y => (ρ.val y.1.2 - ρ.val y.1.1) *
        (ρ.val y.2.2 - ρ.val y.2.1)).sum
  | [], g0, g1, g2 => ⟨g0, g1, g2, rfl, by simp, by simp, by simp⟩
  | y :: z, g0, g1, g2 => by
    obtain ⟨x0, x1, x2, h, e0, e1, e2⟩ := productFold_read z
      (addE g0 (mulE y.1.1 y.2.1))
      (addE g1 (addE (mulE y.1.1 (subE y.2.2 y.2.1)) (mulE (subE y.1.2 y.1.1) y.2.1)))
      (addE g2 (mulE (subE y.1.2 y.1.1) (subE y.2.2 y.2.1)))
    have hs : productStep [g0, g1, g2] y =
        [addE g0 (mulE y.1.1 y.2.1),
         addE g1 (addE (mulE y.1.1 (subE y.2.2 y.2.1)) (mulE (subE y.1.2 y.1.1) y.2.1)),
         addE g2 (mulE (subE y.1.2 y.1.1) (subE y.2.2 y.2.1))] := rfl
    refine ⟨x0, x1, x2, ?_, ?_, ?_, ?_⟩
    · rw [List.foldl_cons, hs]
      exact h
    · rw [e0, List.map_cons, List.sum_cons, ρ.add, ρ.mul]
      ring
    · rw [e1, List.map_cons, List.sum_cons, ρ.add, ρ.add, ρ.mul, ρ.mul, ρ.sub, ρ.sub]
      ring
    · rw [e2, List.map_cons, List.sum_cons, ρ.add, ρ.mul, ρ.sub, ρ.sub]
      ring

/-- **One product's round.** `productRound` is a list of three; twice the first and the two others
add up to the product sum of the two tables, if these have one even length; the polynomial at r is
the product sum of the two tables bound at r. -/
theorem productRound_read (a b : List E) :
    ∃ x0 x1 x2 : E, productRound a b = [x0, x1, x2] ∧
      (∀ h : Nat, a.length = 2 * h → b.length = 2 * h →
        2 * ρ.val x0 + ρ.val x1 + ρ.val x2 = tableDot ρ a b) ∧
      ∀ r : E, ρ.val x0 + ρ.val x1 * ρ.val r + ρ.val x2 * ρ.val r ^ 2 =
        tableDot ρ (bindTop r a) (bindTop r b) := by
  obtain ⟨x0, x1, x2, h, e0, e1, e2⟩ :=
    productFold_read ρ ((tableHalves a).zip (tableHalves b)) zeroE zeroE zeroE
  rw [ρ.zero, zero_add] at e0 e1 e2
  refine ⟨x0, x1, x2, by rw [productRound_eq]; exact h, ?_, ?_⟩
  · intro n ha hb
    rw [dot_halves ρ a b n ha hb, e0, e1, e2]
    have key := sums_under_three (fun y : (E × E) × (E × E) => ρ.val y.1.1 * ρ.val y.2.1)
      (fun y => ρ.val y.1.1 * (ρ.val y.2.2 - ρ.val y.2.1) +
        (ρ.val y.1.2 - ρ.val y.1.1) * ρ.val y.2.1)
      (fun y => (ρ.val y.1.2 - ρ.val y.1.1) * (ρ.val y.2.2 - ρ.val y.2.1)) 2 1 1
      ((tableHalves a).zip (tableHalves b))
    rw [one_mul, one_mul] at key
    rw [key]
    congr 1
    refine List.map_congr_left fun y _ => ?_
    ring
  · intro r
    rw [dot_bindTop ρ r a b, e0, e1, e2]
    have key := sums_under_three (fun y : (E × E) × (E × E) => ρ.val y.1.1 * ρ.val y.2.1)
      (fun y => ρ.val y.1.1 * (ρ.val y.2.2 - ρ.val y.2.1) +
        (ρ.val y.1.2 - ρ.val y.1.1) * ρ.val y.2.1)
      (fun y => (ρ.val y.1.2 - ρ.val y.1.1) * (ρ.val y.2.2 - ρ.val y.2.1)) 1 (ρ.val r)
      (ρ.val r ^ 2) ((tableHalves a).zip (tableHalves b))
    rw [one_mul] at key
    rw [mul_comm _ (ρ.val r), mul_comm _ (ρ.val r ^ 2), key]
    congr 1
    refine List.map_congr_left fun y _ => ?_
    ring

/-! ## All terms -/

/-- Binding at one challenge more binds the next bit of the bound table. -/
theorem bindAll_snoc (rs : List E) (r : E) (t : List E) :
    bindAll (rs ++ [r]) t = bindTop r (bindAll rs t) := by
  simp [bindAll, List.foldl_append]

/-- `termsDot` of a first term and the others. -/
theorem termsDot_cons (t : Term) (ts : List Term) (rs : List E) :
    termsDot ρ (t :: ts) rs =
      ρ.val t.coef * tableDot ρ (bindAll rs t.a) (bindAll rs t.b) + termsDot ρ ts rs := by
  simp [termsDot]

/-- One step of `roundAt`'s fold. -/
def roundStep (rs : List E) (g : List E) (t : Term) : List E :=
  [addE (g.getD 0 zeroE)
     (mulE t.coef ((productRound (bindAll rs t.a) (bindAll rs t.b)).getD 0 zeroE)),
   addE (g.getD 1 zeroE)
     (mulE t.coef ((productRound (bindAll rs t.a) (bindAll rs t.b)).getD 1 zeroE)),
   addE (g.getD 2 zeroE)
     (mulE t.coef ((productRound (bindAll rs t.a) (bindAll rs t.b)).getD 2 zeroE))]

/-- `roundAt` as a fold of `roundStep`. -/
theorem roundAt_eq (ts : List Term) (rs : List E) :
    roundAt ts rs = ts.foldl (roundStep rs) [zeroE, zeroE, zeroE] := rfl

/-- The fold of `roundAt`, from any three coefficients on. n: half the bound tables' length. -/
theorem roundFold_read (rs : List E) (n : Nat) : ∀ (ts : List Term) (g0 g1 g2 : E),
    (∀ t ∈ ts, (bindAll rs t.a).length = 2 * n ∧ (bindAll rs t.b).length = 2 * n) →
    ∃ x0 x1 x2 : E, ts.foldl (roundStep rs) [g0, g1, g2] = [x0, x1, x2] ∧
      2 * ρ.val x0 + ρ.val x1 + ρ.val x2 =
        2 * ρ.val g0 + ρ.val g1 + ρ.val g2 + termsDot ρ ts rs ∧
      ∀ r : E, ρ.val x0 + ρ.val x1 * ρ.val r + ρ.val x2 * ρ.val r ^ 2 =
        ρ.val g0 + ρ.val g1 * ρ.val r + ρ.val g2 * ρ.val r ^ 2 + termsDot ρ ts (rs ++ [r])
  | [], g0, g1, g2, _ => ⟨g0, g1, g2, rfl, by simp [termsDot], fun r => by simp [termsDot]⟩
  | t :: ts, g0, g1, g2, hl => by
    obtain ⟨y0, y1, y2, hy, s1, s2⟩ := productRound_read ρ (bindAll rs t.a) (bindAll rs t.b)
    obtain ⟨x0, x1, x2, h, e1, e2⟩ := roundFold_read rs n ts
      (addE g0 (mulE t.coef y0)) (addE g1 (mulE t.coef y1)) (addE g2 (mulE t.coef y2))
      fun t' ht' => hl t' (List.mem_cons_of_mem _ ht')
    have hs : roundStep rs [g0, g1, g2] t =
        [addE g0 (mulE t.coef y0), addE g1 (mulE t.coef y1), addE g2 (mulE t.coef y2)] := by
      unfold roundStep
      rw [hy]
      rfl
    have hd := s1 n (hl t List.mem_cons_self).1 (hl t List.mem_cons_self).2
    refine ⟨x0, x1, x2, ?_, ?_, ?_⟩
    · rw [List.foldl_cons, hs]
      exact h
    · rw [e1, termsDot_cons, ← hd]
      simp only [ρ.add, ρ.mul]
      ring
    · intro r
      rw [e2 r, termsDot_cons, bindAll_snoc, bindAll_snoc, ← s2 r]
      simp only [ρ.add, ρ.mul]
      ring

/-- **A round of all terms.** `roundAt` is a list of three; twice the first and the two others add
up to `termsDot` at rs; the polynomial at r is `termsDot` at rs ++ [r]. n: half the bound tables'
length. -/
theorem roundAt_read (ts : List Term) (rs : List E) (n : Nat)
    (hl : ∀ t ∈ ts, (bindAll rs t.a).length = 2 * n ∧ (bindAll rs t.b).length = 2 * n) :
    ∃ x0 x1 x2 : E, roundAt ts rs = [x0, x1, x2] ∧
      2 * ρ.val x0 + ρ.val x1 + ρ.val x2 = termsDot ρ ts rs ∧
      ∀ r : E, ρ.val x0 + ρ.val x1 * ρ.val r + ρ.val x2 * ρ.val r ^ 2 =
        termsDot ρ ts (rs ++ [r]) := by
  obtain ⟨x0, x1, x2, h, e1, e2⟩ := roundFold_read ρ rs n ts zeroE zeroE zeroE hl
  refine ⟨x0, x1, x2, by rw [roundAt_eq]; exact h, ?_, fun r => ?_⟩
  · rw [e1, ρ.zero]
    ring
  · rw [e2 r, ρ.zero]
    ring

/-! ## The two ends -/

/-- The first end: `claimedSum` reads as `termsDot` at no challenge. -/
theorem claimedSum_read (ts : List Term) : ρ.val (claimedSum ts) = termsDot ρ ts [] := by
  unfold claimedSum termsDot
  rw [foldAdd_read ρ (fun t : Term =>
    mulE t.coef ((t.a.zip t.b).foldl (fun u y => addE u (mulE y.1 y.2)) zeroE)), ρ.zero, zero_add]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [ρ.mul, foldAdd_read ρ (fun y : E × E => mulE y.1 y.2), ρ.zero, zero_add]
  simp only [ρ.mul]
  rfl

/-- The product sum of two tables with one entry each. -/
theorem dot_one (a b : List E) (ha : a.length = 1) (hb : b.length = 1) :
    tableDot ρ a b = ρ.val (a.headD zeroE) * ρ.val (b.headD zeroE) := by
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 ha
  obtain ⟨y, rfl⟩ := List.length_eq_one_iff.1 hb
  simp [tableDot]

/-- The other end: where all bits are bound, `endAt` reads as `termsDot` at the challenges. -/
theorem endAt_read (ts : List Term) (rs : List E)
    (hl : ∀ t ∈ ts, (bindAll rs t.a).length = 1 ∧ (bindAll rs t.b).length = 1) :
    ρ.val (endAt ts rs) = termsDot ρ ts rs := by
  unfold endAt termsDot
  rw [foldAdd_read ρ (fun t : Term =>
    mulE t.coef (mulE ((bindAll rs t.a).headD zeroE) ((bindAll rs t.b).headD zeroE))), ρ.zero,
    zero_add]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [ρ.mul, ρ.mul, dot_one ρ _ _ (hl t ht).1 (hl t ht).2]

/-! ## Lengths -/

/-- Binding the highest bit halves a table. -/
theorem bindTop_length (r : E) (t : List E) : (bindTop r t).length = t.length / 2 := by
  simp only [bindTop, List.length_map, List.length_zip, List.length_take, List.length_drop]
  omega

/-- A table of 2 ^ (k + m) entries with k bits bound has 2 ^ m. -/
theorem bindAll_length : ∀ (rs : List E) (t : List E) (m : Nat), t.length = 2 ^ (rs.length + m) →
    (bindAll rs t).length = 2 ^ m
  | [], t, m, h => by simpa [bindAll] using h
  | r :: rs, t, m, h => by
    have h1 : (bindTop r t).length = 2 ^ (rs.length + m) := by
      rw [bindTop_length, h, List.length_cons, show rs.length + 1 + m = rs.length + m + 1 by omega,
        pow_succ]
      omega
    exact bindAll_length rs (bindTop r t) m h1

end Johnson.Desc.First.ForkMerge.Honest

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Honest.foldAdd_read
#print axioms Johnson.Desc.First.ForkMerge.Honest.four_lists
#print axioms Johnson.Desc.First.ForkMerge.Honest.dot_halves
#print axioms Johnson.Desc.First.ForkMerge.Honest.dot_bindTop
#print axioms Johnson.Desc.First.ForkMerge.Honest.sums_under_three
#print axioms Johnson.Desc.First.ForkMerge.Honest.productRound_eq
#print axioms Johnson.Desc.First.ForkMerge.Honest.productFold_read
#print axioms Johnson.Desc.First.ForkMerge.Honest.productRound_read
#print axioms Johnson.Desc.First.ForkMerge.Honest.bindAll_snoc
#print axioms Johnson.Desc.First.ForkMerge.Honest.termsDot_cons
#print axioms Johnson.Desc.First.ForkMerge.Honest.roundAt_eq
#print axioms Johnson.Desc.First.ForkMerge.Honest.roundFold_read
#print axioms Johnson.Desc.First.ForkMerge.Honest.roundAt_read
#print axioms Johnson.Desc.First.ForkMerge.Honest.claimedSum_read
#print axioms Johnson.Desc.First.ForkMerge.Honest.dot_one
#print axioms Johnson.Desc.First.ForkMerge.Honest.endAt_read
#print axioms Johnson.Desc.First.ForkMerge.Honest.bindTop_length
#print axioms Johnson.Desc.First.ForkMerge.Honest.bindAll_length
