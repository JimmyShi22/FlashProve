-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/PairLaw.lean: THE LAW OF THE FOUR FUNCTIONS OF
Johnson/Desc/K6/Honest/Pairs.lean (total, round, ends, inY): what an honest prover computes of a
summand that is a sum of weighted products of pairs of multilinear maps, each variable summed at a
point, READ IN THE FIELD. Nine definitions (six terms; three helpers: at3, lineTerm, roundTerm);
statements with their proofs, for every such sum.

WHAT IT IS NOT. Nothing on rounds, messages, masks of a hiding polynomial, or any property of a
protocol. Nothing is said of words that are not below the prime beyond what the reading says of
them. CONDITIONAL on the number of challenges: round_sums and round_at speak of fewer challenges
than variables; partK_all, ends_reads, inY_zero, inY_at and on_shown of just as many. on_shown is
CONDITIONAL also on what the list that it is handed holds. No chance in it.

The functions compute on the program's words. Each statement is on their reading in the library's
extension field (rd, which is Reading.gl.val; Johnson/Desc/Kinds/Law/Base.lean), under the equality
weights as that folder reads them (wt, Law/Corner.lean). Of Law/Mle.lean it takes sum_two_parts (a
sum over the indices of a point in two parts); of Law/FromLookup.lean eqAll_getD alone (entry i of
all the equality weights of a point is the weight of i).

The terms, none of which is made of the functions that they judge:
  PairSum.map    a map by its number; 0 everywhere beyond the list
  laid           a map with its first variables at a point and the later ones at bits: a plain sum
                 over the first bits under the equality weights
  PairSum.onK    the summand, in the field, on one value for each map's number
  PairSum.partK  the partial sum behind the challenges passed
  PairSum.endK   the summand at all challenges, the further variable's among them
  PairSum.valK   the claim behind the challenges passed: the one, then the other
The statements:
  laid_nil, laid_all, partK_nil, partK_all   what the terms are at the two ends
  total_reads    the sum is the partial sum behind no challenge
  round_sums     a round's three coefficients, summed at the variable's point, are the partial sum
  round_at       their value at the challenge is the next partial sum
  ends_reads     an end value is its map's multilinear extension at the challenges
  inY_zero, inY_at   the polynomial in the further variable at 0, and at its challenge
  on_reads, on_shown   the summand on values; on the end values as they are shown
  round_length, inY_length, ends_length
All else is a helper.

-/
import Mathlib
import Johnson.Desc.K6.Honest.Pairs
import Johnson.Desc.Kinds.Law.Mle
import Johnson.Desc.Kinds.Law.FromLookup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes (E)
open Law (K rd wt)
open Part.MaskedSum (valueAt)

/-! ## 1 The terms, in the field -/

/-- Map number j of the sum; where the list has no such number, the map that is 0 everywhere. -/
def PairSum.map (s : PairSum) (j : Nat) : Nat → E := s.maps.getD j fun _ => 0

/-- **A map with its first variables at a point, in the field.** f is a map on a.length + m bits.
Its first (highest) a.length variables stand at the coordinates of a, its m later ones at the bits
of b: the sum, over the first bits t, of the equality weight of t at a times the reading of entry
2^m t + b. -/
def laid (f : Nat → E) (a : List K) (m b : Nat) : K :=
  (Finset.range (2 ^ a.length)).sum fun t => wt a t * rd (f (2 ^ m * t + b))

/-- **The summand, in the field**, on one value for each map's number: the sum over the pairs of
weight times value times value. -/
def PairSum.onK (s : PairSum) (v : Nat → K) : K :=
  (s.pairs.map fun p => rd p.1 * (v p.2.1 * v p.2.2)).sum

/-- **The partial sum behind the challenges rs**, which are at most as many as the variables: the
variables in front stand at rs; the later ones are summed under the equality weights of their
points. -/
def PairSum.partK (s : PairSum) (rs : List E) : K :=
  (Finset.range (2 ^ (s.z.length - rs.length))).sum fun b =>
    wt ((s.z.drop rs.length).map rd) b *
      s.onK fun j => laid (s.map j) (rs.map rd) (s.z.length - rs.length) b

/-- **The summand at all the challenges rs, and at y in the further variable**: each map's value at
rs plus y times its mask entry. A number beyond the list of maps counts as 0. -/
def PairSum.endK (s : PairSum) (rs masks : List E) (y : E) : K :=
  s.onK fun j =>
    if j < s.maps.length then laid (s.map j) (rs.map rd) 0 0 + rd y * rd (masks.getD j 0) else 0

/-- **The claim behind the challenges passed**, the further variable's last: the partial sum; behind
all of them, the summand at them. -/
def PairSum.valK (s : PairSum) (masks rs : List E) : K :=
  if rs.length ≤ s.z.length then s.partK rs
  else s.endK (rs.take s.z.length) masks (rs.getD s.z.length 0)

/-! ## 2 What the terms are at the two ends -/

/-- With no variable laid, a map's value is the reading of its entry. -/
theorem laid_nil (f : Nat → E) (m b : Nat) : laid f [] m b = rd (f b) := by simp [laid, wt]

/-- With all variables laid: the sum over all indices under the equality weights: the map's
multilinear extension at the point. -/
theorem laid_all (f : Nat → E) (a : List K) :
    laid f a 0 0 = (Finset.range (2 ^ a.length)).sum fun t => wt a t * rd (f t) := by simp [laid]

/-- **Behind no challenge the partial sum is the sum**: over all indices, the equality weight at the
points times the summand on the entries. -/
theorem partK_nil (s : PairSum) :
    s.partK [] = (Finset.range (2 ^ s.z.length)).sum fun b =>
      wt (s.z.map rd) b * s.onK fun j => rd (s.map j b) := by
  unfold PairSum.partK
  simp only [List.length_nil, Nat.sub_zero, List.drop_zero, List.map_nil, laid_nil]

/-- **Behind all the variables' challenges the partial sum is the summand on the maps' values at
them.** -/
theorem partK_all (s : PairSum) (rs : List E) (h : rs.length = s.z.length) :
    s.partK rs = s.onK fun j => laid (s.map j) (rs.map rd) 0 0 := by
  unfold PairSum.partK
  simp only [h, Nat.sub_self, pow_zero, Finset.range_one, Finset.sum_singleton, List.drop_length,
    List.map_nil, wt, one_mul]

/-! ## 2a Helpers: the claim; sums under the equality weights; a map with variables laid -/

/-- Up to as many challenges as variables the claim is the partial sum. -/
theorem valK_le (s : PairSum) (masks rs : List E) (h : rs.length ≤ s.z.length) :
    s.valK masks rs = s.partK rs := if_pos h

/-- Behind more it is the summand at the challenges. -/
theorem valK_gt (s : PairSum) (masks rs : List E) (h : s.z.length < rs.length) :
    s.valK masks rs = s.endK (rs.take s.z.length) masks (rs.getD s.z.length 0) :=
  if_neg (Nat.not_le.mpr h)

theorem onK_congr (s : PairSum) {u v : Nat → K} (h : ∀ j, u j = v j) : s.onK u = s.onK v :=
  congrArg s.onK (funext h)

/-- A sum under the weights of a point, cut at its first coordinate, that of the highest bit. -/
theorem sum_cons (x : K) (a : List K) (M : Nat) (hM : a.length = M) (G : Nat → K) :
    ((Finset.range (2 ^ (M + 1))).sum fun b => wt (x :: a) b * G b) =
      (1 - x) * ((Finset.range (2 ^ M)).sum fun b => wt a b * G b) +
        x * ((Finset.range (2 ^ M)).sum fun b => wt a b * G (2 ^ M + b)) := by
  subst hM
  rw [pow_succ, Nat.mul_two, Finset.sum_range_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    simp only [wt]
    rw [Nat.testBit_lt_two_pow (Finset.mem_range.mp ht)]
    simp only [Bool.false_eq_true, if_false]
    ring
  · refine Finset.sum_congr rfl fun t ht => ?_
    simp only [wt]
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (Finset.mem_range.mp ht),
      Law.wt_congr a (2 ^ a.length + t) t fun j hj => Nat.testBit_two_pow_add_gt hj t]
    simp only [Bool.not_false, if_true]
    ring

/-- One more variable laid in front. -/
theorem laid_cons (f : Nat → E) (x : K) (a : List K) (m b : Nat) :
    laid f (x :: a) m b = (1 - x) * laid f a m b + x * laid f a m (2 ^ (m + a.length) + b) := by
  have e : ∀ t, 2 ^ m * (2 ^ a.length + t) + b = 2 ^ m * t + (2 ^ (m + a.length) + b) :=
    fun t => by
      rw [pow_add]
      ring
  unfold laid
  rw [List.length_cons, sum_cons x a a.length rfl fun t => rd (f (2 ^ m * t + b))]
  simp only [e]

/-- A map that is read as a mixture of a map and the same map shifted. -/
theorem laid_mix (g f : Nat → E) (x : K) (c : Nat)
    (hg : ∀ i, rd (g i) = (1 - x) * rd (f i) + x * rd (f (c + i))) (a : List K) (m b : Nat) :
    laid g a m b = (1 - x) * laid f a m b + x * laid f a m (c + b) := by
  unfold laid
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : c + (2 ^ m * t + b) = 2 ^ m * t + (c + b) := by ring
  rw [hg, e]
  ring

theorem wt_one0 (x : K) : wt [x] 0 = 1 - x := by
  show (if Nat.testBit 0 0 = true then x else 1 - x) * 1 = 1 - x
  rw [if_neg (by decide), mul_one]

theorem wt_one1 (x : K) : wt [x] 1 = x := by
  show (if Nat.testBit 1 0 = true then x else 1 - x) * 1 = x
  rw [if_pos (by decide), mul_one]

/-- One more variable laid behind: the highest of the bits that were left. -/
theorem laid_snoc (f : Nat → E) (a : List K) (x : K) (m b : Nat) :
    laid f (a ++ [x]) m b =
      (1 - x) * laid f a (m + 1) b + x * laid f a (m + 1) (2 ^ m + b) := by
  unfold laid
  rw [Law.sum_two_parts a [x] fun i => rd (f (2 ^ m * i + b)), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e2 : (2 : Nat) ^ [x].length = 2 := rfl
  have e3 : 2 ^ m * (2 * t + 0) + b = 2 ^ (m + 1) * t + b := by ring
  have e4 : 2 ^ m * (2 * t + 1) + b = 2 ^ (m + 1) * t + (2 ^ m + b) := by ring
  rw [e2, Finset.sum_range_succ, Finset.sum_range_one, wt_one0, wt_one1, e3, e4]
  ring

theorem laid_zero_map (a : List K) (m b : Nat) : laid (fun _ => 0) a m b = 0 := by
  simp [laid, Law.rd_zero]

theorem laid_beyond (s : PairSum) {j : Nat} (hj : ¬ j < s.maps.length) (a : List K) (m b : Nat) :
    laid (s.map j) a m b = 0 := by
  have e : s.map j = fun _ => 0 := List.getD_eq_default _ _ (Nat.le_of_not_lt hj)
  rw [e, laid_zero_map]

/-- **The program's laying of the first variables is read as the sum under the weights.** -/
theorem atFirst_reads : ∀ (rs : List E) (n : Nat) (f : Nat → E) (j : Nat), rs.length ≤ n →
    rd (atFirst n f rs j) = laid f (rs.map rd) (n - rs.length) j
  | [], n, f, j, _ => by
    show rd (f j) = _
    rw [List.map_nil, laid_nil]
  | r :: rs, n, f, j, h => by
    have hl : rs.length + 1 ≤ n := h
    have h' : rs.length ≤ n - 1 := by omega
    have e1 : n - (r :: rs).length = n - 1 - rs.length := by
      rw [List.length_cons]
      omega
    have e2 : n - 1 - rs.length + (rs.map rd).length = n - 1 := by
      rw [List.length_map]
      omega
    have hg : ∀ i, rd ((fun i => let a := f i; a + r * (f (2 ^ (n - 1) + i) - a)) i) =
        (1 - rd r) * rd (f i) + rd r * rd (f (2 ^ (n - 1) + i)) := by
      intro i
      show rd (f i + r * (f (2 ^ (n - 1) + i) - f i)) = _
      rw [Law.rd_add, Law.rd_mul, Law.rd_sub]
      ring
    have step : atFirst n f (r :: rs) j =
        atFirst (n - 1) (fun i => let a := f i; a + r * (f (2 ^ (n - 1) + i) - a)) rs j := rfl
    rw [step, atFirst_reads rs (n - 1) _ j h', laid_mix _ f (rd r) (2 ^ (n - 1)) hg, List.map_cons,
      laid_cons, e1, e2]

/-! ## 2b Helpers: lists -/

/-- What holds of each map's image holds of the image's member by number, the default standing for
the map that is 0 everywhere. -/
theorem getD_map_list {β γ : Type} (G : (Nat → E) → β) (d : β) (φ : β → γ)
    (h0 : φ d = φ (G fun _ => 0)) : ∀ (l : List (Nat → E)) (j : Nat),
    φ ((l.map G).getD j d) = φ (G (l.getD j fun _ => 0))
  | [], _ => h0
  | _ :: _, 0 => rfl
  | _ :: l, j + 1 => getD_map_list G d φ h0 l j

theorem getD_maps {β γ : Type} (s : PairSum) (G : (Nat → E) → β) (d : β) (φ : β → γ)
    (h0 : φ d = φ (G fun _ => 0)) (j : Nat) : φ ((s.maps.map G).getD j d) = φ (G (s.map j)) :=
  getD_map_list G d φ h0 s.maps j

theorem drop_cons_getD : ∀ (l : List E) (k : Nat), k < l.length →
    l.drop k = l.getD k 0 :: l.drop (k + 1)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, k + 1, h => drop_cons_getD l k (Nat.lt_of_succ_lt_succ h)

theorem zip_getD_from (masks : List E) : ∀ (v : List E) (k j : Nat),
    ((v.zipIdx k).map fun x => (x.1, masks.getD x.2 0)).getD j ((0 : E), (0 : E)) =
      if j < v.length then (v.getD j 0, masks.getD (k + j) 0) else (0, 0)
  | [], _, j => (if_neg (Nat.not_lt_zero j)).symm
  | _ :: _, _, 0 => (if_pos (Nat.succ_pos _)).symm
  | a :: v, k, j + 1 => by
    have ih := zip_getD_from masks v (k + 1) j
    show ((v.zipIdx (k + 1)).map fun x => (x.1, masks.getD x.2 0)).getD j ((0 : E), (0 : E)) = _
    rw [ih]
    by_cases hj : j < v.length
    · have h1 : j + 1 < (a :: v).length := Nat.succ_lt_succ hj
      rw [if_pos hj, if_pos h1, Nat.add_assoc, Nat.add_comm 1 j]
      rfl
    · have h1 : ¬ j + 1 < (a :: v).length := fun h => hj (Nat.lt_of_succ_lt_succ h)
      rw [if_neg hj, if_neg h1]

theorem zip_getD (v masks : List E) (j : Nat) :
    (v.zipIdx.map fun x => (x.1, masks.getD x.2 0)).getD j ((0 : E), (0 : E)) =
      if j < v.length then (v.getD j 0, masks.getD j 0) else (0, 0) := by
  rw [zip_getD_from masks v 0 j, Nat.zero_add]

theorem sum_range_list (n : Nat) (f : Nat → K) :
    ((List.range n).map f).sum = (Finset.range n).sum f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem fold_add {α : Type} (F : α → E) : ∀ (L : List α) (t : E),
    rd (L.foldl (fun t a => t + F a) t) = rd t + (L.map fun a => rd (F a)).sum
  | [], t => by simp
  | a :: L, t => by
    rw [List.foldl_cons, fold_add F L, Law.rd_add, List.map_cons, List.sum_cons]
    ring

theorem rd_eqAll (l : List E) (b : Nat) (hb : b < 2 ^ l.length) :
    rd ((eqAll l.toArray).getD b 0) = wt (l.map rd) b := by
  rw [Law.Came.eqAll_getD, Law.rd_eq]
  exact if_pos hb

/-! ## 2c Helpers: polynomials of three coefficients -/

theorem rdA (a b : E) : rd (OnBytes.addE a b) = rd a + rd b := Law.rd_add a b
theorem rdM (a b : E) : rd (OnBytes.mulE a b) = rd a * rd b := Law.rd_mul a b
theorem rdZ : rd OnBytes.zeroE = 0 := Law.rd_zero

/-- Three coefficients, the lowest first, read as a polynomial's value at an element of the
field. -/
def at3 (g : List E) (x : K) : K :=
  rd (g.getD 0 0) + rd (g.getD 1 0) * x + rd (g.getD 2 0) * x ^ 2

theorem at3_three (a b c : E) (x : K) : at3 [a, b, c] x = rd a + rd b * x + rd c * x ^ 2 := rfl

theorem at3_zero (x : K) : at3 [0, 0, 0] x = 0 := by
  rw [at3_three, Law.rd_zero]
  ring

theorem exists_three {g : List E} (h : g.length = 3) : ∃ a b c, g = [a, b, c] := by
  rcases g with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
  all_goals first
    | exact ⟨_, _, _, rfl⟩
    | exact absurd h (by simp)

theorem valueAt_three (a b c x : E) :
    rd (valueAt [a, b, c] x) = rd a + rd b * rd x + rd c * rd x ^ 2 := by
  simp only [valueAt, List.foldr_cons, List.foldr_nil, rdA, rdM, rdZ]
  ring

theorem valueAt_at3 {g : List E} (h : g.length = 3) (x : E) :
    rd (valueAt g x) = at3 g (rd x) := by
  obtain ⟨a, b, c, rfl⟩ := exists_three h
  exact valueAt_three a b c x

theorem add3_length {g h : List E} (hg : g.length = 3) (hh : h.length = 3) :
    (add3 g h).length = 3 := by
  obtain ⟨a, b, c, rfl⟩ := exists_three hg
  obtain ⟨a', b', c', rfl⟩ := exists_three hh
  rfl

theorem add3_at3 {g h : List E} (hg : g.length = 3) (hh : h.length = 3) (x : K) :
    at3 (add3 g h) x = at3 g x + at3 h x := by
  obtain ⟨a, b, c, rfl⟩ := exists_three hg
  obtain ⟨a', b', c', rfl⟩ := exists_three hh
  show at3 [a + a', b + b', c + c'] x = _
  rw [at3_three, at3_three, at3_three, Law.rd_add, Law.rd_add, Law.rd_add]
  ring

theorem scale_at3 {g : List E} (hg : g.length = 3) (c : E) (x : K) :
    at3 (g.map (c * ·)) x = rd c * at3 g x := by
  obtain ⟨a, b, d, rfl⟩ := exists_three hg
  show at3 [c * a, c * b, c * d] x = _
  rw [at3_three, at3_three, Law.rd_mul, Law.rd_mul, Law.rd_mul]
  ring

/-- A fold of sums of polynomials of three coefficients is read as the sum. -/
theorem fold_add3 {α : Type} (F : α → List E) (hF : ∀ a, (F a).length = 3) :
    ∀ (L : List α) (g : List E), g.length = 3 →
      (L.foldl (fun g a => add3 g (F a)) g).length = 3 ∧
        ∀ x : K, at3 (L.foldl (fun g a => add3 g (F a)) g) x =
          at3 g x + (L.map fun a => at3 (F a) x).sum
  | [], g, hg => ⟨hg, fun x => by simp⟩
  | a :: L, g, hg => by
    have ih := fold_add3 F hF L (add3 g (F a)) (add3_length hg (hF a))
    refine ⟨ih.1, fun x => ?_⟩
    rw [List.foldl_cons, ih.2 x, add3_at3 hg (hF a), List.map_cons, List.sum_cons]
    ring

/-! ## 2d Helpers: the summand on lines; a round's term -/

/-- One pair's term of the summand on lines. -/
def lineTerm (l : List (E × E)) (p : E × Nat × Nat) : List E :=
  [p.1 * ((l.getD p.2.1 (0, 0)).1 * (l.getD p.2.2 (0, 0)).1),
   p.1 * ((l.getD p.2.1 (0, 0)).1 * (l.getD p.2.2 (0, 0)).2 +
     (l.getD p.2.1 (0, 0)).2 * (l.getD p.2.2 (0, 0)).1),
   p.1 * ((l.getD p.2.1 (0, 0)).2 * (l.getD p.2.2 (0, 0)).2)]

theorem onLines_eq (s : PairSum) (l : List (E × E)) :
    s.onLines l = s.pairs.foldl (fun g p => add3 g (lineTerm l p)) [0, 0, 0] := rfl

theorem onLines_length (s : PairSum) (l : List (E × E)) : (s.onLines l).length = 3 :=
  (fold_add3 (lineTerm l) (fun _ => rfl) s.pairs [0, 0, 0] rfl).1

/-- The summand on lines is read as the summand, in the field, on the lines' values. -/
theorem onLines_at3 (s : PairSum) (l : List (E × E)) (x : K) :
    at3 (s.onLines l) x =
      s.onK fun j => rd (l.getD j (0, 0)).1 + rd (l.getD j (0, 0)).2 * x := by
  rw [onLines_eq, (fold_add3 (lineTerm l) (fun _ => rfl) s.pairs [0, 0, 0] rfl).2 x, at3_zero,
    zero_add]
  unfold PairSum.onK
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  unfold lineTerm
  rw [at3_three]
  simp only [Law.rd_mul, Law.rd_add]
  ring

/-- The term of a round's polynomial at the later bits b. -/
def roundTerm (s : PairSum) (rs : List E) (b : Nat) : List E :=
  (s.onLines ((s.maps.map fun f => atFirst s.z.length f rs).map fun f =>
    (f b, f (2 ^ (s.z.length - rs.length - 1) + b) - f b))).map
      ((eqAll (s.z.drop (rs.length + 1)).toArray).getD b 0 * ·)

theorem round_eq (s : PairSum) (rs : List E) :
    s.round rs = (List.range (2 ^ (s.z.length - rs.length - 1))).foldl
      (fun g b => add3 g (roundTerm s rs b)) [0, 0, 0] := rfl

theorem roundTerm_length (s : PairSum) (rs : List E) (b : Nat) :
    (roundTerm s rs b).length = 3 := by
  unfold roundTerm
  rw [List.length_map, onLines_length]

theorem roundTerm_at3 (s : PairSum) (rs : List E) (h : rs.length < s.z.length) (x : K) (b : Nat)
    (hb : b < 2 ^ (s.z.length - (rs.length + 1))) :
    at3 (roundTerm s rs b) x = wt ((s.z.drop (rs.length + 1)).map rd) b *
      s.onK fun j => laid (s.map j) (rs.map rd ++ [x]) (s.z.length - (rs.length + 1)) b := by
  have hm : s.z.length - rs.length - 1 = s.z.length - (rs.length + 1) := Nat.sub_sub _ _ _
  have hn : s.z.length - rs.length = s.z.length - (rs.length + 1) + 1 := by omega
  have hA : ∀ (f : Nat → E) (i : Nat), rd (atFirst s.z.length f rs i) =
      laid f (rs.map rd) (s.z.length - (rs.length + 1) + 1) i := fun f i => by
    rw [atFirst_reads rs s.z.length f i (le_of_lt h), hn]
  unfold roundTerm
  rw [hm, scale_at3 (onLines_length _ _), onLines_at3,
    rd_eqAll _ b (by rw [List.length_drop]; exact hb), List.map_map]
  refine congrArg (HMul.hMul _) (onK_congr s fun j => ?_)
  refine (getD_maps s (fun f => (atFirst s.z.length f rs b,
    atFirst s.z.length f rs (2 ^ (s.z.length - (rs.length + 1)) + b) - atFirst s.z.length f rs b))
    ((0 : E), (0 : E)) (fun p => rd p.1 + rd p.2 * x) ?_ j).trans ?_
  · show rd (0 : E) + rd (0 : E) * x = rd (atFirst s.z.length (fun _ => 0) rs b) +
      rd (atFirst s.z.length (fun _ => 0) rs (2 ^ (s.z.length - (rs.length + 1)) + b) -
        atFirst s.z.length (fun _ => 0) rs b) * x
    rw [Law.rd_sub, hA, hA, laid_zero_map, laid_zero_map, Law.rd_zero]
    ring
  · show rd (atFirst s.z.length (s.map j) rs b) +
      rd (atFirst s.z.length (s.map j) rs (2 ^ (s.z.length - (rs.length + 1)) + b) -
        atFirst s.z.length (s.map j) rs b) * x = _
    rw [Law.rd_sub, hA, hA, laid_snoc]
    ring

/-- **A round's polynomial, at any element of the field, is the partial sum with the variable at
hand laid there.** -/
theorem round_at3 (s : PairSum) (rs : List E) (h : rs.length < s.z.length) (x : K) :
    at3 (s.round rs) x = (Finset.range (2 ^ (s.z.length - (rs.length + 1)))).sum fun b =>
      wt ((s.z.drop (rs.length + 1)).map rd) b *
        s.onK fun j => laid (s.map j) (rs.map rd ++ [x]) (s.z.length - (rs.length + 1)) b := by
  have hm : s.z.length - rs.length - 1 = s.z.length - (rs.length + 1) := Nat.sub_sub _ _ _
  rw [round_eq, (fold_add3 (roundTerm s rs) (roundTerm_length s rs) _ [0, 0, 0] rfl).2 x, at3_zero,
    zero_add, sum_range_list, hm]
  exact Finset.sum_congr rfl fun b hb => roundTerm_at3 s rs h x b (Finset.mem_range.mp hb)

/-! ## 3 The law of the four functions -/

/-- The summand on values is read as the summand in the field. -/
theorem on_reads (s : PairSum) (v : List E) : rd (s.on v) = s.onK fun j => rd (v.getD j 0) :=
  by
  have key := fold_add (fun p : E × Nat × Nat => p.1 * (v.getD p.2.1 0 * v.getD p.2.2 0)) s.pairs 0
  rw [Law.rd_zero, zero_add] at key
  unfold PairSum.on PairSum.onK
  rw [key]
  exact congrArg List.sum (List.map_congr_left fun p _ => by simp only [Law.rd_mul])

theorem round_length (s : PairSum) (rs : List E) : (s.round rs).length = 3 := by
  rw [round_eq]
  exact (fold_add3 (roundTerm s rs) (roundTerm_length s rs) _ [0, 0, 0] rfl).1

theorem inY_length (s : PairSum) (rs masks : List E) : (s.inY rs masks).length = 3 :=
  onLines_length s _

theorem ends_length (s : PairSum) (rs : List E) : (s.ends rs).length = s.maps.length :=
  by
  unfold PairSum.ends
  rw [List.length_map]

/-- **The sum is read as the partial sum behind no challenge.** -/
theorem total_reads (s : PairSum) : rd s.total = s.partK [] := by
  rw [partK_nil]
  show rd (sumTo (2 ^ s.z.length) fun i =>
    (eqAll s.z.toArray).getD i 0 * s.on (s.maps.map (· i))) = _
  rw [Law.rd_sumTo]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Law.rd_mul, rd_eqAll s.z i (Finset.mem_range.mp hi), on_reads]
  exact congrArg (HMul.hMul _) (onK_congr s fun j => getD_maps s (fun f => f i) 0 rd rfl j)

/-- **A round's polynomial, summed at the variable's point, is the partial sum so far**:
g_0 + z (g_1 + g_2), which is (1 - z) g(0) + z g(1). -/
theorem round_sums (s : PairSum) (rs : List E) (h : rs.length < s.z.length) :
    rd ((s.round rs).getD 0 0) + rd (s.z.getD rs.length 0) *
      (rd ((s.round rs).getD 1 0) + rd ((s.round rs).getD 2 0)) = s.partK rs := by
  have hd := drop_cons_getD s.z rs.length h
  have hn : s.z.length - rs.length = s.z.length - (rs.length + 1) + 1 := by omega
  have hl : ((s.z.drop (rs.length + 1)).map rd).length = s.z.length - (rs.length + 1) := by
    rw [List.length_map, List.length_drop]
  have e : rd ((s.round rs).getD 0 0) + rd (s.z.getD rs.length 0) *
      (rd ((s.round rs).getD 1 0) + rd ((s.round rs).getD 2 0)) =
      (1 - rd (s.z.getD rs.length 0)) * at3 (s.round rs) 0 +
        rd (s.z.getD rs.length 0) * at3 (s.round rs) 1 := by
    unfold at3
    ring
  rw [e, round_at3 s rs h 0, round_at3 s rs h 1]
  unfold PairSum.partK
  rw [hd, List.map_cons, hn, sum_cons _ _ _ hl]
  simp only [laid_snoc, sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add]

/-- **A round's polynomial at its challenge is the next partial sum.** -/
theorem round_at (s : PairSum) (rs : List E) (r : E) (h : rs.length < s.z.length) :
    rd (valueAt (s.round rs) r) = s.partK (rs ++ [r]) := by
  rw [valueAt_at3 (round_length s rs), round_at3 s rs h]
  unfold PairSum.partK
  rw [List.length_append, List.length_singleton, List.map_append]
  rfl

/-- **An end value is read as its map's value at the challenges.** -/
theorem ends_reads (s : PairSum) (rs : List E) (j : Nat) (h : rs.length = s.z.length) :
    rd ((s.ends rs).getD j 0) = laid (s.map j) (rs.map rd) 0 0 := by
  have ht : rs.take s.z.length = rs := List.take_of_length_le (le_of_eq h)
  have hA : ∀ f : Nat → E, rd (atFirst s.z.length f rs 0) = laid f (rs.map rd) 0 0 := fun f => by
    rw [atFirst_reads rs s.z.length f 0 (le_of_eq h), h, Nat.sub_self]
  have h0 : rd (0 : E) = rd (atFirst s.z.length (fun _ => 0) rs 0) := by
    rw [hA, laid_zero_map, Law.rd_zero]
  unfold PairSum.ends
  rw [ht]
  exact (getD_maps s (fun f => atFirst s.z.length f rs 0) 0 rd h0 j).trans (hA _)

/-- The polynomial in the further variable, at any element of the field. -/
theorem inY_at3 (s : PairSum) (rs masks : List E) (x : K) :
    at3 (s.inY rs masks) x = s.onK fun j =>
      if j < s.maps.length then rd ((s.ends rs).getD j 0) + rd (masks.getD j 0) * x else 0 := by
  unfold PairSum.inY
  rw [onLines_at3]
  refine onK_congr s fun j => ?_
  rw [zip_getD, ends_length]
  by_cases hj : j < s.maps.length
  · rw [if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj]
    show rd (0 : E) + rd (0 : E) * x = 0
    rw [Law.rd_zero]
    ring

/-- **The polynomial in the further variable, read at 0, is the last partial sum.** -/
theorem inY_zero (s : PairSum) (rs masks : List E) (h : rs.length = s.z.length) :
    rd ((s.inY rs masks).getD 0 0) = s.partK rs := by
  have e : rd ((s.inY rs masks).getD 0 0) = at3 (s.inY rs masks) 0 := by
    unfold at3
    ring
  rw [e, inY_at3, partK_all s rs h]
  refine onK_congr s fun j => ?_
  by_cases hj : j < s.maps.length
  · rw [if_pos hj, ends_reads s rs j h]
    ring
  · rw [if_neg hj]
    exact (laid_beyond s hj _ _ _).symm

/-- **The polynomial in the further variable at its challenge is the summand at all challenges.** -/
theorem inY_at (s : PairSum) (rs masks : List E) (y : E) (h : rs.length = s.z.length) :
    rd (valueAt (s.inY rs masks) y) = s.endK rs masks y := by
  rw [valueAt_at3 (inY_length s rs masks), inY_at3]
  unfold PairSum.endK
  refine onK_congr s fun j => ?_
  by_cases hj : j < s.maps.length
  · rw [if_pos hj, if_pos hj, ends_reads s rs j h]
    ring
  · rw [if_neg hj, if_neg hj]

/-- **The summand on the end values as shown is the same.** v: one element for each map, read as
the end value plus y times the mask entry. -/
theorem on_shown (s : PairSum) (rs masks v : List E) (y : E) (h : rs.length = s.z.length)
    (hl : v.length = s.maps.length)
    (hv : ∀ j, j < s.maps.length →
      rd (v.getD j 0) = rd ((s.ends rs).getD j 0) + rd y * rd (masks.getD j 0)) :
    rd (s.on v) = s.endK rs masks y := by
  rw [on_reads]
  unfold PairSum.endK
  refine onK_congr s fun j => ?_
  by_cases hj : j < s.maps.length
  · rw [if_pos hj, hv j hj, ends_reads s rs j h]
  · rw [if_neg hj, List.getD_eq_default _ _ (by rw [hl]; exact Nat.le_of_not_lt hj), Law.rd_zero]

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.laid_nil
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.laid_all
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.partK_nil
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.partK_all
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.valK_le
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.valK_gt
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.onK_congr
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sum_cons
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.laid_cons
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.laid_mix
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.wt_one0
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.wt_one1
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.laid_snoc
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.laid_zero_map
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.laid_beyond
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.atFirst_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.getD_map_list
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.getD_maps
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.drop_cons_getD
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.zip_getD_from
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.zip_getD
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sum_range_list
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.fold_add
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.rd_eqAll
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.rdA
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.rdM
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.rdZ
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.at3_three
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.at3_zero
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.exists_three
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.valueAt_three
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.valueAt_at3
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.add3_length
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.add3_at3
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.scale_at3
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.fold_add3
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.onLines_eq
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.onLines_length
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.onLines_at3
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.round_eq
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.roundTerm_length
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.roundTerm_at3
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.round_at3
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.on_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.round_length
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.inY_length
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.ends_length
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.total_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.round_sums
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.round_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.ends_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.inY_at3
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.inY_zero
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.inY_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.on_shown
