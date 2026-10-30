-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookCube.lean

The sumcheck of κ + A B over a cube under equality weights, with its variables taken in any order:
the run of its round polynomials (pj, Johnson/HonestTrace/LookDefs.lean) is lawful.

What "lawful" says (Job.Lawful). Along any challenges xs, one for each variable: the first round
polynomial sums, under the weights (1 - z, z) of its variable's coordinate z, to the true sum; each
later one sums to the value of the one in front at its challenge; the last one's value at its
challenge is κ + A B at the point, A and B read as multilinear extensions. And the polynomial in the
further variable Y has that value at 0, and at β the summand at the end values moved by β times
their mask entries.

Main theorems:
* "pj_lawful": if o is a permutation of the numbers below m and z has m coordinates, then pj m κ A B
  o z is lawful.
* "ext_line": if r has m coordinates, (1 - ρ) times the extension of the first 2^m entries of f at r
  plus ρ times that of the next 2^m entries is the extension of the first 2^(m+1) entries at (r, ρ),
  ρ as the new highest coordinate.
* "pjRound_deg1": if o is a permutation of the numbers below m, fewer than m challenges rs stand in
  front, and B does not read the bit of the round's coordinate, then the third coefficient of
  pjRound m κ A B o z rs is 0.
On the way:
* "sum_eqN_split": a sum over the cube under the weights TwV.eqN W, split at one coordinate c.
  "sum_eqN_zeros": under the weights of the point 0 the corner 0 alone counts.
* "wsum_round", "evalP_round": the two laws of a round, and "lvlSum_last": the law of the run's end,
  in terms of "lvlSum", the weighted sum of κ + A B behind l rounds. "chained_from": the run from
  round l on.
* "ext_foldN", "ptN_byVar", "foldN_zero": behind all m rounds a folded function is, at the corner 0,
  the extension at the point TwV.byVar o xs.
* "Ord o m": what the proofs use of "o lists the numbers below m once each"; "ord_of_perm" gets it
  from a permutation. "ptN": the point behind l rounds.

Limits. A, B and κ are arbitrary; o is any permutation; z and the challenges are arbitrary lists of
the right length. The end values' mask entries are an arbitrary list m. Nothing is said of the
polynomial H of the mask entries, of what is sent, or of a verifier. K is a field because
LookDefs.lean asks one.

Not claimed: anything on a lookup, a prover or a verifier.

-/
import Johnson.HonestTrace.LookDefs

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open Finset TwV

section
variable {K : Type} [Field K]

/-! ## Sums over a cube, one coordinate at a time -/

/-- A sum over the numbers below n * 2, by pairs (2 y, 2 y + 1). -/
theorem sum_range_two (n : ℕ) (g : ℕ → K) :
    ∑ x ∈ range (n * 2), g x = ∑ y ∈ range n, (g (2 * y) + g (2 * y + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    have e : n * 2 = 2 * n := Nat.mul_comm _ _
    rw [e]
    ring

/-- The weight of an even corner: (1 - w) times the weight of its half in the other coordinates. -/
theorem eqN_even (w : K) (W : List K) (y : ℕ) : eqN (w :: W) (2 * y) = (1 - w) * eqN W y := by
  have e1 : 2 * y % 2 = 0 := by omega
  have e2 : 2 * y / 2 = y := by omega
  simp [eqN, e1, e2]

/-- The weight of an odd corner: w times the weight of its half in the other coordinates. -/
theorem eqN_odd (w : K) (W : List K) (y : ℕ) : eqN (w :: W) (2 * y + 1) = w * eqN W y := by
  have e1 : (2 * y + 1) % 2 = 1 := by omega
  have e2 : (2 * y + 1) / 2 = y := by omega
  simp [eqN, e1, e2]

/-- A weighted sum over the cube, split at coordinate 0. -/
theorem sum_cons (w : K) (W : List K) (F : ℕ → K) :
    ∑ x ∈ range (2 ^ (w :: W).length), eqN (w :: W) x * F x =
      (1 - w) * ∑ y ∈ range (2 ^ W.length), eqN W y * F (2 * y) +
        w * ∑ y ∈ range (2 ^ W.length), eqN W y * F (2 * y + 1) := by
  rw [List.length_cons, pow_succ, sum_range_two, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [eqN_even, eqN_odd]
  ring

/-- For c below the number of coordinates: the sum of eqN W x * F x over the cube is the sum, under
the weights with coordinate c put to 0, of (1 - W_c) F (x with bit c = 0) + W_c F (x with
bit c = 1). -/
theorem sum_eqN_split : ∀ (W : List K) (c : ℕ), c < W.length → ∀ F : ℕ → K,
    ∑ x ∈ range (2 ^ W.length), eqN W x * F x =
      ∑ x ∈ range (2 ^ W.length), eqN (W.set c 0) x *
        ((1 - W.getD c 0) * F (setBit c false x) + W.getD c 0 * F (setBit c true x))
  | [], c, hc, _ => absurd hc (by simp)
  | w :: W, 0, _, F => by
    have hl : ((w :: W).set 0 0).length = (w :: W).length := List.length_set
    rw [sum_cons, ← hl]
    show _ = ∑ x ∈ range (2 ^ ((0 : K) :: W).length), eqN ((0 : K) :: W) x * _
    rw [sum_cons, mul_sum, mul_sum, ← sum_add_distrib, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    have e1 : setBit 0 false (2 * y) = 2 * y := by
      show 2 * (2 * y / 2) + 0 = 2 * y
      omega
    have e2 : setBit 0 true (2 * y) = 2 * y + 1 := by
      show 2 * (2 * y / 2) + 1 = 2 * y + 1
      omega
    rw [e1, e2]
    show _ = (1 - 0) * (eqN W y * ((1 - w) * F (2 * y) + w * F (2 * y + 1))) + 0 * _
    ring
  | w :: W, c + 1, hc, F => by
    have hc' : c < W.length := by simpa using hc
    have hl : (W.set c 0).length = W.length := List.length_set
    rw [sum_cons, sum_eqN_split W c hc' (fun y => F (2 * y)),
      sum_eqN_split W c hc' (fun y => F (2 * y + 1))]
    show _ = ∑ x ∈ range (2 ^ (w :: W).length), eqN (w :: W.set c 0) x * _
    have hl2 : (w :: W).length = (w :: W.set c 0).length := by simp
    rw [hl2, sum_cons, hl]
    have s0 : ∀ (b : Bool) (y : ℕ), setBit (c + 1) b (2 * y) = 2 * setBit c b y := by
      intro b y
      show 2 * setBit c b (2 * y / 2) + 2 * y % 2 = _
      have e1 : 2 * y / 2 = y := by omega
      have e2 : 2 * y % 2 = 0 := by omega
      rw [e1, e2]
      rfl
    have s1 : ∀ (b : Bool) (y : ℕ), setBit (c + 1) b (2 * y + 1) = 2 * setBit c b y + 1 := by
      intro b y
      show 2 * setBit c b ((2 * y + 1) / 2) + (2 * y + 1) % 2 = _
      have e1 : (2 * y + 1) / 2 = y := by omega
      have e2 : (2 * y + 1) % 2 = 1 := by omega
      rw [e1, e2]
    simp only [s0, s1, List.getD_cons_succ]

/-- Under the weights of the point with m coordinates 0, the weighted sum of F over the cube is
F 0. -/
theorem sum_eqN_zeros : ∀ (m : ℕ) (F : ℕ → K),
    ∑ x ∈ range (2 ^ m), eqN (List.replicate m (0 : K)) x * F x = F 0
  | 0, F => by simp [eqN]
  | m + 1, F => by
    have h := sum_cons (0 : K) (List.replicate m 0) F
    rw [List.length_cons, List.length_replicate] at h
    rw [List.replicate_succ, h, sum_eqN_zeros m (fun y => F (2 * y))]
    simp

end

/-! ## The weights and the folded functions -/

section
variable {K : Type} [Field K]

/-- wtN keeps the number of coordinates. -/
theorem wtN_length (o : List ℕ) (z : List K) : ∀ l, (wtN o z l).length = z.length
  | 0 => rfl
  | l + 1 => by
    show ((wtN o z l).set (o.getD l 0) 0).length = _
    rw [List.length_set, wtN_length o z l]

/-- At a coordinate that none of the first l rounds takes, wtN o z l is z. -/
theorem wtN_getD (o : List ℕ) (z : List K) : ∀ (l c : ℕ), (∀ i < l, o.getD i 0 ≠ c) →
    (wtN o z l).getD c 0 = z.getD c 0
  | 0, _, _ => rfl
  | l + 1, c, h => by
    show ((wtN o z l).set (o.getD l 0) 0).getD c 0 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (h l (by omega)),
      ← List.getD_eq_getElem?_getD, wtN_getD o z l c fun i hi => h i (by omega)]

/-- A list with 0 put at place c reads 0 at c, with the default 0. -/
theorem set_getD_self (L : List K) (c : ℕ) : (L.set c 0).getD c 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : c < L.length
  · rw [List.getElem?_set_self h]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_set]; omega)]
    rfl

/-- At a coordinate that one of the first l rounds takes, wtN o z l is 0. -/
theorem wtN_zero (o : List ℕ) (z : List K) : ∀ (l c : ℕ), (∃ i < l, o.getD i 0 = c) →
    (wtN o z l).getD c 0 = 0
  | 0, _, h => by
    obtain ⟨i, hi, _⟩ := h
    omega
  | l + 1, c, h => by
    show ((wtN o z l).set (o.getD l 0) 0).getD c 0 = 0
    by_cases e : o.getD l 0 = c
    · rw [e]
      exact set_getD_self _ _
    · obtain ⟨i, hi, hc⟩ := h
      have hil : i < l := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h1 | h1
        · exact h1
        · exact absurd (h1 ▸ hc) e
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne e, ← List.getD_eq_getElem?_getD]
      exact wtN_zero o z l c ⟨i, hil, hc⟩

/-- What is used of "o lists the coordinates below m, each once". -/
structure Ord (o : List ℕ) (m : ℕ) : Prop where
  len : o.length = m
  lt : ∀ i < m, o.getD i 0 < m
  inj : ∀ i < m, ∀ j < m, o.getD i 0 = o.getD j 0 → i = j
  onto : ∀ c < m, ∃ i < m, o.getD i 0 = c

/-- A permutation of the numbers below m meets Ord. -/
theorem ord_of_perm {o : List ℕ} {m : ℕ} (h : o.Perm (List.range m)) : Ord o m := by
  have hl : o.length = m := by rw [h.length_eq, List.length_range]
  have hnd : o.Nodup := h.symm.nodup List.nodup_range
  have hg : ∀ i, (hi : i < m) → o.getD i 0 = o[i]'(by omega) := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by omega)]
  refine ⟨hl, fun i hi => ?_, fun i hi j hj e => ?_, fun c hc => ?_⟩
  · rw [hg i hi]
    exact List.mem_range.1 (h.mem_iff.1 (List.getElem_mem _))
  · rw [hg i hi, hg j hj] at e
    exact (List.Nodup.getElem_inj_iff hnd).1 e
  · obtain ⟨i, hi, e⟩ := List.getElem_of_mem (h.mem_iff.2 (List.mem_range.2 hc))
    exact ⟨i, by omega, by rw [hg i (by omega)]; exact e⟩

/-- Under Ord o m, for z of m coordinates: behind all m rounds every weight's coordinate is 0. -/
theorem wtN_all {o : List ℕ} {m : ℕ} (O : Ord o m) (z : List K) (hz : z.length = m) :
    wtN o z m = List.replicate m 0 := by
  refine List.ext_getElem (by rw [wtN_length, hz, List.length_replicate]) fun c h1 h2 => ?_
  have hc : c < m := by rw [wtN_length, hz] at h1; exact h1
  have e := wtN_zero o z m c (O.onto c hc)
  rw [List.getD_eq_getElem _ _ h1] at e
  rw [e, List.getElem_replicate]

/-- foldN o rs f l reads of rs the first l challenges alone. -/
theorem foldN_congr (o : List ℕ) {rs rs' : List K} (f : ℕ → K) : ∀ l,
    (∀ i < l, rs.getD i 0 = rs'.getD i 0) → foldN o rs f l = foldN o rs' f l
  | 0, _ => rfl
  | l + 1, h => by
    show fixAt _ (rs.getD l 0) (foldN o rs f l) = fixAt _ (rs'.getD l 0) (foldN o rs' f l)
    rw [h l (by omega), foldN_congr o f l fun i hi => h i (by omega)]

/-- foldN behind l rounds at the first l challenges of xs is foldN at xs. -/
theorem foldN_take (o : List ℕ) (xs : List K) (f : ℕ → K) (l : ℕ) :
    foldN o (xs.take l) f l = foldN o xs f l :=
  foldN_congr o f l fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

/-! ## The two laws of a round -/

/-- The weighted sum of κ + A B behind l rounds. -/
def lvlSum (m : ℕ) (κ : K) (A B : ℕ → K) (o : List ℕ) (z xs : List K) (l : ℕ) : K :=
  ∑ X ∈ range (2 ^ m), eqN (wtN o z l) X * (κ + foldN o xs A l X * foldN o xs B l X)

/-- Under Ord o m, for z of m coordinates, l < m and at least l challenges: round l's polynomial
sums, under the weights of its coordinate of z, to lvlSum behind l rounds. -/
theorem wsum_round {m : ℕ} (κ : K) (A B : ℕ → K) {o : List ℕ} (O : Ord o m) (z xs : List K)
    (hz : z.length = m) {l : ℕ} (hl : l < m) (hx : l ≤ xs.length) :
    wsum (z.getD (o.getD l 0) 0) (pjRound m κ A B o z (xs.take l)) =
      lvlSum m κ A B o z xs l := by
  have hlen : (xs.take l).length = l := by rw [List.length_take, Nat.min_eq_left hx]
  have hs := sum_eqN_split (wtN o z l) (o.getD l 0) (by rw [wtN_length, hz]; exact O.lt l hl)
    (fun X => κ + foldN o xs A l X * foldN o xs B l X)
  rw [wtN_length, hz, wtN_getD o z l _ fun i hi e => by
    have := O.inj i (by omega) l hl e
    omega] at hs
  unfold lvlSum
  rw [hs]
  unfold pjRound wsum
  simp only [hlen, foldN_take, List.headD_cons, List.tail_cons, List.sum_cons, List.sum_nil,
    add_zero]
  rw [← sum_add_distrib, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun X _ => ?_
  show eqN (wtN o z (l + 1)) X * _ + _ = eqN (wtN o z (l + 1)) X * _
  ring

/-- With at least l challenges: round l's polynomial has at challenge number l (0 if there is none)
the value lvlSum behind l + 1 rounds. -/
theorem evalP_round {m : ℕ} (κ : K) (A B : ℕ → K) (o : List ℕ) (z xs : List K) {l : ℕ}
    (hx : l ≤ xs.length) :
    evalP (pjRound m κ A B o z (xs.take l)) (xs.getD l 0) = lvlSum m κ A B o z xs (l + 1) := by
  have hlen : (xs.take l).length = l := by rw [List.length_take, Nat.min_eq_left hx]
  unfold lvlSum pjRound evalP
  simp only [hlen, foldN_take, List.headD_cons, List.tail_cons, evalGo, add_zero]
  rw [sum_mul, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun X _ => ?_
  show _ = eqN (wtN o z (l + 1)) X *
    (κ + fixAt (o.getD l 0) (xs.getD l 0) (foldN o xs A l) X *
      fixAt (o.getD l 0) (xs.getD l 0) (foldN o xs B l) X)
  unfold fixAt
  ring

end

/-! ## The end of the run: the folded functions at the corner 0 are extensions at the point -/

section
variable {K : Type} [Field K]

/-- For pt of m coordinates with 0 at coordinate c < m: the extension of fixAt c r f at pt is the
extension of f at pt with r put at coordinate c. -/
theorem ext_fixAt (m : ℕ) (f : ℕ → K) (c : ℕ) (r : K) (pt : List K) (hp : pt.length = m)
    (hc : c < m) (h0 : pt.getD c 0 = 0) : ext m (fixAt c r f) pt = ext m f (pt.set c r) := by
  have hcl : c < pt.length := by omega
  have hs := sum_eqN_split (pt.set c r) c (by rw [List.length_set]; exact hcl) f
  rw [List.length_set, hp] at hs
  have hg : pt[c] = 0 := by rw [← List.getD_eq_getElem _ 0 hcl]; exact h0
  have e1 : (pt.set c r).set c 0 = pt := by
    rw [List.set_set, ← hg]
    exact List.set_getElem_self hcl
  have e2 : (pt.set c r).getD c 0 = r := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hcl]
    rfl
  unfold ext fixAt
  rw [hs, e1, e2]

/-- pt with coordinate o[i] put to xs[i], for i below l. -/
def ptN (o : List ℕ) (xs : List K) : ℕ → List K → List K
  | 0, pt => pt
  | l + 1, pt => ptN o xs l (pt.set (o.getD l 0) (xs.getD l 0))

/-- ptN keeps the number of coordinates. -/
theorem ptN_length (o : List ℕ) (xs : List K) : ∀ (l : ℕ) (pt : List K),
    (ptN o xs l pt).length = pt.length
  | 0, _ => rfl
  | l + 1, pt => by
    show (ptN o xs l (pt.set _ _)).length = _
    rw [ptN_length o xs l, List.length_set]

/-- At a coordinate that none of the first l rounds takes, ptN o xs l pt is pt. -/
theorem ptN_off (o : List ℕ) (xs : List K) : ∀ (l : ℕ) (pt : List K) (c : ℕ),
    (∀ j < l, o.getD j 0 ≠ c) → (ptN o xs l pt).getD c 0 = pt.getD c 0
  | 0, _, _, _ => rfl
  | l + 1, pt, c, h => by
    show (ptN o xs l (pt.set _ _)).getD c 0 = _
    rw [ptN_off o xs l _ c fun j hj => h j (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (h l (by omega)), ← List.getD_eq_getElem?_getD]

/-- Under Ord o m, for l ≤ m and pt of m coordinates: at the coordinate of round i < l,
ptN o xs l pt is challenge number i. -/
theorem ptN_at {o : List ℕ} {m : ℕ} (O : Ord o m) (xs : List K) : ∀ (l : ℕ), l ≤ m →
    ∀ (pt : List K), pt.length = m → ∀ i < l, (ptN o xs l pt).getD (o.getD i 0) 0 = xs.getD i 0
  | 0, _, _, _, i, hi => by omega
  | l + 1, hl, pt, hp, i, hi => by
    show (ptN o xs l (pt.set _ _)).getD _ 0 = _
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h1 | h1
    · exact ptN_at O xs l (by omega) _ (by rw [List.length_set]; exact hp) i h1
    · subst h1
      rw [ptN_off o xs i _ _ fun j hj e => by
        have := O.inj j (by omega) i (by omega) e
        omega, List.getD_eq_getElem?_getD,
        List.getElem?_set_self (by rw [hp]; exact O.lt i (by omega))]
      rfl

/-- Under Ord o m, for l ≤ m and pt of m coordinates with 0 at the coordinates of the first l
rounds: the extension of foldN o xs f l at pt is the extension of f at ptN o xs l pt. -/
theorem ext_foldN {o : List ℕ} {m : ℕ} (O : Ord o m) (f : ℕ → K) (xs : List K) : ∀ (l : ℕ),
    l ≤ m → ∀ (pt : List K), pt.length = m → (∀ i < l, pt.getD (o.getD i 0) 0 = 0) →
    ext m (foldN o xs f l) pt = ext m f (ptN o xs l pt)
  | 0, _, _, _, _ => rfl
  | l + 1, hl, pt, hp, h0 => by
    show ext m (fixAt (o.getD l 0) (xs.getD l 0) (foldN o xs f l)) pt = _
    rw [ext_fixAt m _ _ _ pt hp (O.lt l (by omega)) (h0 l (by omega))]
    refine ext_foldN O f xs l (by omega) _ (by rw [List.length_set]; exact hp) fun i hi => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (fun e => by
      have := O.inj l (by omega) i (by omega) e
      omega), ← List.getD_eq_getElem?_getD]
    exact h0 i (by omega)

/-- Under Ord o m, for o without repeats: the point 0 with all m rounds' challenges put in is
TwV.byVar o xs. -/
theorem ptN_byVar {o : List ℕ} {m : ℕ} (O : Ord o m) (hnd : o.Nodup) (xs : List K) :
    ptN o xs m (List.replicate m 0) = byVar o xs := by
  have hl : (ptN o xs m (List.replicate m (0 : K))).length = m := by
    rw [ptN_length, List.length_replicate]
  refine List.ext_getElem (by
    rw [hl]
    unfold byVar
    rw [List.length_map, List.length_range, O.len]) fun c h1 h2 => ?_
  have hc : c < m := by omega
  obtain ⟨i, hi, e⟩ := O.onto c hc
  have hio : i < o.length := by rw [O.len]; exact hi
  have e' : o[i] = c := by rw [← List.getD_eq_getElem _ 0 hio]; exact e
  have h3 := ptN_at O xs m (le_refl m) (List.replicate m 0) List.length_replicate i hi
  rw [e, List.getD_eq_getElem _ _ h1] at h3
  rw [h3]
  unfold byVar
  rw [List.getElem_map, List.getElem_range, ← e', List.Nodup.idxOf_getElem hnd]

/-- Under Ord o m, for o without repeats: behind all m rounds the folded function is, at the corner
0, the extension of f at TwV.byVar o xs. -/
theorem foldN_zero {o : List ℕ} {m : ℕ} (O : Ord o m) (hnd : o.Nodup) (f : ℕ → K)
    (xs : List K) : foldN o xs f m 0 = ext m f (byVar o xs) := by
  have hz : ∀ c, (List.replicate m (0 : K)).getD c 0 = 0 := fun c => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  rw [← ptN_byVar O hnd xs, ← ext_foldN O f xs m (le_refl m) _ List.length_replicate
    fun i _ => hz _]
  exact (sum_eqN_zeros m _).symm

/-- Under Ord o m, for o without repeats and z of m coordinates: lvlSum behind all m rounds is
κ + A B at the point TwV.byVar o xs, A and B read as extensions. -/
theorem lvlSum_last {m : ℕ} (κ : K) (A B : ℕ → K) {o : List ℕ} (O : Ord o m) (hnd : o.Nodup)
    (z xs : List K) (hz : z.length = m) :
    lvlSum m κ A B o z xs m = κ + ext m A (byVar o xs) * ext m B (byVar o xs) := by
  unfold lvlSum
  rw [wtN_all O z hz, sum_eqN_zeros, foldN_zero O hnd, foldN_zero O hnd]

/-! ## The run, whole -/

/-- Under Ord o m, for z and xs of m entries each: from round l on the round polynomials are Chained
from lvlSum behind l rounds to lvlSum behind all m. -/
theorem chained_from {m : ℕ} (κ : K) (A B : ℕ → K) {o : List ℕ} (O : Ord o m) (z xs : List K)
    (hz : z.length = m) (hx : xs.length = m) : ∀ k l, l + k = m →
    Chained (lvlSum m κ A B o z xs l) ((inRounds o z).drop l)
      (((List.range m).map fun i => pjRound m κ A B o z (xs.take i)).drop l) (xs.drop l)
      (lvlSum m κ A B o z xs m)
  | 0, l, h => by
    have e : l = m := by omega
    subst e
    rw [List.drop_of_length_le (by unfold inRounds; rw [List.length_map, O.len]),
      List.drop_of_length_le (by rw [List.length_map, List.length_range]),
      List.drop_of_length_le (by rw [hx])]
    rfl
  | k + 1, l, h => by
    have hl : l < m := by omega
    have h1 : l < (inRounds o z).length := by unfold inRounds; rw [List.length_map, O.len]; exact hl
    have h2 : l < ((List.range m).map fun i => pjRound m κ A B o z (xs.take i)).length := by
      rw [List.length_map, List.length_range]
      exact hl
    have h3 : l < xs.length := by omega
    rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2, List.drop_eq_getElem_cons h3]
    have e1 : (inRounds o z)[l] = z.getD (o.getD l 0) 0 := by
      unfold inRounds
      rw [List.getElem_map, List.getD_eq_getElem o 0 (by rw [O.len]; exact hl)]
    have e2 : ((List.range m).map fun i => pjRound m κ A B o z (xs.take i))[l] =
        pjRound m κ A B o z (xs.take l) := by
      rw [List.getElem_map, List.getElem_range]
    have e3 : xs[l] = xs.getD l 0 := (List.getD_eq_getElem _ _ h3).symm
    rw [e1, e2, e3]
    refine ⟨wsum_round κ A B O z xs hz hl (by omega), ?_⟩
    rw [evalP_round κ A B o z xs (by omega)]
    exact chained_from κ A B O z xs hz hx k (l + 1) (by omega)

/-- If o lists the coordinates below m, each once, and z has m coordinates, pj m κ A B o z is
lawful. -/
theorem pj_lawful (m : ℕ) (κ : K) (A B : ℕ → K) (o : List ℕ) (z : List K)
    (ho : o.Perm (List.range m)) (hz : z.length = m) : (pj m κ A B o z).Lawful := by
  have O := ord_of_perm ho
  have hnd : o.Nodup := ho.symm.nodup List.nodup_range
  have hzs : (pj m κ A B o z).zs.length = m := by
    show (inRounds o z).length = m
    unfold inRounds
    rw [List.length_map, O.len]
  refine ⟨fun xs hx => ?_, fun _ xs mk β _ hm => ?_⟩
  · rw [hzs] at hx
    have h := chained_from κ A B O z xs hz hx m 0 (by omega)
    rw [lvlSum_last κ A B O hnd z xs hz] at h
    unfold Job.gs
    rw [hzs]
    exact h
  · obtain ⟨m0, m1, rfl⟩ : ∃ m0 m1, mk = [m0, m1] := by
      match mk, hm with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    refine ⟨?_, ?_⟩
    · show κ + _ * _ + 0 * _ = κ + _ * _
      ring
    · show evalP [_, _, _] β = κ + (shownL β [_, _] [m0, m1]).getD 0 0 *
        (shownL β [_, _] [m0, m1]).getD 1 0
      simp only [evalP, evalGo, List.headD_cons, List.tail_cons, shownL, List.zipWith_cons_cons,
        List.getD_cons_zero, List.getD_cons_succ]
      ring

end

/-! ## The line; a round of degree 1 -/

section
variable {K : Type} [Field K]

/-- For r of m coordinates: (1 - ρ) times the extension of the first 2^m entries of f at r, plus ρ
times that of the next 2^m, is the extension of the first 2^(m+1) at (r, ρ), ρ the new highest
coordinate. -/
theorem ext_line (m : ℕ) (f : ℕ → K) (r : List K) (ρ : K) (hr : r.length = m) :
    (1 - ρ) * ext m f r + ρ * ext m (fun X => f (X + 2 ^ m)) r = ext (m + 1) f (r ++ [ρ]) := by
  have hp : 0 < 2 ^ m := by positivity
  unfold ext
  rw [pow_succ, Nat.mul_two, sum_range_add, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun X hX => ?_
    have hX' := mem_range.1 hX
    have e3 : eqN [ρ] 0 = 1 - ρ := by simp [eqN]
    rw [_root_.Fo.eqN_append, hr, Nat.mod_eq_of_lt hX', Nat.div_eq_of_lt hX', e3]
    ring
  · refine sum_congr rfl fun X hX => ?_
    have hX' := mem_range.1 hX
    have e1 : (2 ^ m + X) % 2 ^ m = X := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hX']
    have e2 : (2 ^ m + X) / 2 ^ m = 1 := by
      rw [Nat.add_div_left _ hp, Nat.div_eq_of_lt hX']
    have e3 : eqN [ρ] 1 = ρ := by simp [eqN]
    rw [_root_.Fo.eqN_append, hr, e1, e2, e3, Nat.add_comm (2 ^ m) X]
    ring

/-- Putting two different bits commutes. -/
theorem setBit_comm : ∀ (c c' : ℕ), c ≠ c' → ∀ (b b' : Bool) (X : ℕ),
    setBit c b (setBit c' b' X) = setBit c' b' (setBit c b X)
  | 0, 0, h, _, _, _ => absurd rfl h
  | 0, c' + 1, _, b, b', X => by
    show 2 * ((2 * setBit c' b' (X / 2) + X % 2) / 2) + b.toNat =
      2 * setBit c' b' ((2 * (X / 2) + b.toNat) / 2) + (2 * (X / 2) + b.toNat) % 2
    have hb : b.toNat < 2 := by cases b <;> decide
    have e1 : (2 * (X / 2) + b.toNat) / 2 = X / 2 := by omega
    have e2 : (2 * (X / 2) + b.toNat) % 2 = b.toNat := by omega
    rw [e1, e2]
    omega
  | c + 1, 0, _, b, b', X => by
    show 2 * setBit c b ((2 * (X / 2) + b'.toNat) / 2) + (2 * (X / 2) + b'.toNat) % 2 =
      2 * ((2 * setBit c b (X / 2) + X % 2) / 2) + b'.toNat
    have hb : b'.toNat < 2 := by cases b' <;> decide
    have e1 : (2 * (X / 2) + b'.toNat) / 2 = X / 2 := by omega
    have e2 : (2 * (X / 2) + b'.toNat) % 2 = b'.toNat := by omega
    rw [e1, e2]
    omega
  | c + 1, c' + 1, h, b, b', X => by
    show 2 * setBit c b ((2 * setBit c' b' (X / 2) + X % 2) / 2) +
        (2 * setBit c' b' (X / 2) + X % 2) % 2 =
      2 * setBit c' b' ((2 * setBit c b (X / 2) + X % 2) / 2) +
        (2 * setBit c b (X / 2) + X % 2) % 2
    have e1 : ∀ s : ℕ, (2 * s + X % 2) / 2 = s := fun s => by omega
    have e2 : ∀ s : ℕ, (2 * s + X % 2) % 2 = X % 2 := fun s => by omega
    rw [e1, e1, e2, e2, setBit_comm c c' (fun e => h (by rw [e])) b b' (X / 2)]

/-- A function that does not read bit c still does not read it behind rounds that take other
coordinates. -/
theorem foldN_skips (o : List ℕ) (rs : List K) (f : ℕ → K) (c : ℕ)
    (hf : ∀ (b : Bool) (X : ℕ), f (setBit c b X) = f X) : ∀ l, (∀ i < l, o.getD i 0 ≠ c) →
    ∀ (b : Bool) (X : ℕ), foldN o rs f l (setBit c b X) = foldN o rs f l X
  | 0, _, b, X => hf b X
  | l + 1, h, b, X => by
    show fixAt _ _ (foldN o rs f l) (setBit c b X) = fixAt _ _ (foldN o rs f l) X
    unfold fixAt
    rw [setBit_comm _ c (h l (by omega)), setBit_comm _ c (h l (by omega)),
      foldN_skips o rs f c hf l (fun i hi => h i (by omega)),
      foldN_skips o rs f c hf l (fun i hi => h i (by omega))]

/-- If o is a permutation of the numbers below m, fewer than m challenges rs stand in front, and B
does not read the bit of the round's coordinate, then the third coefficient of pjRound m κ A B o z
rs is 0. -/
theorem pjRound_deg1 (m : ℕ) (κ : K) (A B : ℕ → K) (o : List ℕ) (z rs : List K)
    (ho : o.Perm (List.range m)) (hl : rs.length < m)
    (hB : ∀ (b : Bool) (X : ℕ), B (setBit (o.getD rs.length 0) b X) = B X) :
    (pjRound m κ A B o z rs).getD 2 0 = 0 := by
  have O := ord_of_perm ho
  have hs := foldN_skips o rs B _ hB rs.length fun i hi e => by
    have := O.inj i (by omega) rs.length hl e
    omega
  show ∑ X ∈ range (2 ^ m), _ * (_ * (foldN o rs B rs.length (setBit _ true X) -
    foldN o rs B rs.length (setBit _ false X))) = 0
  refine sum_eq_zero fun X _ => ?_
  rw [hs true X, hs false X]
  ring

end

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.sum_range_two
#print axioms OnBytes.HonestTrace.Look.eqN_even
#print axioms OnBytes.HonestTrace.Look.eqN_odd
#print axioms OnBytes.HonestTrace.Look.sum_cons
#print axioms OnBytes.HonestTrace.Look.sum_eqN_split
#print axioms OnBytes.HonestTrace.Look.sum_eqN_zeros
#print axioms OnBytes.HonestTrace.Look.wtN_length
#print axioms OnBytes.HonestTrace.Look.wtN_getD
#print axioms OnBytes.HonestTrace.Look.set_getD_self
#print axioms OnBytes.HonestTrace.Look.wtN_zero
#print axioms OnBytes.HonestTrace.Look.ord_of_perm
#print axioms OnBytes.HonestTrace.Look.wtN_all
#print axioms OnBytes.HonestTrace.Look.foldN_congr
#print axioms OnBytes.HonestTrace.Look.foldN_take
#print axioms OnBytes.HonestTrace.Look.wsum_round
#print axioms OnBytes.HonestTrace.Look.evalP_round
#print axioms OnBytes.HonestTrace.Look.ext_fixAt
#print axioms OnBytes.HonestTrace.Look.ptN_length
#print axioms OnBytes.HonestTrace.Look.ptN_off
#print axioms OnBytes.HonestTrace.Look.ptN_at
#print axioms OnBytes.HonestTrace.Look.ext_foldN
#print axioms OnBytes.HonestTrace.Look.ptN_byVar
#print axioms OnBytes.HonestTrace.Look.foldN_zero
#print axioms OnBytes.HonestTrace.Look.lvlSum_last
#print axioms OnBytes.HonestTrace.Look.chained_from
#print axioms OnBytes.HonestTrace.Look.pj_lawful
#print axioms OnBytes.HonestTrace.Look.ext_line
#print axioms OnBytes.HonestTrace.Look.setBit_comm
#print axioms OnBytes.HonestTrace.Look.foldN_skips
#print axioms OnBytes.HonestTrace.Look.pjRound_deg1
