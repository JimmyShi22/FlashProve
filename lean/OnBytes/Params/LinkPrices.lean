-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/LinkPrices.lean: that the planner's prices of a link's fold point and of its lists of
columns cover counts of the proof library's form.

A link ties a further copy of the stored table to the first one (`planLink`,
OnBytes/Params/Planner.lean). The price of its fold point is `fieldError` at the
table's v row variables and, for each of the two tables, `tableFoldError`: the sum over the v steps
of a fold of one closeness term `mcaError`, and the list size times v / q. `tableFoldShares` is what
the sum encloses (`enclR_tableFoldTerms`); it is at least v times cnt / q (`le_tableFoldShares`). So
`tableFoldError` encloses a number that is at least (v B + L v) / q, for B at most what the count
encloses and L at most the list size (`tableFold_covers`), and the price of the fold point
covers (v + (v B1 + L1 v) + (v B0 + L0 v)) / q (`link_point_covers`). For a table whose
distances are given by integers, with m as printed, k > 0 and both counts not marked bad, the B can
be the library's `Cb.bchksBound` and the L its `Cb.listMax`, at a radius for each table: the further
table's at most 1 less the one-time test's agreement, times the length, the first table's at most 1
less a later test's (`link_point_covers_johnson`); and the like in whole numbers, with the counts
rounded down (`link_point_covers_floor`). The message with the two lists of columns has as its price
the larger of the two agreements' powers; it covers the larger of ((n - e0 - 1) / n) ^ t0 and ((n -
ej - 1) / n) ^ tj (`link_positions_cover`; at a table with integers, for radii from the upper radii
on: `link_positions_cover_johnson`).

Main definition: `tableFoldShares`.
Main theorems: `enclR_tableFoldTerms`, `le_tableFoldShares`, `tableFold_covers`,
`link_point_covers`, `link_positions_cover`, `link_point_covers_johnson`, `link_point_covers_floor`,
`link_positions_cover_johnson`.
What is not claimed: that the numbers on the left bound a prover's chance: their form is meant to be
that of the library's lemmas on a link; no such lemma is imported or compared here.
OnBytes/Slice/PricedRound.lean makes the comparison (`point_share`, `loc_share`): at the format's
field, for sizes that are those of the planner's table, the library's counts of the fold point and
of the positions of a link are at most `linkPointCount` and `linkPositionsShare`
(OnBytes/Params/EntryCovered.lean: the numbers on the left of `link_point_covers_floor` and
`link_positions_cover_johnson`) times the number of the round's typed values. A whole number above
the library's count: see the head of OnBytes/Params/GroupPrices.lean. That `planLink` closes its
rounds at these prices: by its text; no law here. The link's round of seeds (`send_two_covers`,
OnBytes/Params/MorePrices.lean), its last point (`fieldError`), and its proximity test
(OnBytes/Params/GroupPrices.lean). The point of the test on a table, whose price has one
`tableFoldError` (`tableFold_covers` speaks of it). That a price is not
marked bad is a hypothesis. For proofs only; the program, that is the Lean port built from OnBytes/,
does not import this file.

-/
import OnBytes.Params.MorePrices

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- The number that `tableFoldTerms` encloses from y on, at a count that encloses cnt. -/
noncomputable def tableFoldShares (s : Setting) (v : ℕ) (x : Proximity) (cnt : ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, y => y
  | fuel + 1, j, y => tableFoldShares s v x cnt fuel (j + 1) (y + mcaShare s x (2 ^ (v - j)) cnt)

/-- `tableFoldTerms` from a bound that encloses y encloses `tableFoldShares` from y. -/
theorem enclR_tableFoldTerms (s : Setting) (v : ℕ) (x : Proximity) {cnt : ℝ}
    (hx : EnclR x.count cnt) : ∀ (fuel j : ℕ) {e : Bound} {y : ℝ}, EnclR e y →
      EnclR (tableFoldTerms s v x fuel j e) (tableFoldShares s v x cnt fuel j y)
  | 0, _, _, _, h => h
  | fuel + 1, j, _, _, h =>
    enclR_tableFoldTerms s v x hx fuel (j + 1) (enclR_add h (enclR_mcaError s x (2 ^ (v - j)) hx))

/-- The shares are at least y and cnt / q for each step, if cnt is not negative. -/
theorem le_tableFoldShares (s : Setting) (v : ℕ) (x : Proximity) {cnt : ℝ} (h0 : 0 ≤ cnt) :
    ∀ (fuel j : ℕ) (y : ℝ),
      y + (fuel : ℝ) * (cnt / (s.cardE : ℝ)) ≤ tableFoldShares s v x cnt fuel j y
  | 0, _, y => by simp [tableFoldShares]
  | fuel + 1, j, y => by
    have ih := le_tableFoldShares s v x h0 fuel (j + 1) (y + mcaShare s x (2 ^ (v - j)) cnt)
    have h1 := le_mcaShare s x (rows := 2 ^ (v - j)) h0 Nat.one_le_two_pow
    show _ ≤ tableFoldShares s v x cnt fuel (j + 1) (y + mcaShare s x (2 ^ (v - j)) cnt)
    push_cast
    linarith

/-- **The closeness term of a fold of all rows of a table covers (v B + L v) / q**, for B at most
what the count encloses and L at most the list size. -/
theorem tableFold_covers (s : Setting) (T : TableSize) (x : Proximity) {cnt B : ℝ} {L : ℕ}
    (hx : EnclR x.count cnt) (hB : B ≤ cnt) (h0 : 0 ≤ cnt) (hL : L ≤ x.list) :
    ∃ w : ℝ, EnclR (tableFoldError s T x) w ∧
      ((T.v : ℝ) * B + (L : ℝ) * (T.v : ℝ)) / (s.cardE : ℝ) ≤ w := by
  refine ⟨tableFoldShares s T.v x cnt T.v 1 ((0 : ℕ) : ℝ) +
    (x.list : ℝ) * ((T.v : ℝ) / (s.cardE : ℝ)), ?_, ?_⟩
  · unfold tableFoldError
    exact enclR_add (enclR_tableFoldTerms s T.v x hx T.v 1 (enclR_ofWord 0))
      (enclR_mul (enclR_ofNat x.list) (enclR_fieldError s T.v))
  · have h1 := le_tableFoldShares s T.v x h0 T.v 1 ((0 : ℕ) : ℝ)
    have hq : (0 : ℝ) ≤ (s.cardE : ℝ) := Nat.cast_nonneg _
    have hv : (0 : ℝ) ≤ (T.v : ℝ) := Nat.cast_nonneg _
    have hL' : (L : ℝ) ≤ (x.list : ℝ) := by exact_mod_cast hL
    have h2 : (T.v : ℝ) * B / (s.cardE : ℝ) ≤ (T.v : ℝ) * (cnt / (s.cardE : ℝ)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hB hq) hv
    have h3 : (L : ℝ) * (T.v : ℝ) / (s.cardE : ℝ) ≤ (x.list : ℝ) * ((T.v : ℝ) / (s.cardE : ℝ)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hL' (by positivity)
    rw [add_div]
    push_cast at h1
    linarith

/-- **The price of a link's fold point covers (v + (v B1 + L1 v) + (v B0 + L0 v)) /
q**: B1, L1 for the further table, at the one-time test's distance; B0, L0 for the first table, at a
later test's. -/
theorem link_point_covers (s : Setting) (T : TableSize) (x1 x0 : Proximity) {c1 c0 B1 B0 : ℝ}
    {L1 L0 : ℕ} (h1 : EnclR x1.count c1) (h0 : EnclR x0.count c0) (hB1 : B1 ≤ c1) (hB0 : B0 ≤ c0)
    (n1 : 0 ≤ c1) (n0 : 0 ≤ c0) (hL1 : L1 ≤ x1.list) (hL0 : L0 ≤ x0.list)
    (g : (fieldError s T.v + tableFoldError s T x1 + tableFoldError s T x0).bad = false) :
    ((T.v : ℝ) + ((T.v : ℝ) * B1 + (L1 : ℝ) * (T.v : ℝ)) +
        ((T.v : ℝ) * B0 + (L0 : ℝ) * (T.v : ℝ))) / (s.cardE : ℝ) ≤
      (((fieldError s T.v + tableFoldError s T x1 + tableFoldError s T x0).error.val : ℚ) : ℝ) := by
  obtain ⟨w1, e1, l1⟩ := tableFold_covers s T x1 h1 hB1 n1 hL1
  obtain ⟨w0, e0, l0⟩ := tableFold_covers s T x0 h0 hB0 n0 hL0
  refine le_trans ?_ (le_errorR (enclR_add (enclR_add (enclR_fieldError s T.v) e1) e0) g)
  rw [add_div, add_div]
  linarith

/-- **The price of the message with a link's two lists of columns covers both lists' shares.** -/
theorem link_positions_cover {a0 aj : Bound} {x0 xj : ℝ} {n e0 ej : ℕ} (t0 tj : ℕ)
    (h0 : EnclR a0 x0) (hj : EnclR aj xj) (hn : 0 < n)
    (r0 : ((n - e0 - 1 : ℕ) : ℝ) ≤ x0 * (n : ℝ)) (rj : ((n - ej - 1 : ℕ) : ℝ) ≤ xj * (n : ℝ))
    (g0 : (Bound.pow a0 t0).bad = false) (gj : (Bound.pow aj tj).bad = false) :
    max ((((n - e0 - 1 : ℕ) : ℝ) / (n : ℝ)) ^ t0) ((((n - ej - 1 : ℕ) : ℝ) / (n : ℝ)) ^ tj) ≤
      (((if (Bound.pow a0 t0).hi.lt (Bound.pow aj tj).hi then Bound.pow aj tj
        else Bound.pow a0 t0).error.val : ℚ) : ℝ) := by
  have p0 := positions_cover t0 h0 hn r0 g0
  have pj := positions_cover tj hj hn rj gj
  have E0 : (Bound.pow a0 t0).error = (Bound.pow a0 t0).hi := by unfold Bound.error; rw [g0]; rfl
  have Ej : (Bound.pow aj tj).error = (Bound.pow aj tj).hi := by unfold Bound.error; rw [gj]; rfl
  rw [E0] at p0
  rw [Ej] at pj
  split
  · rename_i hlt
    rw [Ej]
    have hv : ((Bound.pow a0 t0).hi.val : ℚ) < (Bound.pow aj tj).hi.val := Binary.lt_sound _ _ hlt
    have hv' : (((Bound.pow a0 t0).hi.val : ℚ) : ℝ) ≤ (((Bound.pow aj tj).hi.val : ℚ) : ℝ) := by
      exact_mod_cast hv.le
    exact max_le (p0.trans hv') pj
  · rename_i hlt
    rw [E0]
    have hv : ((Bound.pow aj tj).hi.val : ℚ) ≤ (Bound.pow a0 t0).hi.val :=
      Binary.le_of_not_lt _ _ (by simpa using hlt)
    have hv' : (((Bound.pow aj tj).hi.val : ℚ) : ℝ) ≤ (((Bound.pow a0 t0).hi.val : ℚ) : ℝ) := by
      exact_mod_cast hv
    exact max_le p0 (pj.trans hv')

/-- **The price of a link's fold point at a table with integers covers the library's numbers**: with
m as printed, k > 0 and the two counts not marked bad; e1 is a radius of the further table, at most
1 less the one-time test's agreement, times the length; e0 one of the first table, at most 1 less a
later test's. For each table: v times the library's count, and its bound on the list times v; and v
more; all over q. -/
theorem link_point_covers_johnson {s : Setting} {T : TableSize} {e1 e0 : ℕ}
    (hM : T.distances.mOnce ≠ 0) (hp : s.printed = true)
    (g1 : (tableAnalysis s T).once.count.bad = false)
    (g0 : (tableAnalysis s T).later.count.bad = false) (hk : 0 < (wordOf T.code).k)
    (h1 : (e1 : ℝ) ≤
      (1 - (wordOf T.code).agreeAt T.distances.mOnce true) * ((wordOf T.code).n : ℝ))
    (h0 : (e0 : ℝ) ≤
      (1 - (wordOf T.code).agreeAt T.distances.mLater true) * ((wordOf T.code).n : ℝ))
    (g : (fieldError s T.v + tableFoldError s T (tableAnalysis s T).once +
      tableFoldError s T (tableAnalysis s T).later).bad = false) :
    ((T.v : ℝ) +
        ((T.v : ℝ) * Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e1 +
          (Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e1 : ℝ) *
            (T.v : ℝ)) +
        ((T.v : ℝ) * Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e0 +
          (Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e0 : ℝ) *
            (T.v : ℝ))) / (s.cardE : ℝ) ≤
      (((fieldError s T.v + tableFoldError s T (tableAnalysis s T).once +
        tableFoldError s T (tableAnalysis s T).later).error.val : ℚ) : ℝ) := by
  obtain ⟨a1, a0⟩ := tableAnalysis_fromM (s := s) hM
  rw [hp] at a1 a0
  rw [a1, a0] at g ⊢
  rw [a1] at g1
  rw [a0] at g0
  have c1 := enclR_johnson_count (wordOf T.code) T.distances.mOnce true
  have c0 := enclR_johnson_count (wordOf T.code) T.distances.mLater true
  exact link_point_covers s T _ _ c1 c0
    (bchksBound_le_countAt (johnson_count_good g1).1 hk le_rfl h1)
    (bchksBound_le_countAt (johnson_count_good g0).1 hk le_rfl h0)
    (enclR_nonneg c1 g1) (enclR_nonneg c0 g0) (listMax_le_list g1 hk h1)
    (listMax_le_list g0 hk h0) g

/-- **The same in whole numbers**, with the library's two counts rounded down. -/
theorem link_point_covers_floor {s : Setting} {T : TableSize} {e1 e0 : ℕ}
    (hM : T.distances.mOnce ≠ 0) (hp : s.printed = true)
    (g1 : (tableAnalysis s T).once.count.bad = false)
    (g0 : (tableAnalysis s T).later.count.bad = false) (hk : 0 < (wordOf T.code).k)
    (h1 : (e1 : ℝ) ≤
      (1 - (wordOf T.code).agreeAt T.distances.mOnce true) * ((wordOf T.code).n : ℝ))
    (h0 : (e0 : ℝ) ≤
      (1 - (wordOf T.code).agreeAt T.distances.mLater true) * ((wordOf T.code).n : ℝ))
    (g : (fieldError s T.v + tableFoldError s T (tableAnalysis s T).once +
      tableFoldError s T (tableAnalysis s T).later).bad = false) :
    (((T.v + (T.v * ⌊Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e1⌋₊ +
          Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e1 * T.v) +
        (T.v * ⌊Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e0⌋₊ +
          Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e0 * T.v) :
        ℕ) : ℝ)) / (s.cardE : ℝ) ≤
      (((fieldError s T.v + tableFoldError s T (tableAnalysis s T).once +
        tableFoldError s T (tableAnalysis s T).later).error.val : ℚ) : ℝ) := by
  refine le_trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
    (link_point_covers_johnson hM hp g1 g0 hk h1 h0 g)
  have hv : (0 : ℝ) ≤ (T.v : ℝ) := Nat.cast_nonneg _
  have f1 := mul_le_mul_of_nonneg_left
    (Nat.floor_le (bchksBound_nonneg (wordOf T.code).n (wordOf T.code).k e1)) hv
  have f0 := mul_le_mul_of_nonneg_left
    (Nat.floor_le (bchksBound_nonneg (wordOf T.code).n (wordOf T.code).k e0)) hv
  push_cast
  linarith

/-- **The price of the message with a link's two lists of columns, at a table with integers**: e0 is
a radius of the first table, from the upper radius of a later test's distance on; ej one of the
further table, from the upper radius of the one-time test's distance on. With m as printed. -/
theorem link_positions_cover_johnson {s : Setting} {T : TableSize} {e0 ej : ℕ} (t0 tj : ℕ)
    (hM : T.distances.mOnce ≠ 0) (hp : s.printed = true)
    (p0 : ((tableAnalysis s T).later.delta * Bound.ofNat (wordOf T.code).n).bad = false)
    (u0 : upperRadius (tableAnalysis s T).later.delta (wordOf T.code).n ≤ e0)
    (pj : ((tableAnalysis s T).once.delta * Bound.ofNat (wordOf T.code).n).bad = false)
    (uj : upperRadius (tableAnalysis s T).once.delta (wordOf T.code).n ≤ ej)
    (g0 : (Bound.pow (tableAnalysis s T).later.agree t0).bad = false)
    (gj : (Bound.pow (tableAnalysis s T).once.agree tj).bad = false) :
    max (((((wordOf T.code).n - e0 - 1 : ℕ) : ℝ) / ((wordOf T.code).n : ℝ)) ^ t0)
        (((((wordOf T.code).n - ej - 1 : ℕ) : ℝ) / ((wordOf T.code).n : ℝ)) ^ tj) ≤
      (((if (Bound.pow (tableAnalysis s T).later.agree t0).hi.lt
          (Bound.pow (tableAnalysis s T).once.agree tj).hi
        then Bound.pow (tableAnalysis s T).once.agree tj
        else Bound.pow (tableAnalysis s T).later.agree t0).error.val : ℚ) : ℝ) := by
  obtain ⟨a1, a0⟩ := tableAnalysis_fromM (s := s) hM
  rw [hp] at a1 a0
  have hA0 : EnclR (tableAnalysis s T).later.agree
      ((wordOf T.code).agreeAt T.distances.mLater true) := by
    rw [a0]
    exact enclR_johnson_agree _ _ _
  have hD0 : EnclR (tableAnalysis s T).later.delta
      (1 - (wordOf T.code).agreeAt T.distances.mLater true) := by
    rw [a0]
    exact enclR_johnson_delta _ _ _
  have hAj : EnclR (tableAnalysis s T).once.agree
      ((wordOf T.code).agreeAt T.distances.mOnce true) := by
    rw [a1]
    exact enclR_johnson_agree _ _ _
  have hDj : EnclR (tableAnalysis s T).once.delta
      (1 - (wordOf T.code).agreeAt T.distances.mOnce true) := by
    rw [a1]
    exact enclR_johnson_delta _ _ _
  have hn : 0 < (wordOf T.code).n := by unfold Word.n; positivity
  exact link_positions_cover t0 tj hA0 hAj hn
    (agree_of_upperRadius hD0 p0 u0 (agreeAt_nonneg _ _ _))
    (agree_of_upperRadius hDj pj uj (agreeAt_nonneg _ _ _)) g0 gj

end OnBytes.Params

#print axioms OnBytes.Params.link_positions_cover_johnson
#print axioms OnBytes.Params.link_point_covers_floor
#print axioms OnBytes.Params.link_point_covers_johnson
#print axioms OnBytes.Params.enclR_tableFoldTerms
#print axioms OnBytes.Params.le_tableFoldShares
#print axioms OnBytes.Params.tableFold_covers
#print axioms OnBytes.Params.link_point_covers
#print axioms OnBytes.Params.link_positions_cover
