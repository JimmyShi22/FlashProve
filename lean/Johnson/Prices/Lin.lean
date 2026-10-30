-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/Lin.lean: every plan of a proof's shared chain, at a table with a record, pays at its
rounds LIN point and LOC for counts of the proof library's form.

The first round of a shared chain (place 0) is LIN point: the verifier draws v + kLo elements of the
extension field, v being the table's row variables. With a record, in a test that is no one-time
test, its price is the number of requests times `fieldError` at v + kLo, and `tableFoldError` at a
later test's distance. It covers (N (v + kLo) + c) |E| ^ (v + kLo - 1) of the |E| ^ (v + kLo)
points, for every whole number c that is at most v B + L v, B being the library's `Cb.bchksBound`
and L its `Cb.listMax` at the table's code and a radius e that is at most 1 less a later test's
agreement, times the length (`lin_point_covers`, `point_pays`). The fourth round (place 3) is LOC:
the verifier draws as many positions of the table's code as the shape has columns. Its price covers
g ^ columns of the n ^ columns lists, for every g that is at most n - e - 1, e being a radius from
the upper radius of a later test's distance on (`loc_covers`, `loc_pays`). All at every setting and
all sizes under the named conditions: nothing is evaluated.

Main definitions: `PointPaysOf`, `LocPaysOf`.
Main theorems: `covers_of_real`, `lin_point_covers`, `covers_point`, `loc_covers`, `point_pays`,
`loc_pays`.
What is not claimed: that `sharedPlan` returns a plan at any values, or that the conditions hold at
any. That the counts bound a prover's chance: their form is meant to be that of `LdLinP.errPt` and
`LdLinP.errLoc` (Cb/Ld/LdLin.lean), which is not imported. One radius for both rounds: LIN point
asks a radius up to the lower radius, LOC one from the upper radius on. What the heads of
Johnson/Prices/Pays.lean and OnBytes/Params/LinkPrices.lean do not claim.

-/
import Johnson.Prices.Zeta
import OnBytes.Params.LinkPrices
import OnBytes.Plan.PlanListsConfigure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices
open Bound

/-- `Covers` from the same inequality between real numbers. -/
theorem covers_of_real {r : PlanRound} {count total : ℕ}
    (h : (count : ℝ) ≤ ((r.error.val : ℚ) : ℝ) * (total : ℝ)) : Covers r count total := by
  unfold Covers
  exact_mod_cast h

/-- **The price of LIN point at a table with integers covers the library's numbers**: N d, and for
the table v times the library's count and its bound on the list times v; all over q. -/
theorem lin_point_covers {s : Setting} {T : TableSize} {N d e0 : ℕ}
    (hM : T.distances.mOnce ≠ 0) (hp : s.printed = true)
    (g0 : (tableAnalysis s T).later.count.bad = false) (hk : 0 < (wordOf T.code).k)
    (h0 : (e0 : ℝ) ≤
      (1 - (wordOf T.code).agreeAt T.distances.mLater true) * ((wordOf T.code).n : ℝ))
    (g : (Bound.ofNat N * fieldError s d +
      tableFoldError s T (tableAnalysis s T).later).bad = false) :
    ((N : ℝ) * (d : ℝ) +
        ((T.v : ℝ) * Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e0 +
          (Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e0 : ℝ) *
            (T.v : ℝ))) / (s.cardE : ℝ) ≤
      (((Bound.ofNat N * fieldError s d +
        tableFoldError s T (tableAnalysis s T).later).error.val : ℚ) : ℝ) := by
  obtain ⟨_, a0⟩ := tableAnalysis_fromM (s := s) hM
  rw [hp] at a0
  rw [a0] at g ⊢
  rw [a0] at g0
  have c0 := enclR_johnson_count (wordOf T.code) T.distances.mLater true
  obtain ⟨w0, e0', l0⟩ := tableFold_covers s T _ c0
    (bchksBound_le_countAt (johnson_count_good g0).1 hk le_rfl h0) (enclR_nonneg c0 g0)
    (listMax_le_list g0 hk h0)
  refine le_trans ?_
    (le_errorR (enclR_add (enclR_mul (enclR_ofNat N) (enclR_fieldError s d)) e0') g)
  rw [add_div, mul_div_assoc]
  linarith

/-- A price that is at least (a + c') / q covers (a + c) q ^ (d - 1) of the q ^ d points, for a
whole number c that is at most c', and d > 0. -/
theorem covers_point {r : PlanRound} {q a c d : ℕ} {c' : ℝ} (hq : 0 < q) (hd : 0 < d)
    (h : ((a : ℝ) + c') / (q : ℝ) ≤ ((r.error.val : ℚ) : ℝ)) (hc : (c : ℝ) ≤ c') :
    Covers r ((a + c) * q ^ (d - 1)) (q ^ d) := by
  apply covers_of_real
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [Nat.add_sub_cancel]
  push_cast
  have h1 : ((a : ℝ) + (c : ℝ)) / (q : ℝ) ≤ ((r.error.val : ℚ) : ℝ) :=
    le_trans (div_le_div_of_nonneg_right (by linarith) hq'.le) h
  have h2 : ((a : ℝ) + (c : ℝ)) * (q : ℝ) ^ j =
      ((a : ℝ) + (c : ℝ)) / (q : ℝ) * ((q : ℝ) ^ (j + 1)) := by
    rw [pow_succ]
    field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- **The price of a draw of t positions covers g ^ t of the n ^ t lists**, for g at most n - e - 1,
where n - e - 1 is at most what the agreement encloses, times n. -/
theorem loc_covers {r : PlanRound} {agree : Bound} {a : ℝ} {n e g : ℕ} (t : ℕ)
    (ha : EnclR agree a) (hn : 0 < n) (h : ((n - e - 1 : ℕ) : ℝ) ≤ a * (n : ℝ))
    (gd : (Bound.pow agree t).bad = false) (hg : g ≤ n - e - 1)
    (he : r.error = (Bound.pow agree t).error) : Covers r (g ^ t) (n ^ t) := by
  apply covers_of_real
  have hp := positions_cover t ha hn h gd
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hg' : (g : ℝ) ≤ ((n - e - 1 : ℕ) : ℝ) := by exact_mod_cast hg
  rw [he]
  push_cast
  calc (g : ℝ) ^ t ≤ ((n - e - 1 : ℕ) : ℝ) ^ t := pow_le_pow_left₀ (Nat.cast_nonneg _) hg' t
    _ = (((n - e - 1 : ℕ) : ℝ) / (n : ℝ)) ^ t * (n : ℝ) ^ t := by
        rw [div_pow]
        field_simp
    _ ≤ (((Bound.pow agree t).error.val : ℚ) : ℝ) * (n : ℝ) ^ t :=
        mul_le_mul_of_nonneg_right hp (by positivity)

/-- The conditions on the sizes of a test on the table under which the two laws speak: a table with
a record, whose distances are given by integers; no one-time test; m as printed. -/
structure Recorded (s : Setting) (x : LinSized) : Prop where
  oneTime : x.lines.oneTime = false
  fromM : x.table.distances.mOnce ≠ 0
  printed : s.printed = true

/-- Of a function in the place of `sharedPlan`: under `Recorded`, with k > 0, a later test's count
not marked bad and at least one drawn element, every plan that it returns pays at the place 0, under
the name LIN point, for (N (v + kLo) + c) |E| ^ (v + kLo - 1) of the |E| ^ (v + kLo) points. -/
def PointPaysOf (plan : Setting → Codes → LinSized → Except String Planned) : Prop :=
  ∀ (s : Setting) (codes : Codes) (x : LinSized) (P : Planned), plan s codes x = .ok P →
    Recorded s x → (tableAnalysis s x.table).later.count.bad = false →
    0 < (wordOf x.table.code).k → 0 < x.table.v + x.shape.kLo →
    ∀ e c : ℕ, (e : ℝ) ≤ (1 - (wordOf x.table.code).agreeAt x.table.distances.mLater true) *
        ((wordOf x.table.code).n : ℝ) →
      (c : ℝ) ≤ (x.table.v : ℝ) * Cb.bchksBound (wordOf x.table.code).n (wordOf x.table.code).k e +
        (Cb.listMax (wordOf x.table.code).n
          ((wordOf x.table.code).n - (wordOf x.table.code).k) e : ℝ) * (x.table.v : ℝ) →
      PaysAt P 0 "LIN point" (x.table.v + x.shape.kLo)
        ((x.lines.requests * (x.table.v + x.shape.kLo) + c) *
          s.cardE ^ (x.table.v + x.shape.kLo - 1))

/-- The sizes that the plans read have the shape's number of low variables. -/
theorem linSizeOf_kLo {codes : Codes} {x : LinSized} {L : LinSize}
    (h : linSizeOf codes x = some L) : L.kLo = x.shape.kLo := by
  unfold linSizeOf at h
  extract_lets at h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  cases h
  rfl

/-- The description of LIN point with a record, in a test that is no one-time test. -/
def pointSpec (s : Setting) (T : TableSize) (N d : ℕ) : RoundSpec :=
  .said "LIN point" .closeness
    (Bound.ofNat N * fieldError s d + tableFoldError s T (tableAnalysis s T).later)
    { drawE := d, rests := (tableAnalysis s T).later.source, priced := .callersWord } 0 0 0

/-- The description of LOC with a record, in a test that is no one-time test. -/
def locSpec (s : Setting) (T : TableSize) (t : ℕ) : RoundSpec :=
  .said "LOC" .query (Bound.pow (tableAnalysis s T).later.agree t)
    { poss := t, logN := T.code.logN, priced := .callersWord } 0 0 0

/-- What a shared plan has at the places 0 and 3, under `Recorded`. -/
theorem shared_front {s : Setting} {codes : Codes} {x : LinSized} {P : Planned}
    (h : sharedPlan s codes x = .ok P) (hx : Recorded s x) :
    ∃ l : List RoundSpec, PlanIs P s .shared l ∧
      l[0]? = some (pointSpec s x.table x.lines.requests (x.table.v + x.shape.kLo)) ∧
      l[3]? = some (locSpec s x.table x.shape.fold.columns) := by
  obtain ⟨L, hL, hc, hP⟩ := sharedPlan_is h
  simp only [hx.oneTime, Bool.false_eq_true, ↓reduceIte] at hc hP
  obtain ⟨hot, hN, -⟩ := linSizeOf_lines hL
  rw [hx.oneTime] at hot
  have hk := linSizeOf_kLo hL
  refine ⟨_, hP, ?_, ?_⟩
  · simp [linSharedTests, linSharedList, pointSpec, hot, hN, hk]
  · simp [linSharedTests, linSharedList, locSpec, hot, hc]

/-- Under the scope of a batch a round's error is that of the routine's bound. -/
theorem said_error_shared (s : Setting) (name : String) (why : ErrorKind) (error : Bound)
    (d : Draws) (bytes roots answers : ℕ) :
    ((RoundSpec.said name why error d bytes roots answers).round s .shared).error =
      error.error := rfl

/-- **Every plan of a shared chain pays at LIN point.** -/
theorem point_pays : PointPaysOf sharedPlan := by
  intro s codes x P h hx g0 hk hd e c he hc
  obtain ⟨l, hP, h0, -⟩ := shared_front h hx
  have hmem := List.mem_of_getElem? h0
  have hg := hP.good _ hmem
  have hh := hP.holds _ hmem
  have hgood : (Bound.ofNat x.lines.requests * fieldError s (x.table.v + x.shape.kLo) +
      tableFoldError s x.table (tableAnalysis s x.table).later).bad = false := hg.1
  have hreal := lin_point_covers (N := x.lines.requests) (d := x.table.v + x.shape.kLo)
    hx.fromM hx.printed g0 hk he hgood
  have hq : 0 < s.cardE := by
    rcases Nat.eq_zero_or_pos s.cardE with h0' | h0'
    · exfalso
      have hz : (fieldError s (x.table.v + x.shape.kLo)).bad = true := by
        unfold fieldError
        rw [h0']
        exact ratio_zero_bad _
      have : (Bound.ofNat x.lines.requests * fieldError s (x.table.v + x.shape.kLo) +
          tableFoldError s x.table (tableAnalysis s x.table).later).bad = true := by
        show (Bound.add (Bound.mul _ _) _).bad = true
        simp [Bound.add, Bound.mul, Bound.inherit, hz]
      rw [this] at hgood
      cases hgood
    · exact h0'
  have hcov : Covers ((pointSpec s x.table x.lines.requests (x.table.v + x.shape.kLo)).round s
      .shared) ((x.lines.requests * (x.table.v + x.shape.kLo) + c) *
        s.cardE ^ (x.table.v + x.shape.kLo - 1)) (s.cardE ^ (x.table.v + x.shape.kLo)) := by
    have he' : ((pointSpec s x.table x.lines.requests (x.table.v + x.shape.kLo)).round s
        .shared).error = (Bound.ofNat x.lines.requests * fieldError s (x.table.v + x.shape.kLo) +
          tableFoldError s x.table (tableAnalysis s x.table).later).error := by
      unfold pointSpec
      exact said_error_shared _ _ _ _ _ _ _ _
    refine covers_point hq hd ?_ hc
    rw [he']
    push_cast at hreal ⊢
    exact hreal
  refine ⟨(pointSpec s x.table x.lines.requests (x.table.v + x.shape.kLo)).round s .shared, ?_,
    rfl, ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · rw [hP.rounds, List.getElem?_map, h0]
    rfl
  · rw [hP.set]
    exact hg.2.1
  · rw [hP.set]
    exact hcov
  · rw [hP.set]
    exact within_of_covers hh hcov

/-- Of a function in the place of `sharedPlan`: under `Recorded`, with a later test's distance times
the length not marked bad, every plan that it returns has at the place 3 a round of the name LOC
that draws as many positions below 2 ^ logN as the shape has columns, and nothing else; its work is
below the target; and it covers g ^ columns of the n ^ columns lists, within the target, for every g
that is at most n - e - 1 and every e from the upper radius on. -/
def LocPaysOf (plan : Setting → Codes → LinSized → Except String Planned) : Prop :=
  ∀ (s : Setting) (codes : Codes) (x : LinSized) (P : Planned), plan s codes x = .ok P →
    Recorded s x →
    ((tableAnalysis s x.table).later.delta * Bound.ofNat (wordOf x.table.code).n).bad = false →
    ∀ e g : ℕ, upperRadius (tableAnalysis s x.table).later.delta (wordOf x.table.code).n ≤ e →
      g ≤ (wordOf x.table.code).n - e - 1 →
      ∃ r, P.rounds[3]? = some r ∧ r.entry.name = "LOC" ∧
        (r.entry.poss = x.shape.fold.columns ∧ r.entry.logN = x.table.code.logN ∧
          r.entry.drawE = 0 ∧ r.entry.drawNZ = 0 ∧ r.entry.trits = 0) ∧
        r.entry.work < s.target ∧
        Covers r (g ^ x.shape.fold.columns) ((2 ^ x.table.code.logN) ^ x.shape.fold.columns) ∧
        Within s.target r.entry.work (g ^ x.shape.fold.columns)
          ((2 ^ x.table.code.logN) ^ x.shape.fold.columns)

/-- **Every plan of a shared chain pays at LOC.** -/
theorem loc_pays : LocPaysOf sharedPlan := by
  intro s codes x P h hx p0 e g u0 hg
  obtain ⟨l, hP, -, h3⟩ := shared_front h hx
  have hmem := List.mem_of_getElem? h3
  have hgd := hP.good _ hmem
  have hh := hP.holds _ hmem
  obtain ⟨_, a0⟩ := tableAnalysis_fromM (s := s) hx.fromM
  rw [hx.printed] at a0
  have hA0 : EnclR (tableAnalysis s x.table).later.agree
      ((wordOf x.table.code).agreeAt x.table.distances.mLater true) := by
    rw [a0]
    exact enclR_johnson_agree _ _ _
  have hD0 : EnclR (tableAnalysis s x.table).later.delta
      (1 - (wordOf x.table.code).agreeAt x.table.distances.mLater true) := by
    rw [a0]
    exact enclR_johnson_delta _ _ _
  have hn : 0 < (wordOf x.table.code).n := by unfold Word.n; positivity
  have hcov : Covers ((locSpec s x.table x.shape.fold.columns).round s .shared)
      (g ^ x.shape.fold.columns) ((wordOf x.table.code).n ^ x.shape.fold.columns) :=
    loc_covers x.shape.fold.columns hA0 hn
      (agree_of_upperRadius hD0 p0 u0 (agreeAt_nonneg _ _ _)) hgd.1 hg rfl
  refine ⟨_, ?_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, hgd.2.1, hcov, within_of_covers hh hcov⟩
  rw [hP.rounds, List.getElem?_map, h3]
  rfl

end OnBytes.Params.Prices
