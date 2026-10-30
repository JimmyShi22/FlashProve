-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/LinPortB.lean: the three own rounds of the test on a stored table for a batch of at
most N requests: the library's error counts against the rounds "LIN point", "LOC" and "LIN zeta"
that the planner adds, in any scope.

OnBytes/Tie/Pv/LinPort.lean and LinPortAt.lean treat the point's count for one request
(`LdLinP.errPt`) under the scope `.once`. For at most N requests that share the point the library's
count is `LdLinP.errPtB εf N` (Cb/Ld/LdLinB.lean): the term of the point's own degree stands N
times. The planner's price has that term `x.instances` times (`linPoint`, LinPort.lean), so it
serves every N up to `x.instances`. The counts of the locations and of the point zeta do not grow
with N (`LdLinP.errCoreB`); the laws on them are turned to a scope c. A round "covers a of b" if
a / b is at most the error that a plan holds of the round (`Covered`, OnBytes/Tie/Pv/PortKit.lean).
In the place of "the price is not marked bad" stands what `close` has tested of the round
(`RoundSpec.Good`, which asks two clauses on the round's work more). One definition, and statements
with their proofs. For proofs only; no program imports this file.

Main names (q := `s.cardE`, v := `T.v`, k := `x.kLo`):
  `pt_coveredB`: "LIN point", with a closeness term, covers
    εf * q ^ k + N * ((v + k) * q ^ (v + k - 1)) of q ^ (v + k) for N at most `x.instances`, if εf
    is at most (v * B + L * v) * q ^ (v - 1), for a whole number B at most what the count of the
    table's distance encloses and L at most its list size.
  `pt_coveredB_at`: the same at εf := `ptCount` (LinPortAt.lean), for a table whose distances are
    given by integers, with m as printed, a count that is not marked bad and a code of dimension
    above 0, and a radius e ≤ (1 - a) * n, for the agreement a at which the table is read and its
    code's length n.
  `linPointTest`, `pt_coveredB_of_test`: these premises, but for what `close` has tested, from a yes
    of a test in the planner's own arithmetic.
  `loc_coveredB`: "LOC" covers (n - e - 1) ^ t of n ^ t, t := `linColumns s c T x`, if 0 < n and
    n - e - 1 is at most what the agreement encloses, times n. `loc_coveredB_at`: so at a table that
    is read near, whose distances are given by integers, with m as printed, where the distance times
    the length is not marked bad, for n its code's length and e from the planner's `upperRadius` on.
  `fits_coveredB`: a round that fits is covered. `zeta_coveredB`: "LIN zeta" covers l * q ^ (l - 1)
    of q ^ l, l := `x.rowsLog`.
  `pt_tiedB`, `pt_tiedB_at`, `loc_tiedB`, `loc_tiedB_at`, `zeta_tiedB`: so of the block's
    `errPtB εf N`, `errLoc` and `errZeta`. `pt_numB`, `errPtB_one`: the count times q; at N = 1 it
    is `errPt`.

Limits: those of LinPort.lean and LinPortAt.lean, but for the scope and the number of requests.
Inequalities. `LinSize.instances`, how many requests share the point, is another number than
`Setting.instances`; in a request's scope with several `Setting.instances` a plan holds the price
times their number, and these laws hold one count against it. The clause on εf is a premise, and it
bounds εf from above; that the library's block is knowledge sound at that εf (`LdLinP.FoldErr`) is
not shown. One radius serves the point and the locations only if it is at least `upperRadius` and at
most (1 - a) * n; no radius is evaluated here. That the N of a given batch is at most `x.instances`,
and that the radius is the block's, is the caller's to show. The point's price without a closeness
term, and the two sendings between the three rounds, are not treated. Nothing on soundness.

-/
import OnBytes.Tie.Pv.LinPortAt
import OnBytes.Tie.Pv.Switch.SendLocPrices
import Cb.Ld.LdLinB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lin
open OnBytes OnBytes.Params Iop Cb

/-- The point's count for N requests, times q. -/
theorem pt_numB {εf v k B L q N : ℕ} (h : εf ≤ (v * B + L * v) * q ^ (v - 1)) :
    (εf * q ^ k + N * ((v + k) * q ^ (v + k - 1))) * q ≤
      (v * B + L * v + N * (v + k)) * q ^ (v + k) := by
  have h1 : εf * q ^ k * q ≤ (v * B + L * v) * q ^ (v + k) := by
    calc εf * q ^ k * q ≤ (v * B + L * v) * q ^ (v - 1) * q ^ k * q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
      _ = (B + L) * (v * q ^ (v - 1) * q) * q ^ k := by ring
      _ = (B + L) * (v * q ^ v) * q ^ k := by rw [pred_pow]
      _ = (v * B + L * v) * q ^ (v + k) := by
          rw [pow_add]
          ring
  calc (εf * q ^ k + N * ((v + k) * q ^ (v + k - 1))) * q
      = εf * q ^ k * q + N * ((v + k) * q ^ (v + k - 1) * q) := by ring
    _ = εf * q ^ k * q + N * ((v + k) * q ^ (v + k)) := by rw [pred_pow]
    _ ≤ (v * B + L * v) * q ^ (v + k) + N * ((v + k) * q ^ (v + k)) := Nat.add_le_add_right h1 _
    _ = (v * B + L * v + N * (v + k)) * q ^ (v + k) := by ring

/-- **"LIN point", with a closeness term, for at most N requests, in any scope.** -/
theorem pt_coveredB {s : Setting} {T : TableSize} {x : LinSize} (c : Scope) {cnt : ℝ} {B L εf N : ℕ} (hx : EnclR (linProx s T x).count cnt)
    (hB : (B : ℝ) ≤ cnt) (hL : L ≤ (linProx s T x).list) (hN : N ≤ x.instances)
    (hq : 0 < s.cardE) (hε : εf ≤ (T.v * B + L * T.v) * s.cardE ^ (T.v - 1))
    (hg : (linPoint s T x).Good s c) :
    Covered s c
      (εf * s.cardE ^ x.kLo + N * ((T.v + x.kLo) * s.cardE ^ (T.v + x.kLo - 1)),
        s.cardE ^ (T.v + x.kLo)) (linPoint s T x) := by
  unfold Covered
  unfold linPoint at hg ⊢
  simp only [↓reduceIte] at hg ⊢
  obtain ⟨w, ew, lw⟩ := tableFold_covers s T (linProx s T x) hx hB
    (le_trans (Nat.cast_nonneg B) hB) hL
  refine OnBytes.Tie.Pv.Switch.said_covers (Bound.enclR_add (Bound.enclR_mul
    (Bound.enclR_ofNat x.instances) (enclR_fieldError s (T.v + x.kLo))) ew)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_ hg
  have hQ : (0 : ℝ) < (s.cardE : ℝ) := by exact_mod_cast hq
  have hQm : (0 : ℝ) < ((s.cardE ^ (T.v + x.kLo) : ℕ) : ℝ) := by exact_mod_cast pow_pos hq _
  have h1 : ((εf * s.cardE ^ x.kLo + N * ((T.v + x.kLo) * s.cardE ^ (T.v + x.kLo - 1)) : ℕ) : ℝ) /
      ((s.cardE ^ (T.v + x.kLo) : ℕ) : ℝ) ≤
      ((T.v * B + L * T.v + N * (T.v + x.kLo) : ℕ) : ℝ) / (s.cardE : ℝ) := by
    rw [div_le_iff₀ hQm, div_mul_eq_mul_div, le_div_iff₀ hQ]
    exact_mod_cast pt_numB hε
  have h2 : (N : ℝ) * (((T.v + x.kLo : ℕ) : ℝ) / (s.cardE : ℝ)) ≤
      (x.instances : ℝ) * (((T.v + x.kLo : ℕ) : ℝ) / (s.cardE : ℝ)) := by
    have hN' : (N : ℝ) ≤ (x.instances : ℝ) := by exact_mod_cast hN
    exact mul_le_mul_of_nonneg_right hN' (by positivity)
  refine h1.trans ?_
  have h3 : ((T.v * B + L * T.v + N * (T.v + x.kLo) : ℕ) : ℝ) / (s.cardE : ℝ) =
      ((T.v : ℝ) * (B : ℝ) + (L : ℝ) * (T.v : ℝ)) / (s.cardE : ℝ) +
        (N : ℝ) * (((T.v + x.kLo : ℕ) : ℝ) / (s.cardE : ℝ)) := by
    push_cast
    ring
  rw [h3]
  linarith

section
variable {s : Setting} {T : TableSize} {x : LinSize} {e N : ℕ}

/-- **"LIN point" for at most N requests, at the library's numbers.** -/
theorem pt_coveredB_at (c : Scope) (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true) (gc : (linProx s T x).count.bad = false)
    (hk : 0 < (wordOf T.code).k)
    (he : (e : ℝ) ≤ (1 - (wordOf T.code).agreeAt (linM T x) true) * ((wordOf T.code).n : ℝ))
    (hN : N ≤ x.instances) (hq : 0 < s.cardE) (hg : (linPoint s T x).Good s c) :
    Covered s c
      (ptCount T e s.cardE * s.cardE ^ x.kLo +
          N * ((T.v + x.kLo) * s.cardE ^ (T.v + x.kLo - 1)),
        s.cardE ^ (T.v + x.kLo)) (linPoint s T x) := by
  have ej := linProx_johnson (s := s) (T := T) x hM hp
  have gc' : (johnson (wordOf T.code) (linM T x) true).count.bad = false := ej ▸ gc
  have hx : EnclR (linProx s T x).count
      (countAt (wordOf T.code).n (wordOf T.code).rho
        (1 - (wordOf T.code).agreeAt (linM T x) true) (linM T x)) := by
    rw [ej]
    exact enclR_johnson_count _ _ _
  have hB : ((⌊Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e⌋₊ : ℕ) : ℝ) ≤
      countAt (wordOf T.code).n (wordOf T.code).rho
        (1 - (wordOf T.code).agreeAt (linM T x) true) (linM T x) :=
    (Nat.floor_le (bchksBound_nonneg _ _ _)).trans
      (bchksBound_le_countAt (johnson_count_good gc').1 hk le_rfl he)
  have hL : Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e ≤
      (linProx s T x).list := by
    rw [ej]
    exact listMax_le_list gc' hk he
  exact pt_coveredB c hx hB hL hN hq le_rfl hg

/-- A test, by the planner's own arithmetic, from which the premises of `pt_coveredB_at` follow, but
for what `close` has tested of the round. The radius is held against the lower end of the table's
distance times the length, rounded down. -/
def linPointTest (s : Setting) (T : TableSize) (x : LinSize) (e N : ℕ) : Bool :=
  decide (T.distances.mOnce ≠ 0) && s.printed && !(linProx s T x).count.bad &&
    decide (0 < (wordOf T.code).k) &&
    !((linProx s T x).delta * Bound.ofNat (wordOf T.code).n).bad &&
    decide (e ≤ lowerRadius (linProx s T x).delta (wordOf T.code).n) &&
    decide (N ≤ x.instances) && decide (0 < s.cardE)

/-- **A yes of that test gives the law's conclusion**, in every scope in which `close` has tested
the round. -/
theorem pt_coveredB_of_test (c : Scope) (h : linPointTest s T x e N = true)
    (hg : (linPoint s T x).Good s c) :
    Covered s c
      (ptCount T e s.cardE * s.cardE ^ x.kLo +
          N * ((T.v + x.kLo) * s.cardE ^ (T.v + x.kLo - 1)),
        s.cardE ^ (T.v + x.kLo)) (linPoint s T x) := by
  unfold linPointTest at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := h
  have ej := linProx_johnson (s := s) (T := T) x a1 a2
  have hd : EnclR (linProx s T x).delta (1 - (wordOf T.code).agreeAt (linM T x) true) := by
    rw [ej]
    exact enclR_johnson_delta _ _ _
  have hr := lowerRadius_le hd a5
  have he : (e : ℝ) ≤ (lowerRadius (linProx s T x).delta (wordOf T.code).n : ℝ) := by
    exact_mod_cast a6
  exact pt_coveredB_at c a1 a2 a3 a4 (he.trans hr) a7 a8 hg

/-! ### the locations and the point zeta, in any scope -/

/-- "LOC", in any scope. -/
theorem loc_coveredB (c : Scope) {a : ℝ} {n : ℕ} (ha : EnclR (linAgree s T x) a) (hn : 0 < n)
    (h : ((n - e - 1 : ℕ) : ℝ) ≤ a * (n : ℝ)) (hg : (linLoc s c T x).Good s c) :
    Covered s c ((n - e - 1) ^ linColumns s c T x, n ^ linColumns s c T x) (linLoc s c T x) := by
  unfold Covered
  unfold linLoc at hg ⊢
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine OnBytes.Tie.Pv.Switch.said_covers (Bound.enclR_pow ha (linColumns s c T x))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_ hg
  show (((n - e - 1) ^ linColumns s c T x : ℕ) : ℝ) / ((n ^ linColumns s c T x : ℕ) : ℝ) ≤
    a ^ linColumns s c T x
  rw [Nat.cast_pow, Nat.cast_pow, ← div_pow]
  exact pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hn').mpr h) _

/-- "LOC" at a table that is read near, from the upper radius on, in any scope. -/
theorem loc_coveredB_at (c : Scope) (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true)
    (p : ((linProx s T x).delta * Bound.ofNat (wordOf T.code).n).bad = false)
    (u : upperRadius (linProx s T x).delta (wordOf T.code).n ≤ e)
    (hg : (linLoc s c T x).Good s c) :
    Covered s c
      (((wordOf T.code).n - e - 1) ^ linColumns s c T x,
        (wordOf T.code).n ^ linColumns s c T x) (linLoc s c T x) := by
  have ej := linProx_johnson (s := s) (T := T) x hM hp
  have ha : EnclR (linAgree s T x) ((wordOf T.code).agreeAt (linM T x) true) := by
    unfold linAgree
    rw [ej]
    exact enclR_johnson_agree _ _ _
  have hd : EnclR (linProx s T x).delta (1 - (wordOf T.code).agreeAt (linM T x) true) := by
    rw [ej]
    exact enclR_johnson_delta _ _ _
  have hpos : 0 < (wordOf T.code).n := by
    unfold Word.n
    positivity
  exact loc_coveredB c ha hpos (agree_of_upperRadius hd p u (agreeAt_nonneg _ _ _)) hg

/-- A round that fits is covered, in any scope. -/
theorem fits_coveredB (s : Setting) (c : Scope) (q : ℕ) (cn : ℕ × ℕ) (n : String) (w : ErrorKind)
    (er : Bound) (d : Draws) (b r a : ℕ) (h : Fits q cn (.said n w er d b r a)) (hn : 0 < cn.2)
    (hg : (RoundSpec.said n w er d b r a).Good s c) :
    Covered s c cn (.said n w er d b r a) := by
  obtain ⟨_, a', b', hb, rfl, hab⟩ := h
  unfold Covered
  refine OnBytes.Tie.Pv.Switch.said_covers (Bound.enclR_ratio a' b')
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (le_of_eq ?_) hg
  have hn' : (cn.2 : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hb' : (b' : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [div_eq_div_iff hn' hb']
  exact_mod_cast hab

/-- "LIN zeta", in any scope. -/
theorem zeta_coveredB (c : Scope) (hq : 0 < s.cardE) (hg : (linZeta s x).Good s c) :
    Covered s c (x.rowsLog * s.cardE ^ (x.rowsLog - 1), s.cardE ^ x.rowsLog) (linZeta s x) :=
  fits_coveredB s c s.cardE _ _ _ _ _ _ _ _ (zeta_fits s x hq) (pow_pos hq _) hg

end

section Blocks
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y) {s : Setting} {T : TableSize} {x : LinSize}

omit [Field E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- At one request the count is `errPt`. -/
theorem errPtB_one (εf : ℕ) : P.errPtB εf 1 = P.errPt εf := by
  unfold LdLinP.errPtB LdLinP.errPt
  rw [Nat.one_mul]

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The block's shared point for at most N requests is covered by "LIN point". -/
theorem pt_tiedB (c : Scope) {cnt : ℝ} {B L εf N : ℕ}
    (hq : Fintype.card E = s.cardE) (hv : P.D.X.v = T.v) (hk : P.D.klo = x.kLo)
    (hx : EnclR (linProx s T x).count cnt) (hB : (B : ℝ) ≤ cnt) (hL : L ≤ (linProx s T x).list)
    (hN : N ≤ x.instances) (hε : εf ≤ (T.v * B + L * T.v) * s.cardE ^ (T.v - 1))
    (hg : (linPoint s T x).Good s c) :
    Covered s c (P.errPtB εf N, Fintype.card P.D.Pt) (linPoint s T x) := by
  have h0 : 0 < s.cardE := hq ▸ Fintype.card_pos
  have hc : Fintype.card P.D.Pt = s.cardE ^ (T.v + x.kLo) := by
    show Fintype.card ((Fin P.D.X.v → E) × (Fin P.D.klo → E)) = _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      hq, hv, hk, pow_add]
  unfold LdLinP.errPtB
  rw [hc, hq, hv, hk]
  exact pt_coveredB c hx hB hL hN h0 hε hg

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The block's shared point for at most N requests, at εf := `ptCount`. -/
theorem pt_tiedB_at (c : Scope) {e N : ℕ}
    (hM : T.distances.mOnce ≠ 0) (hp : s.printed = true)
    (gc : (linProx s T x).count.bad = false) (hk : 0 < (wordOf T.code).k)
    (he : (e : ℝ) ≤ (1 - (wordOf T.code).agreeAt (linM T x) true) * ((wordOf T.code).n : ℝ))
    (hN : N ≤ x.instances) (hq : Fintype.card E = s.cardE) (hv : P.D.X.v = T.v)
    (hkl : P.D.klo = x.kLo) (hg : (linPoint s T x).Good s c) :
    Covered s c (P.errPtB (ptCount T e s.cardE) N, Fintype.card P.D.Pt) (linPoint s T x) := by
  have h0 : 0 < s.cardE := hq ▸ Fintype.card_pos
  have hc : Fintype.card P.D.Pt = s.cardE ^ (T.v + x.kLo) := by
    show Fintype.card ((Fin P.D.X.v → E) × (Fin P.D.klo → E)) = _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      hq, hv, hkl, pow_add]
  unfold LdLinP.errPtB
  rw [hc, hq, hv, hkl]
  exact pt_coveredB_at c hM hp gc hk he hN h0 hg

omit [Field E] [Fintype E] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The block's locations are covered by "LOC", in any scope. -/
theorem loc_tiedB (c : Scope) {a : ℝ} (ht : P.t = linColumns s c T x)
    (ha : EnclR (linAgree s T x) a)
    (h : ((Fintype.card ι - P.e' - 1 : ℕ) : ℝ) ≤ a * (Fintype.card ι : ℝ))
    (hg : (linLoc s c T x).Good s c) :
    Covered s c (P.errLoc, Fintype.card (Fin P.t → ι)) (linLoc s c T x) := by
  unfold LdLinP.errLoc
  rw [Fintype.card_fun, Fintype.card_fin, ht]
  exact loc_coveredB c ha Fintype.card_pos h hg

omit [Field E] [Fintype E] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The block's locations, at a table that is read near, in any scope. -/
theorem loc_tiedB_at (c : Scope) (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true) (hι : Fintype.card ι = (wordOf T.code).n)
    (ht : P.t = linColumns s c T x)
    (p : ((linProx s T x).delta * Bound.ofNat (wordOf T.code).n).bad = false)
    (u : upperRadius (linProx s T x).delta (wordOf T.code).n ≤ P.e')
    (hg : (linLoc s c T x).Good s c) :
    Covered s c (P.errLoc, Fintype.card (Fin P.t → ι)) (linLoc s c T x) := by
  unfold LdLinP.errLoc
  rw [Fintype.card_fun, Fintype.card_fin, ht, hι]
  exact loc_coveredB_at c hM hp p u hg

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The block's last round is covered by "LIN zeta", in any scope. -/
theorem zeta_tiedB (c : Scope) (hq : Fintype.card E = s.cardE) (hl : P.D.l = x.rowsLog)
    (hg : (linZeta s x).Good s c) :
    Covered s c (P.errZeta, Fintype.card (Fin P.D.l → E)) (linZeta s x) := by
  have h0 : 0 < s.cardE := hq ▸ Fintype.card_pos
  unfold LdLinP.errZeta
  rw [Fintype.card_fun, Fintype.card_fin, hq, hl]
  exact zeta_coveredB c h0 hg

end Blocks

end Cb.Pv.Lin

#print axioms Cb.Pv.Lin.pt_numB
#print axioms Cb.Pv.Lin.pt_coveredB
#print axioms Cb.Pv.Lin.pt_coveredB_at
#print axioms Cb.Pv.Lin.pt_coveredB_of_test
#print axioms Cb.Pv.Lin.loc_coveredB
#print axioms Cb.Pv.Lin.loc_coveredB_at
#print axioms Cb.Pv.Lin.fits_coveredB
#print axioms Cb.Pv.Lin.zeta_coveredB
#print axioms Cb.Pv.Lin.errPtB_one
#print axioms Cb.Pv.Lin.pt_tiedB
#print axioms Cb.Pv.Lin.pt_tiedB_at
#print axioms Cb.Pv.Lin.loc_tiedB
#print axioms Cb.Pv.Lin.loc_tiedB_at
#print axioms Cb.Pv.Lin.zeta_tiedB
