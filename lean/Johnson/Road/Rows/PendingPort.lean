-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/PendingPort.lean: the pending row as wsPending makes it, against the merge's
function at its point.

The merge leaves one equation to the test on the committed matrix, the pending row. wsPending
(OnBytes/Model/Pending.lean) folds the row weights Gam from row 0 to the end of the stretch of rows
that the claims' units span, cuts that stretch out, and has memberWeightsOnRows
(OnBytes/Iop/Lin.lean) spell the stretch as a list of vectors of product form.
Johnson/Road/FormsKeysMerge.lean shows that the merge's function at its point is the sum over all
rows below the stretch's end of Gam's member times the row read at the point (pending_gamma). This
file goes on to the record that wsPending returns.

Main definitions.
 - StretchMeans: a named hypothesis on stretchInTheCube, through which memberWeightsOnRows answers.
   The entries of the vectors that it returns add up, at each row of the cube, to the value written
   for that row, and to 0 outside the stretch. Johnson/Road/Rows/StretchLaws.lean proves it;
   Johnson/Road/Rows/TestPendingPort.lean evaluates it for all stretches in
   cubes of up to 32 rows.
 - pendWeight: the sum of the entries of a list of vectors at a row.
Main theorems: span_fold (the stretch holds every claim's unit), below_zero (Gam weighs no row below
the stretch), cut_sum (the sum over all rows is the sum over the stretch), stretch_sum (under
StretchMeans the sum over the cube is the sum over the stretch), pending_port (what wsPending
returns).

What is not claimed. In this file StretchMeans is a hypothesis. How the test on the matrix reads the
record is not looked at. M is any function. The program does not import this file.


-/
import Johnson.Road.FormsKeysMerge
import OnBytes.Model.Pending

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading WsLay WsClaim WsRecClaim WsForkOut WsPending wsEpsT wsRowPart
  wsGammaAdd wsGamma wsSpan wsPending)

/-! ## The stretch -/

/-- One step of wsSpan. -/
def spanStep (lay : WsLay) (r : ℕ × ℕ) (c : WsRecClaim) : Except String (ℕ × ℕ) :=
  match lay.U[c.ui]? with
  | none => throw "internal-gamma-rows"
  | some u => pure (min r.1 u.off, max r.2 (u.off + u.rows))

/-- The fold of wsSpan only widens the stretch, and the stretch holds the unit of each claim. -/
theorem span_fold (lay : WsLay) : ∀ (recs : List WsRecClaim) (r r' : ℕ × ℕ),
    recs.foldlM (spanStep lay) r = .ok r' →
    r'.1 ≤ r.1 ∧ r.2 ≤ r'.2 ∧
      ∀ c ∈ recs, ∀ u, lay.U[c.ui]? = some u → r'.1 ≤ u.off ∧ u.off + u.rows ≤ r'.2
  | [], r, r', h => by
    have e : r = r' := Except.ok.inj h
    subst e
    exact ⟨le_refl _, le_refl _, fun c hc => nomatch hc⟩
  | c :: recs, r, r', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨r1, h1, h2⟩ := ok_of_bind h
    cases hu : lay.U[c.ui]? with
    | none =>
      unfold spanStep at h1
      rw [hu] at h1
      cases h1
    | some u =>
      unfold spanStep at h1
      rw [hu] at h1
      have e : (min r.1 u.off, max r.2 (u.off + u.rows)) = r1 := Except.ok.inj h1
      subst e
      obtain ⟨a, b, d⟩ := span_fold lay recs _ r' h2
      refine ⟨le_trans a (min_le_left _ _), le_trans (le_max_left _ _) b, fun c' hc' u' hu' => ?_⟩
      rcases List.mem_cons.mp hc' with e' | h'
      · subst e'
        rw [hu] at hu'
        cases hu'
        exact ⟨le_trans a (min_le_right _ _), le_trans (le_max_right _ _) b⟩
      · exact d c' h' u' hu'

/-- What is left of a claim names the claim's unit. -/
theorem rowPart_ui (lay : WsLay) (c : WsClaim) (ka : E) : (wsRowPart lay c ka).ui = c.ui := by
  unfold wsRowPart
  split <;> rfl

variable {K : Type} [Field K] {ρ : Reading K}

/-! ## The folded weights below the stretch -/

/-- Gam weighs no row below the first row of the claims' units: for every R the sum over the rows
below n of Gam's member times R, counted below first alone, is 0. -/
theorem below_zero (hρ : Numerals ρ) (lay : WsLay) (rm : Array E) (cr : List (WsClaim × E))
    {n first : ℕ} {Gam : Array E}
    (h : (cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 rm))).foldlM
      (fun G c => wsGammaAdd G lay c oneE) (Array.replicate n zeroE) = .ok Gam)
    (hf : ∀ y ∈ cr, ∀ u, lay.U[y.1.ui]? = some u → first ≤ u.off) (R : ℕ → K) :
    ∑ y ∈ range n, ρ.val (Gam.getD y zeroE) * (if y < first then R y else 0) = 0 := by
  obtain ⟨-, h2⟩ := gamma_fold hρ lay rm (fun y => if y < first then R y else 0) cr _ Gam h
  rw [Array.size_replicate] at h2
  rw [h2]
  have h0 : ∑ y ∈ range n, ρ.val ((Array.replicate n zeroE).getD y zeroE) *
      (if y < first then R y else 0) = 0 := by
    refine sum_eq_zero fun y hy => ?_
    have e : (Array.replicate n zeroE).getD y zeroE = zeroE := by
      simp [Array.getD, mem_range.mp hy]
    rw [e, ρ.zero, zero_mul]
  rw [h0, zero_add]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  cases hu : lay.U[y.1.ui]? with
  | none => simp
  | some u =>
    have hle := hf y hy u hu
    have hz : ∑ j ∈ range u.rows,
        ρ.val ((wsGamma u (wsRowPart lay y.1 oneE) oneE).getD j zeroE) *
          (if u.off + j < first then R (u.off + j) else 0) = 0 := by
      refine sum_eq_zero fun j _ => ?_
      rw [if_neg (by omega), mul_zero]
    simp only [hz, mul_zero]

/-- The sum over all rows below first + d is the sum over the stretch from first on. -/
theorem cut_sum {first d : ℕ} {Gam : Array E} (hs : Gam.size = first + d) (R : ℕ → K)
    (hz : ∑ y ∈ range (first + d), ρ.val (Gam.getD y zeroE) * (if y < first then R y else 0) = 0) :
    ∑ y ∈ range (first + d), ρ.val (Gam.getD y zeroE) * R y =
      ∑ i ∈ range d, ρ.val ((Gam.extract first (first + d)).getD i zeroE) * R (first + i) := by
  rw [sum_range_add] at hz ⊢
  have h1 : ∑ x ∈ range d, ρ.val (Gam.getD (first + x) zeroE) *
      (if first + x < first then R (first + x) else 0) = 0 :=
    sum_eq_zero fun x _ => by rw [if_neg (by omega), mul_zero]
  have h2 : ∑ x ∈ range first, ρ.val (Gam.getD x zeroE) * (if x < first then R x else 0) =
      ∑ x ∈ range first, ρ.val (Gam.getD x zeroE) * R x :=
    sum_congr rfl fun x hx => by rw [if_pos (mem_range.mp hx)]
  rw [h1, add_zero, h2] at hz
  rw [hz, zero_add]
  refine sum_congr rfl fun i hi => ?_
  rw [getD_extract Gam (a := first) (b := first + d) (j := i) (by omega)
    (by have := mem_range.mp hi; omega) zeroE]

/-! ## The stretch as a list of vectors -/

/-- The sum of the entries of a list of vectors at row j. -/
def pendWeight (ρ : Reading K) (g : List Tensor) (j : ℕ) : K :=
  (g.map fun t => ρ.val (t.entry j)).sum

/-- What stretchInTheCube, through which memberWeightsOnRows answers, is meant to return: vectors
whose entries add up, at each row of the cube, to the value written for that row, and to 0 outside
the stretch. -/
def StretchMeans (ρ : Reading K) : Prop :=
  ∀ (kRow first : ℕ) (values : Array E) (g : List Tensor),
    stretchInTheCube kRow first values = some g → ∀ j, j < 2 ^ kRow →
      pendWeight ρ g j =
        if first ≤ j ∧ j < first + values.size then ρ.val (values.getD (j - first) zeroE) else 0

omit [Field K] in
/-- A sum over N rows under weights that vanish outside a stretch is the sum over the stretch. -/
theorem stretch_sum [Field K] {N first d : ℕ} {w v R : ℕ → K} (hN : first + d ≤ N)
    (hm : ∀ j, j < N → w j = if first ≤ j ∧ j < first + d then v (j - first) else 0) :
    ∑ j ∈ range N, w j * R j = ∑ i ∈ range d, v i * R (first + i) := by
  obtain ⟨r, rfl⟩ : ∃ r, N = first + d + r := ⟨N - (first + d), by omega⟩
  rw [sum_range_add, sum_range_add]
  have A : ∑ x ∈ range first, w x * R x = 0 := sum_eq_zero fun x hx => by
    have hx' := mem_range.mp hx
    rw [hm x (by omega), if_neg (by omega), zero_mul]
  have B : ∑ x ∈ range r, w (first + d + x) * R (first + d + x) = 0 := sum_eq_zero fun x hx => by
    have hx' := mem_range.mp hx
    rw [hm _ (by omega), if_neg (by omega), zero_mul]
  rw [A, B, zero_add, add_zero]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [hm _ (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

/-! ## What wsPending returns -/

omit [Field K] in
/-- The steps of wsPending, if it returns. -/
theorem wsPending_ok {lay : WsLay} {o : WsForkOut} {claims : ℕ} {S : Params.LinShape}
    {w : WsPending} (h : wsPending lay o claims S = .ok w) :
    ∃ (first last : ℕ) (Gam : Array E) (g : List Tensor),
      wsSpan lay o.recs = .ok (first, last) ∧ first < last ∧ last ≤ lay.m0 ∧
      lay.m0 ≤ 2 ^ S.kRow ∧
      o.recs.foldlM (fun G c => wsGammaAdd G lay c oneE) (Array.replicate last zeroE) = .ok Gam ∧
      memberWeightsOnRows S first (Gam.extract first last) = some g ∧
      w = { g := g, psi := o.rm.toList.reverse, beta := o.beta, target := o.fvp } := by
  unfold wsPending at h
  try dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, -, h⟩ := ok_of_bind h
  obtain ⟨_, -, h⟩ := ok_of_bind h
  obtain ⟨⟨first, last⟩, hsp, h⟩ := ok_of_bind h
  try dsimp only at h
  split at h
  · cases h
  rename_i c3
  obtain ⟨_, -, h⟩ := ok_of_bind h
  obtain ⟨Gam, hG, h⟩ := ok_of_bind h
  try dsimp only at h
  split at h
  · cases h
  rename_i g hg
  have c3' : (decide (last ≤ first) || decide (lay.m0 < last) || decide (62 < S.kRow) ||
      decide (2 ^ S.kRow < lay.m0)) = false := by simpa using c3
  have a1 := or_false_split c3'
  have a2 := or_false_split a1.1
  have a3 := or_false_split a2.1
  exact ⟨first, last, Gam, g, hsp, Nat.not_le.mp (of_decide_eq_false a3.1),
    Nat.not_lt.mp (of_decide_eq_false a3.2), Nat.not_lt.mp (of_decide_eq_false a1.2), hG, hg,
    (Except.ok.inj h).symm⟩

/-- What wsPending returns, against the merge's function at its point. cr: the claims with their
coefficients; ho: what the merge leaves of them, as wsForkEnd makes it. -/
theorem pending_port (hρ : Numerals ρ) (St : StretchMeans ρ) (lay : WsLay) (M : Wm K)
    (o : WsForkOut) (claims : ℕ) (S : Params.LinShape) (cr : List (WsClaim × E))
    (ho : o.recs = cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm)))
    {w : WsPending} (h : wsPending lay o claims S = .ok w) :
    w.psi = o.rm.toList.reverse ∧ w.beta = o.beta ∧ w.target = o.fvp ∧
      ∑ j ∈ range (2 ^ S.kRow), pendWeight ρ w.g j * rowAt ρ lay.lk o.rm M j =
        fmAt ρ lay M cr o.rm := by
  obtain ⟨first, last, Gam, g, hsp, hfl, hlm, hm2, hG, hg, rfl⟩ := wsPending_ok h
  refine ⟨rfl, rfl, rfl, ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, last = first + d := ⟨last - first, by omega⟩
  rw [ho] at hG hsp
  have hsz : Gam.size = first + d := by
    rw [(gamma_fold hρ lay o.rm (fun _ => (0 : K)) cr _ Gam hG).1, Array.size_replicate]
  have hsp' : (cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm))).foldlM
      (spanStep lay) (2 ^ 64 - 1, 0) = .ok (first, first + d) := hsp
  have hf : ∀ y ∈ cr, ∀ u, lay.U[y.1.ui]? = some u → first ≤ u.off := by
    intro y hy u hu
    refine ((span_fold lay _ _ _ hsp').2.2 _ (List.mem_map.mpr ⟨y, hy, rfl⟩) u ?_).1
    rw [rowPart_ui]
    exact hu
  have hx : (Gam.extract first (first + d)).size = d := by
    rw [Array.size_extract]
    omega
  rw [pending_gamma hρ lay M o.rm cr hG,
    cut_sum hsz _ (below_zero hρ lay o.rm cr hG hf _)]
  refine stretch_sum (by omega) fun j hj => ?_
  have hg' : stretchInTheCube S.kRow first (Gam.extract first (first + d)) = some g := by
    unfold memberWeightsOnRows at hg
    split at hg
    · exact hg
    · cases hg
  have e := St S.kRow first _ g hg' j hj
  rw [hx] at e
  exact e

end OnBytes.Road.Rows
