-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PanelTerm.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side, the batched sumcheck:
ONE PANEL. What the verifier's function stackEndOf adds for a panel is written out by the library
(dEnd, stackEndOf_rd, Johnson/Road/FormsKeysEnd.lean). Here: at the true end values, what it adds
to the first form and to the first element together is the weight of the panel's place times the
panel's first side (panelTabs, Johnson/Desc/K4/Honest/Stack.lean) under the rows' and the columns'
weights; and the like for the second. Definitions; statements and proofs.

  `sideTerm`        the weight of a panel's place times a side under the rows' and columns'
                    weights.
  `sideTerm_read`, `under_one`, `grid_at`, `sideTerm_grid`, `range_mapM_has`   loops and tables,
                    read.
  `EndsAre`         the numbers that stand for a panel's end values are the true ones.
  `sum_row_col`       a sum over rows and columns of a product of a row's and a column's factor.
  `grid_div_mod`, `grid_place_lt`   a place in a table that is laid row by row.
  `term_tri`, `term_down`, `term_forms`   the arms.
  **`panel_adds`**    all arms.

Not shown here. That the hypotheses hold anywhere: no example is known. THAT THE NUMBERS h1 AND vv
ARE THE TRUE END VALUES (EndsAre) and that a form's value on the honest reads is its value in the
world W (hval) are hypotheses.
No property is claimed.
-/
import Johnson.Road.K4.C.LongExt
import Johnson.Road.K4.C.RowMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk Lay)
open OnBytes.Desc.First.K4.Honest

/-- The weight of a panel's place times a side of the panel under the rows' and the columns'
weights: one member of the sums in LongExt.lean. -/
def sideTerm (rs : Array E) (lam : ℕ) (b : SBlk) (x : Array E) : Cb.Gl.E :=
  Reading.gl.val (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) *
    Reading.gl.val (StackData.under (eqLow rs b.wy b.w) (eqLow rs 0 b.wy) b.ni b.ny
      fun i yv => x.getD (i * b.ny + yv) zeroE)

/-- It, in the library's names for the weights. -/
theorem sideTerm_read (rs : Array E) (lam : ℕ) (b : SBlk) (x : Array E) :
    sideTerm rs lam b x = sbK Reading.gl rs lam b * ∑ i ∈ range b.ni, eiK Reading.gl rs b i *
      ∑ yv ∈ range b.ny, eyK Reading.gl rs b yv *
        Reading.gl.val (x.getD (i * b.ny + yv) zeroE) := by
  unfold sideTerm
  rw [under_read]
  rfl

/-- The loop with one row of weight 1. -/
theorem under_one (EY : Array E) (ny : ℕ) (f : ℕ → ℕ → E) :
    Reading.gl.val (StackData.under #[oneE] EY 1 ny f) =
      ∑ yv ∈ range ny, Reading.gl.val (EY.getD yv zeroE) * Reading.gl.val (f 0 yv) := by
  rw [under_read, sum_range_one]
  show Reading.gl.val oneE * _ = _
  rw [Reading.gl.one, one_mul]

/-- An entry of a table that is laid row by row. -/
theorem grid_at (ni ny : ℕ) (f : ℕ → ℕ → E) {i yv : ℕ} (hi : i < ni) (hy : yv < ny) :
    ((Array.range (ni * ny)).map fun x => f (x / ny) (x % ny)).getD (i * ny + yv) zeroE =
      f i yv := by
  have h0 : 0 < ny := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  have hlt : i * ny + yv < ni * ny := by
    have h1 : (i + 1) * ny ≤ ni * ny := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at h1
    omega
  rw [range_map_getD' _ _ _ hlt, Nat.mul_comm i ny, Nat.mul_add_div h0, Nat.div_eq_of_lt hy,
    Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]

/-- The term of a side that is laid row by row. -/
theorem sideTerm_grid (rs : Array E) (lam : ℕ) (b : SBlk) (f : ℕ → ℕ → E) :
    sideTerm rs lam b ((Array.range (b.ni * b.ny)).map fun x => f (x / b.ny) (x % b.ny)) =
      sbK Reading.gl rs lam b * ∑ i ∈ range b.ni, eiK Reading.gl rs b i *
        ∑ yv ∈ range b.ny, eyK Reading.gl rs b yv * Reading.gl.val (f i yv) := by
  rw [sideTerm_read]
  refine congrArg _ (sum_congr rfl fun i hi => congrArg _ (sum_congr rfl fun yv hy => ?_))
  rw [grid_at b.ni b.ny f (mem_range.mp hi) (mem_range.mp hy)]

/-- A member of what mapM over the first n numbers returns. -/
theorem range_mapM_has {g : ℕ → Option E} {n : ℕ} {a : Array E}
    (h : (Array.range n).mapM g = some a) {x : ℕ} (hx : x < n) :
    ∃ z, g x = some z ∧ a.getD x zeroE = z := by
  obtain ⟨z, hz, hg⟩ := amapM_get h (i := x) (x := x) (by simp [hx])
  exact ⟨z, hz, by rw [Array.getD_eq_getD_getElem?, hg, Option.getD_some]⟩

/-- **The numbers that stand for a panel's end values are the true ones.** h1 k: never-sent vector
number k; vv n: weight claim number n. This defines a hypothesis; the definition claims nothing. -/
structure EndsAre (S : Sides) (F : Array (Array E)) (hZ hR : Tab) (y : Lay) (rs : Array E)
    (h1 vv : ℕ → Cb.Gl.E) (b : SBlk) : Prop where
  /-- with the selector: as many rows as experts -/
  ne : b.tri = true → b.ni = y.h.NE
  /-- with the selector: the one weight claim -/
  tv : b.tri = true → ∀ v0, b.v0 = some v0 → vv v0 = ∑ i ∈ range b.ni, eiK Reading.gl rs b i *
    ∑ yv ∈ range b.ny, eyK Reading.gl rs b yv *
      Reading.gl.val (at2 (F.getD v0 #[]) (S.kkOf v0) i yv)
  /-- without it: one weight claim for each row -/
  pv : b.tri = false → ∀ v0, b.v0 = some v0 → ∀ i, i < b.ni → vv (v0 + i) =
    ∑ yv ∈ range b.ny, eyK Reading.gl rs b yv *
      Reading.gl.val (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
  /-- with the selector: the routed experts' never-sent vector -/
  th : b.tri = true → ∀ k, b.virt = some k → h1 k = ∑ yv ∈ range b.ny, eyK Reading.gl rs b yv *
    Reading.gl.val (hR.getD (S.routedAt (k - 1) yv) zeroE)
  /-- without it: the down product's never-sent vector -/
  dh : b.tri = false → ∀ k, b.virt = some k → h1 k = ∑ i ∈ range b.ni, eiK Reading.gl rs b i *
    ∑ yv ∈ range b.ny, eyK Reading.gl rs b yv *
      Reading.gl.val (hZ.getD (i * S.v.y.Pf + yv) zeroE)

/-- A sum over rows and columns of a constant, a row's factor and a column's factor. -/
theorem sum_row_col (n m : ℕ) (ei sl ey col : ℕ → Cb.Gl.E) (C : Cb.Gl.E) :
    ∑ i ∈ range n, ei i * ∑ yv ∈ range m, ey yv * (C * sl i * col yv) =
      C * (∑ i ∈ range n, sl i * ei i) * ∑ yv ∈ range m, ey yv * col yv := by
  have inner : ∀ i, ∑ yv ∈ range m, ey yv * (C * sl i * col yv) =
      C * sl i * ∑ yv ∈ range m, ey yv * col yv := by
    intro i
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  simp only [inner]
  generalize (∑ yv ∈ range m, ey yv * col yv) = T
  rw [mul_sum, sum_mul]
  exact sum_congr rfl fun _ _ => by ring

variable {S : Sides} {val : Aff → Option E} {om : Array E} {F : Array (Array E)} {hZ hR : Tab}
  {b : SBlk} {a c : Array E} {W : World Cb.Gl.E} {y : Lay} {rs : Array E} {lam : ℕ}
  {h1 vv : ℕ → Cb.Gl.E}

/-- **A panel with the selector.** -/
theorem term_tri (ht : b.tri = true) (h : panelTabs S val om F hZ hR b = some (a, c))
    (hval : ∀ f x, val f = some x → Reading.gl.val x = f.value Reading.gl W)
    (T : EndsAre S F hZ hR y rs h1 vv b) :
    (dEnd Reading.gl W y rs lam om h1 vv b).1 + (dEnd Reading.gl W y rs lam om h1 vv b).2.2.1 =
        sideTerm rs lam b a ∧
      (dEnd Reading.gl W y rs lam om h1 vv b).2.1 +
        (dEnd Reading.gl W y rs lam om h1 vv b).2.2.2.1 = sideTerm rs lam b c := by
  unfold panelTabs at h
  dsimp only at h
  rw [if_pos ht] at h
  obtain ⟨v0, hv0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cols, hcols, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  rw [sideTerm_grid rs lam b fun e yv => at2 (F.getD v0 #[]) (S.kkOf v0) e yv,
    sideTerm_grid rs lam b fun e yv =>
      mulE (mulE (mulE (mulE (om.getD b.claim zeroE) b.ec) (b.wt.getD 0 zeroE))
        (b.sl.getD e zeroE)) (cols.getD yv zeroE)]
  have hA : ∑ i ∈ range b.ni, eiK Reading.gl rs b i * ∑ yv ∈ range b.ny, eyK Reading.gl rs b yv *
      Reading.gl.val (mulE (mulE (mulE (mulE (om.getD b.claim zeroE) b.ec) (b.wt.getD 0 zeroE))
        (b.sl.getD i zeroE)) (cols.getD yv zeroE)) =
      omK Reading.gl om b * Reading.gl.val b.ec * wtK Reading.gl b 0 *
        (∑ e ∈ range y.h.NE, Reading.gl.val (b.sl.getD e zeroE) * eiK Reading.gl rs b e) *
        ∑ yv ∈ range b.ny, eyK Reading.gl rs b yv * Reading.gl.val (cols.getD yv zeroE) := by
    rw [← T.ne ht, ← sum_row_col]
    refine sum_congr rfl fun i _ => congrArg _ (sum_congr rfl fun yv _ => ?_)
    rw [Reading.gl.mul, Reading.gl.mul, Reading.gl.mul, Reading.gl.mul]
    rfl
  rw [hA, ← T.tv ht v0 hv0]
  unfold dEnd
  cases hk : b.virt with
  | some k =>
    rw [ht, hv0]
    have hc : ∀ yv, yv < b.ny →
        cols.getD yv zeroE = hR.getD (S.routedAt (k - 1) yv) zeroE := by
      intro yv hy
      obtain ⟨z, hz, e⟩ := range_mapM_has hcols hy
      rw [hk] at hz
      rw [e]
      exact (Option.some.inj hz).symm
    have hs : ∑ yv ∈ range b.ny, eyK Reading.gl rs b yv * Reading.gl.val (cols.getD yv zeroE) =
        h1 k := by
      rw [T.th ht k hk]
      exact sum_congr rfl fun yv hy => by rw [hc yv (mem_range.mp hy)]
    rw [hs]
    refine ⟨?_, ?_⟩
    · show 0 + c1K Reading.gl y rs lam om b * h1 k = _
      unfold c1K
      ring
    · show 0 + sbK Reading.gl rs lam b * vv v0 = _
      ring
  | none =>
    rw [ht, hv0]
    have hc : ∀ yv, yv < b.ny →
        Reading.gl.val (cols.getD yv zeroE) = (b.xx.getD yv {}).value Reading.gl W := by
      intro yv hy
      obtain ⟨z, hz, e⟩ := range_mapM_has hcols hy
      rw [hk] at hz
      rw [e]
      exact hval _ _ hz
    refine ⟨?_, ?_⟩
    · show (∑ k2 ∈ range b.ny, c1K Reading.gl y rs lam om b * eyK Reading.gl rs b k2 *
        (b.xx.getD k2 {}).value Reading.gl W) + 0 = _
      rw [add_zero, mul_sum, mul_sum]
      refine sum_congr rfl fun yv hy => ?_
      rw [hc yv (mem_range.mp hy)]
      unfold c1K
      ring
    · show 0 + sbK Reading.gl rs lam b * vv v0 = _
      ring

/-- The row and the column of a place in a table that is laid row by row. -/
theorem grid_div_mod {ny i yv : ℕ} (hy : yv < ny) :
    (i * ny + yv) / ny = i ∧ (i * ny + yv) % ny = yv := by
  have h0 : 0 < ny := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  rw [Nat.mul_comm i ny, Nat.mul_add_div h0, Nat.div_eq_of_lt hy, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hy]
  exact ⟨rfl, rfl⟩

/-- A place of a table of ni rows lies in the table. -/
theorem grid_place_lt {ni ny i yv : ℕ} (hi : i < ni) (hy : yv < ny) : i * ny + yv < ni * ny := by
  have h1 : (i + 1) * ny ≤ ni * ny := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at h1
  omega

/-- **The panel of the down product.** -/
theorem term_down (ht : b.tri = false) {k : ℕ} (hk : b.virt = some k)
    (h : panelTabs S val om F hZ hR b = some (a, c)) (T : EndsAre S F hZ hR y rs h1 vv b) :
    (dEnd Reading.gl W y rs lam om h1 vv b).1 + (dEnd Reading.gl W y rs lam om h1 vv b).2.2.1 =
        sideTerm rs lam b a ∧
      (dEnd Reading.gl W y rs lam om h1 vv b).2.1 +
        (dEnd Reading.gl W y rs lam om h1 vv b).2.2.2.1 = sideTerm rs lam b c := by
  unfold panelTabs at h
  dsimp only at h
  rw [if_neg (by rw [ht]; exact Bool.false_ne_true), hk] at h
  dsimp only at h
  obtain ⟨v0, hv0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  rw [sideTerm_grid rs lam b fun i yv =>
      mulE (om.getD b.claim zeroE) (hZ.getD (i * S.v.y.Pf + yv) zeroE),
    sideTerm_grid rs lam b fun i yv => mulE (mulE b.ec (b.wt.getD i zeroE))
      (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)]
  unfold dEnd
  rw [ht, hk, hv0]
  refine ⟨?_, ?_⟩
  · show 0 + sbK Reading.gl rs lam b * omK Reading.gl om b * h1 k = _
    rw [T.dh ht k hk, zero_add, mul_assoc]
    refine congrArg _ ?_
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun yv _ => ?_
    rw [Reading.gl.mul]
    unfold omK
    ring
  · show 0 + ∑ i ∈ range b.ni, sbK Reading.gl rs lam b * eiK Reading.gl rs b i *
      Reading.gl.val b.ec * wtK Reading.gl b i * vv (v0 + i) = _
    rw [zero_add, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [T.pv ht v0 hv0 i (mem_range.mp hi), mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun yv _ => ?_
    rw [Reading.gl.mul, Reading.gl.mul]
    unfold wtK
    ring

/-- **A panel without the selector whose first side is given as forms.** -/
theorem term_forms (ht : b.tri = false) (hk : b.virt = none)
    (h : panelTabs S val om F hZ hR b = some (a, c))
    (hval : ∀ f x, val f = some x → Reading.gl.val x = f.value Reading.gl W)
    (T : EndsAre S F hZ hR y rs h1 vv b) :
    (dEnd Reading.gl W y rs lam om h1 vv b).1 + (dEnd Reading.gl W y rs lam om h1 vv b).2.2.1 =
        sideTerm rs lam b a ∧
      (dEnd Reading.gl W y rs lam om h1 vv b).2.1 +
        (dEnd Reading.gl W y rs lam om h1 vv b).2.2.2.1 = sideTerm rs lam b c := by
  unfold panelTabs at h
  dsimp only at h
  rw [if_neg (by rw [ht]; exact Bool.false_ne_true), hk] at h
  dsimp only at h
  obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
  have hAt : ∀ i, i < b.ni → ∀ yv, yv < b.ny →
      Reading.gl.val (a'.getD (i * b.ny + yv) zeroE) = omK Reading.gl om b * Reading.gl.val b.ec *
        wtK Reading.gl b i * sideK Reading.gl W b.A i yv := by
    intro i hi yv hy
    obtain ⟨z, hz, e⟩ := range_mapM_has ha (grid_place_lt hi hy)
    rw [(grid_div_mod (i := i) hy).1, (grid_div_mod (i := i) hy).2] at hz
    obtain ⟨f, hf, hz⟩ := Option.bind_eq_some_iff.mp hz
    obtain ⟨u, hu, hz⟩ := Option.bind_eq_some_iff.mp hz
    obtain rfl := Option.some.inj hz
    rw [e, Reading.gl.mul, Reading.gl.mul, Reading.gl.mul, hval f u hu, hA]
    show _ = _ * ov Reading.gl W (A i yv)
    rw [hf]
    rfl
  have hFirst : ∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK Reading.gl rs lam b *
      omK Reading.gl om b * Reading.gl.val b.ec * wtK Reading.gl b i * eiK Reading.gl rs b i *
      eyK Reading.gl rs b yv * sideK Reading.gl W b.A i yv = sideTerm rs lam b a' := by
    rw [sideTerm_read, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun yv hy => ?_
    rw [hAt i (mem_range.mp hi) yv (mem_range.mp hy)]
    ring
  unfold dEnd
  cases h0 : b.v0 with
  | some v0 =>
    rw [ht, hk]
    have h' : some (a', (Array.range (b.ni * b.ny)).map fun x =>
        at2 (F.getD (v0 + x / b.ny) #[]) (S.kkOf (v0 + x / b.ny)) 0 (x % b.ny)) = some (a, c) := by
      rw [h0] at h
      cases hB : b.B <;> rw [hB] at h <;> exact h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    refine ⟨?_, ?_⟩
    · show (∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK Reading.gl rs lam b *
        omK Reading.gl om b * Reading.gl.val b.ec * wtK Reading.gl b i * eiK Reading.gl rs b i *
        eyK Reading.gl rs b yv * sideK Reading.gl W b.A i yv) + 0 = _
      rw [add_zero, hFirst]
    · show 0 + ∑ i ∈ range b.ni, sbK Reading.gl rs lam b * eiK Reading.gl rs b i * vv (v0 + i) = _
      rw [zero_add, sideTerm_grid rs lam b fun i yv =>
        at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv, mul_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [T.pv ht v0 h0 i (mem_range.mp hi), mul_assoc]
  | none =>
    rw [ht, hk]
    rw [h0] at h
    cases hB : b.B with
    | none =>
      rw [hB] at h
      cases h
    | some B =>
      rw [hB] at h
      obtain ⟨c', hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hBt : ∀ i, i < b.ni → ∀ yv, yv < b.ny →
          Reading.gl.val (c'.getD (i * b.ny + yv) zeroE) = sideK Reading.gl W (some B) i yv := by
        intro i hi yv hy
        obtain ⟨z, hz, e⟩ := range_mapM_has hc (grid_place_lt hi hy)
        rw [(grid_div_mod (i := i) hy).1, (grid_div_mod (i := i) hy).2] at hz
        obtain ⟨f, hf, hz⟩ := Option.bind_eq_some_iff.mp hz
        rw [e, hval f z hz]
        show _ = ov Reading.gl W (B i yv)
        rw [hf]
        rfl
      refine ⟨?_, ?_⟩
      · show (∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK Reading.gl rs lam b *
          omK Reading.gl om b * Reading.gl.val b.ec * wtK Reading.gl b i * eiK Reading.gl rs b i *
          eyK Reading.gl rs b yv * sideK Reading.gl W b.A i yv) + 0 = _
        rw [add_zero, hFirst]
      · show (∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK Reading.gl rs lam b *
          eiK Reading.gl rs b i * eyK Reading.gl rs b yv * sideK Reading.gl W (some B) i yv) + 0 = _
        rw [add_zero, sideTerm_read, mul_sum]
        refine sum_congr rfl fun i hi => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun yv hy => ?_
        rw [hBt i (mem_range.mp hi) yv (mem_range.mp hy)]
        ring

/-- **WHAT stackEndOf ADDS FOR A PANEL, AT THE TRUE END VALUES, IS THE PANEL's TWO TERMS.** The
first and third of the library's five numbers together: the first side's term; the second and
fourth: the second side's. CONDITIONAL: on h, hval and T. -/
theorem panel_adds (h : panelTabs S val om F hZ hR b = some (a, c))
    (hval : ∀ f x, val f = some x → Reading.gl.val x = f.value Reading.gl W)
    (T : EndsAre S F hZ hR y rs h1 vv b) :
    (dEnd Reading.gl W y rs lam om h1 vv b).1 + (dEnd Reading.gl W y rs lam om h1 vv b).2.2.1 =
        sideTerm rs lam b a ∧
      (dEnd Reading.gl W y rs lam om h1 vv b).2.1 +
        (dEnd Reading.gl W y rs lam om h1 vv b).2.2.2.1 = sideTerm rs lam b c := by
  cases ht : b.tri with
  | true => exact term_tri ht h hval T
  | false =>
    cases hk : b.virt with
    | some k => exact term_down ht hk h T
    | none => exact term_forms ht hk h hval T

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.sideTerm_read
#print axioms OnBytes.Road.K4.C.under_one
#print axioms OnBytes.Road.K4.C.grid_at
#print axioms OnBytes.Road.K4.C.sideTerm_grid
#print axioms OnBytes.Road.K4.C.range_mapM_has
#print axioms OnBytes.Road.K4.C.sum_row_col
#print axioms OnBytes.Road.K4.C.term_tri
#print axioms OnBytes.Road.K4.C.grid_div_mod
#print axioms OnBytes.Road.K4.C.grid_place_lt
#print axioms OnBytes.Road.K4.C.term_down
#print axioms OnBytes.Road.K4.C.term_forms
#print axioms OnBytes.Road.K4.C.panel_adds
