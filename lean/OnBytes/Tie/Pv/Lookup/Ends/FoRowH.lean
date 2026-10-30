-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoRowH.lean.
The head's key forms: the law of the segment ROW, as a theorem.

The segment ROW holds the digits of the head's row, each times its multiplier. Its form reads each
digit in the table of the matrix hr under the equality weights of the call's position point.

Defines:
  RowFacts R g: facts on public numbers: ROW has as many entries as the head's row has digits; the
    matrix hr has the layout's rows and columns; all the row's digits lie in it.
States:
  eqTab_at: an entry of the table of equality weights, read.
  line_ROW: Fo.LineLaw at the segment ROW, of the form that a run of Head.LINE returns.
Premises of line_ROW: MadeH R; FoundH, RowFacts, LayH (on public numbers and the length of the
record's point); the law of the reads.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLineKit

set_option autoImplicit false

namespace Fo
open TwV Finset OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Ends OnBytes.Ends.H

/-- Facts on public numbers at the segment ROW. -/
structure RowFacts (R : Head.Run) (g : Seg) : Prop where
  n : g.n = ledNRH R.h.XL
  m : (R.hp.tl.mats.getD (R.h.NHf + 1) {}).m = R.L.mR
  k : (R.hp.tl.mats.getD (R.h.NHf + 1) {}).k = R.L.kR
  fit : ledNRH R.h.XL ≤ R.L.kR * (R.L.mR / R.h.T)

/-- An entry of the table of equality weights, read. -/
theorem eqTab_at {K : Type} [CommRing K] (ρ : Reading K) (z : Array E) (i : ℕ)
    (hi : i < 2 ^ z.size) : ρ.val ((eqTab z).getD i zeroE) = eqN (rdA ρ z).reverse i := by
  rw [rdL_getD, eqTab_val, eqTabK_get, if_pos (by rw [rdL_length]; exact hi)]
  rfl

/-- **The law of the segment ROW.** -/
theorem line_ROW {R : Head.Run} {lay : WsLay} {q : ℕ} {g : Seg} (hR : MadeH R)
    (hN : FoundH R q g) (hn : g.name = "ROW") (hL : LayH R q) (hF : RowFacts R g) (F : Fork)
    (c : Ctx) (a : Aff) (h : Head.LINE R g.name F c = .ok ((a, F), c)) (W : World Cb.Gl.E)
    (cell : NameH → Cb.Gl.E)
    (hU : ReadsAll Reading.gl R.hp.tl.mats (funsH R) W.entry R.iU3 (colsOf F R.iU3)
      (fun m r c => cell (.cell m r c))) : LineLaw R lay W cell q g a := by
  -- the table
  obtain ⟨F2, c2, F3, c3, ht⟩ := hR.tabs
  obtain ⟨ZV, YN, qFC, qROW, b0, b1, _, eR, _, hA⟩ := tablesOf_ok _ _ _ _ _ _ _ _ _ _ ht
  obtain ⟨p0, len, t1, _, t3⟩ := tab_hrROW hA
  have hq : qROW = q := Option.some.inj (eR.symm.trans (hn ▸ hN.call))
  rw [hq] at t3
  have hrec := t3 0 (by decide)
  -- the run
  unfold Head.LINE at h
  dsimp only at h
  obtain ⟨ew, G, d, h1, h⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨hew, rfl, rfl⟩ := ewOf_ok R q g hN F G c d ew h1
  rw [hn] at h
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos (by decide)] at h
  obtain ⟨t, G1, d1, h2, h⟩ := (bind_ok _ _ G d _).1 h
  have e2 := tabAt_ok R _ p0 len G d _ t1 h2
  have x0 : t = p0 := congrArg (fun y : (ℕ × Fork) × Ctx => y.1.1) e2
  have x1 : G1 = G := congrArg (fun y : (ℕ × Fork) × Ctx => y.1.2) e2
  have x2 : d1 = d := congrArg (fun y : (ℕ × Fork) × Ctx => y.2) e2
  rw [x0, x1, x2] at h
  obtain ⟨r, G2, d2, h3, h⟩ := (bind_ok _ _ G d _).1 h
  have e4 := (pure_ok _ _ _ _).1 h
  have y0 : a = r := congrArg (fun y : (Aff × Fork) × Ctx => y.1.1) e4
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h3
  obtain ⟨_, _, hv⟩ := loop_val Reading.gl W G d _
    (fun idx => ((if idx < ledNR R.h.XL then ledMu R.h.XL idx else 1 : ℕ) : Cb.Gl.E) *
      Reading.gl.val (ew.getD idx zeroE) *
        (u3Val W.entry R.iU3 (colsOf G R.iU3) (p0 + idx) + 128))
    (fun idx s out ho => by
      obtain ⟨u, G3, d3, k1, k2⟩ := (bind_ok _ _ G d _).1 ho
      have e5 := U3at_ok R p0 idx G d _ k1
      have z1 : G3 = G := congrArg (fun y : (Aff × Fork) × Ctx => y.1.2) e5
      have z2 : d3 = d := congrArg (fun y : (Aff × Fork) × Ctx => y.2) e5
      rw [z1, z2] at k1 k2
      refine ⟨_, thenPure_ok _ G d out k2, ?_⟩
      rw [Aff.value_addMul, Aff.value_add, Aff.value_ofConst, scaleNat_val, ofNat_val,
        U3at_val Reading.gl R p0 idx G G d d u W k1]
      norm_num) _ _ _ h3
  -- the two sides, digit by digit
  have hg : g ∈ (R.L.calls.getD q default).segs := List.mem_of_find?_eq_some hN.seg
  have hsz : g.pos.size = g.n := hL.size g hg
  have hzt : (Head.ztOf R.h R.L R.x.g1 q).size = R.h.lt := by
    unfold Head.ztOf
    dsimp only
    rw [Array.size_extract, hL.point]
    omega
  have hztL : (rdA Reading.gl (Head.ztOf R.h R.L R.x.g1 q)).length = R.h.lt := by
    show (rdL Reading.gl _).length = _
    rw [rdL_length, hzt]
  unfold LineLaw
  rw [y0, hv, Aff.value_empty, zero_add, if_neg (by rw [hn]; decide), add_zero, hF.n]
  have hr : List.range' 0 (Std.Legacy.Range.size [:ledNRH R.h.XL]) 1 =
      List.range (ledNRH R.h.XL) := by
    rw [List.range_eq_range']
    simp [Std.Legacy.Range.size]
  rw [hr]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  have hx' : x < ledNRH R.h.XL := List.mem_range.mp hx
  have hxu : x < R.L.kR * (R.L.mR / R.h.T) := lt_of_lt_of_le hx' hF.fit
  -- the port's side
  have hread := read_part Reading.gl R W.entry (colsOf G R.iU3) (fun m r c => cell (.cell m r c))
    hU (R.h.NHf + 1) R.h.T p0 (eqTab (Head.ztOf R.h R.L R.x.g1 q)) 0 hrec (by omega) x
    (by unfold partLen; rw [Nat.add_zero, hF.m, hF.k]; exact hxu)
  rw [show partStart R.hp.tl.mats (R.h.NHf + 1) R.h.T p0 0 = p0 from rfl] at hread
  rw [hread, hew, ew_get _ _ _ (by rw [hsz, hF.n]; exact hx'), Nat.add_zero, hF.m]
  -- our side
  have haff : affH (pubH R lay) cell g.name x = fun t =>
      ((if x < ledNR R.h.XL then ledMu R.h.XL x else 1 : ℕ) : Cb.Gl.E) *
        (hrC (pubH R lay) cell x t + 128) := by
    funext t
    rw [hn]
    unfold affH
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    rfl
  rw [haff, extL_smul, extL_add, extL_const]
  have hext : extL (hrC (pubH R lay) cell x) (rdA Reading.gl (Head.ztOf R.h R.L R.x.g1 q)) =
      ∑ row ∈ range R.h.T, Reading.gl.val ((eqTab (Head.ztOf R.h R.L R.x.g1 q)).getD row zeroE) *
        cell (.cell (R.h.NHf + 1) (x % (R.L.mR / R.h.T) * R.h.T + row)
          (x / (R.L.mR / R.h.T))) := by
    unfold extL
    rw [lsum, hztL]
    refine Finset.sum_congr rfl fun row hrow => ?_
    have hrow' : row < 2 ^ (Head.ztOf R.h R.L R.x.g1 q).size := by
      rw [hzt]
      exact mem_range.mp hrow
    rw [eqTab_at Reading.gl _ row hrow']
    congr 1
    show cell (cellAt (R.h.NHf + 1) R.L.mR R.L.kR R.h.T x row) = _
    unfold cellAt
    rw [Nat.div_eq_of_lt hxu, Nat.add_zero,
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hxu))]
  rw [hext]
  ring

end Fo
