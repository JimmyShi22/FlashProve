-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PanelShare.lean: CONDITIONAL.

What is here. One panel of the batched sumcheck: the sum of the products of the two sides that the
honest side lays (`panelTabs`, Johnson/Desc/K4/Honest/Stack.lean) is the weight of the panel's claim
times the library's share of the verifier's panel (`shareP`, Johnson/Road/FormsKeysPort.lean).

  `FormOf`, `PanelTies`   a panel's own forms; the ties
  `sum_cut`   a sum whose later terms are 0
  `share_tri`, `share_virt`, `share_plain`   the three kinds of a panel
  `panel_share`   **one panel**

Limits. At the reading `Reading.gl`. ALL TIES BETWEEN THE TWO SIDES ARE HYPOTHESES, gathered in
`PanelTies`: the honest value of each of the panel's own forms is the form's value in the world Wo
(of no other form: a form that is a bare slot has the honest value 0, whatever the world holds
there); the never-sent vectors hv read as the honest tables of the gated products, inside the
panel's rows and columns; the weight claims' vectors wv read as the honest tables of the weights,
and 0 from the panel's number of columns on; a panel with the selector has as many rows as there are
routed experts; the panel's columns fit its bits. hv, wv and Wo are variables. PanelTiesOf.lean pays
the ties at chosen hv and wv, in every world in which the first of them holds; HvalOf.lean pays that
one in every world with the true entries. No example of the ties together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackSecond
import Johnson.Road.FormsKeysPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE mulE)
open OnBytes.Model (Reading Aff World)
open OnBytes.Model.Layer (SBlk)
open OnBytes.Road (shareP omK wtK rowW aRaw bRaw nRows sideK ov)
open OnBytes.Road.K4.C (sum_grid)
open OnBytes.Desc.First.K4.Honest

/-- **A form of the panel b**: a column factor's, or one of the A side or of the B side. -/
def FormOf (b : SBlk) (a : Aff) : Prop :=
  (∃ yv, yv < b.ny ∧ a = b.xx.getD yv {}) ∨ (∃ A i yv, b.A = some A ∧ A i yv = some a) ∨
    ∃ B i yv, b.B = some B ∧ B i yv = some a

/-- **The ties between the honest side's letters and the library's, at one panel.** -/
structure PanelTies (S : OnBytes.Desc.First.K4.Honest.Sides) (val : Aff → Option E)
    (F : Array (Array E)) (hZ hR : Tab) (Wo : World Cb.Gl.E) (hv wv : ℕ → ℕ → Cb.Gl.E)
    (b : SBlk) : Prop where
  /-- the honest value of a column factor's form is its value in the world -/
  valX : ∀ yv y, yv < b.ny → val (b.xx.getD yv {}) = some y →
    Reading.gl.val y = (b.xx.getD yv {}).value Reading.gl Wo
  /-- the like for a form of the A side -/
  valA : ∀ A i yv f y, b.A = some A → A i yv = some f → val f = some y →
    Reading.gl.val y = f.value Reading.gl Wo
  /-- the like for a form of the B side -/
  valB : ∀ B i yv f y, b.B = some B → B i yv = some f → val f = some y →
    Reading.gl.val y = f.value Reading.gl Wo
  /-- a panel with the selector has a row for each routed expert -/
  rows : b.tri = true → b.ni = S.v.y.h.NE
  /-- the columns fit the bits -/
  cols : b.ny ≤ 2 ^ b.wy
  /-- a never-sent vector that is the column factor of a panel with the selector -/
  hvT : b.tri = true → ∀ k, b.virt = some k → ∀ yv, yv < b.ny →
    hv k yv = Reading.gl.val (hR.getD (S.routedAt (k - 1) yv) zeroE)
  /-- a never-sent vector that is a whole A side -/
  hvP : b.tri = false → ∀ k, b.virt = some k → ∀ i yv, i < b.ni → yv < b.ny →
    hv k (i * 2 ^ b.wy + yv) = Reading.gl.val (hZ.getD (i * S.v.y.Pf + yv) zeroE)
  /-- the one weight claim of a panel with the selector -/
  wvT : b.tri = true → ∀ v0, b.v0 = some v0 → ∀ i yv, i < b.ni → yv < 2 ^ b.wy →
    wv v0 (i * 2 ^ b.wy + yv) = if yv < b.ny then
      Reading.gl.val (at2 (F.getD v0 #[]) (S.kkOf v0) i yv) else 0
  /-- the weight claims of another panel, one for each row -/
  wvP : b.tri = false → ∀ v0, b.v0 = some v0 → ∀ i yv, i < b.ni → yv < 2 ^ b.wy →
    wv (v0 + i) yv = if yv < b.ny then
      Reading.gl.val (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv) else 0

/-- A sum whose terms from n on are 0. -/
theorem sum_cut {n N : ℕ} (h : n ≤ N) (f : ℕ → Cb.Gl.E) (hz : ∀ y, n ≤ y → y < N → f y = 0) :
    ∑ y ∈ Finset.range N, f y = ∑ y ∈ Finset.range n, f y :=
  (Finset.sum_subset (Finset.range_subset_range.mpr h) fun y hy hn =>
    hz y (by simpa using hn) (Finset.mem_range.mp hy)).symm

/-- A place in a grid of ni rows and ny columns lies below the grid's size. -/
theorem grid_lt {i yv ni ny : ℕ} (hi : i < ni) (hy : yv < ny) : i * ny + yv < ni * ny := by
  calc i * ny + yv < i * ny + ny := by omega
    _ = (i + 1) * ny := by rw [Nat.succ_mul]
    _ ≤ ni * ny := Nat.mul_le_mul_right _ hi

variable {S : OnBytes.Desc.First.K4.Honest.Sides} {val : Aff → Option E} {om : Array E}
  {F : Array (Array E)} {hZ hR : Tab} {Wo : World Cb.Gl.E} {hv wv : ℕ → ℕ → Cb.Gl.E} {b : SBlk}

/-- **A panel with the selector.** -/
theorem share_tri (T : PanelTies S val F hZ hR Wo hv wv b) (htri : b.tri = true)
    {x : Array E × Array E} (hx : panelTabs S val om F hZ hR b = some x) :
    ∑ j ∈ Finset.range (b.ni * b.ny),
        Reading.gl.val (x.1.getD j zeroE) * Reading.gl.val (x.2.getD j zeroE) =
      omK Reading.gl om b * shareP Reading.gl Wo S.v.y hv wv b := by
  unfold panelTabs at hx
  simp only [htri, ↓reduceIte] at hx
  obtain ⟨v0, hv0, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨cols, hc, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain rfl := Option.some.inj hx
  unfold shareP nRows
  rw [if_pos htri, ← T.rows htri, sum_grid _ b.ny b.ni, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hb : ∀ yv, yv < 2 ^ b.wy → bRaw Reading.gl Wo wv b i yv = if yv < b.ny then
      Reading.gl.val (at2 (F.getD v0 #[]) (S.kkOf v0) i yv) else 0 := by
    intro yv hy
    unfold bRaw
    rw [htri, hv0]
    exact T.wvT htri v0 hv0 i yv hi' hy
  rw [sum_cut T.cols _ fun yv h1 h2 => by rw [hb yv h2, if_neg (by omega), mul_zero],
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun yv hyv => ?_
  have hyv' := Finset.mem_range.mp hyv
  have hj := grid_lt hi' hyv'
  have ha : aRaw Reading.gl Wo hv b i yv = Reading.gl.val (cols.getD yv zeroE) := by
    have g := amapM_range_get _ hc hyv' zeroE
    unfold aRaw
    rw [htri]
    cases hk : b.virt with
    | some k =>
      simp only [hk] at g
      show hv k yv = _
      rw [T.hvT htri k hk yv hyv', Option.some.inj g]
    | none =>
      simp only [hk] at g
      show (if yv < b.ny then (b.xx.getD yv {}).value Reading.gl Wo else 0) = _
      rw [if_pos hyv', T.valX yv _ hyv' g]
  rw [getD_amap_range _ _ _ hj, getD_amap_range _ _ _ hj, div_grid i b.ny yv hyv',
    mod_grid i b.ny yv hyv', ha, hb yv (lt_of_lt_of_le hyv' T.cols), if_pos hyv', Reading.gl.mul,
    Reading.gl.mul, Reading.gl.mul, Reading.gl.mul]
  unfold omK rowW wtK
  rw [if_pos htri]
  ring

/-- **A panel whose whole A side is a never-sent vector.** -/
theorem share_virt (T : PanelTies S val F hZ hR Wo hv wv b) (htri : b.tri = false) {k : ℕ}
    (hk : b.virt = some k) {x : Array E × Array E}
    (hx : panelTabs S val om F hZ hR b = some x) :
    ∑ j ∈ Finset.range (b.ni * b.ny),
        Reading.gl.val (x.1.getD j zeroE) * Reading.gl.val (x.2.getD j zeroE) =
      omK Reading.gl om b * shareP Reading.gl Wo S.v.y hv wv b := by
  unfold panelTabs at hx
  simp only [htri, Bool.false_eq_true, ↓reduceIte, hk] at hx
  obtain ⟨v0, hv0, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain rfl := Option.some.inj hx
  unfold shareP nRows
  rw [if_neg (by rw [htri]; decide), sum_grid _ b.ny b.ni, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hb : ∀ yv, yv < 2 ^ b.wy → bRaw Reading.gl Wo wv b i yv = if yv < b.ny then
      Reading.gl.val (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv) else 0 := by
    intro yv hy
    unfold bRaw
    rw [htri, hk, hv0]
    exact T.wvP htri v0 hv0 i yv hi' hy
  rw [sum_cut T.cols _ fun yv h1 h2 => by rw [hb yv h2, if_neg (by omega), mul_zero],
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun yv hyv => ?_
  have hyv' := Finset.mem_range.mp hyv
  have hj := grid_lt hi' hyv'
  have ha : aRaw Reading.gl Wo hv b i yv =
      Reading.gl.val (hZ.getD (i * S.v.y.Pf + yv) zeroE) := by
    unfold aRaw
    rw [htri, hk]
    exact T.hvP htri k hk i yv hi' hyv'
  rw [getD_amap_range _ _ _ hj, getD_amap_range _ _ _ hj, div_grid i b.ny yv hyv',
    mod_grid i b.ny yv hyv', ha, hb yv (lt_of_lt_of_le hyv' T.cols), if_pos hyv', Reading.gl.mul,
    Reading.gl.mul, Reading.gl.mul]
  unfold omK rowW wtK
  rw [if_neg (by rw [htri]; decide)]
  ring

/-- **A panel with two factors whose A side is given as forms.** -/
theorem share_plain (T : PanelTies S val F hZ hR Wo hv wv b) (htri : b.tri = false)
    (hk : b.virt = none) {x : Array E × Array E} (hx : panelTabs S val om F hZ hR b = some x) :
    ∑ j ∈ Finset.range (b.ni * b.ny),
        Reading.gl.val (x.1.getD j zeroE) * Reading.gl.val (x.2.getD j zeroE) =
      omK Reading.gl om b * shareP Reading.gl Wo S.v.y hv wv b := by
  unfold panelTabs at hx
  simp only [htri, Bool.false_eq_true, ↓reduceIte, hk] at hx
  obtain ⟨A, hA, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨a, ha, hx⟩ := Option.bind_eq_some_iff.mp hx
  have hxc : ∃ c, (match b.v0, b.B with
      | none, some B =>
        (Array.range (b.ni * b.ny)).mapM fun j => (B (j / b.ny) (j % b.ny)).bind val
      | some v0, _ => some ((Array.range (b.ni * b.ny)).map fun j =>
          at2 (F.getD (v0 + j / b.ny) #[]) (S.kkOf (v0 + j / b.ny)) 0 (j % b.ny))
      | none, none => none) = some c ∧ x = (a, c) := by
    revert hx
    cases b.v0 with
    | some v0 =>
      intro hx
      exact ⟨_, rfl, (Option.some.inj hx).symm⟩
    | none =>
      cases b.B with
      | none =>
        intro hx
        cases hx
      | some B =>
        intro hx
        obtain ⟨c, hc, hx⟩ := Option.bind_eq_some_iff.mp hx
        exact ⟨c, hc, (Option.some.inj hx).symm⟩
  obtain ⟨c, hc, rfl⟩ := hxc
  unfold shareP nRows
  rw [if_neg (by rw [htri]; decide), sum_grid _ b.ny b.ni, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have haR : ∀ yv, aRaw Reading.gl Wo hv b i yv =
      if yv < b.ny then sideK Reading.gl Wo b.A i yv else 0 := by
    intro yv
    unfold aRaw
    rw [htri, hk]
  rw [sum_cut T.cols _ fun yv h1 _ => by rw [haR yv, if_neg (by omega), zero_mul],
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun yv hyv => ?_
  have hyv' := Finset.mem_range.mp hyv
  have hj := grid_lt hi' hyv'
  -- the first side's entry
  have ga := amapM_range_get _ ha hj zeroE
  rw [div_grid i b.ny yv hyv', mod_grid i b.ny yv hyv'] at ga
  obtain ⟨f1, k1, ga⟩ := Option.bind_eq_some_iff.mp ga
  obtain ⟨a1, k2, ga⟩ := Option.bind_eq_some_iff.mp ga
  have eA : aRaw Reading.gl Wo hv b i yv = Reading.gl.val a1 := by
    rw [haR yv, if_pos hyv', hA]
    show ov Reading.gl Wo (A i yv) = _
    rw [k1]
    exact (T.valA A i yv f1 a1 hA k1 k2).symm
  -- the second side's entry
  have eB : bRaw Reading.gl Wo wv b i yv = Reading.gl.val (c.getD (i * b.ny + yv) zeroE) := by
    unfold bRaw
    rw [htri, hk]
    revert hc
    cases h0 : b.v0 with
    | some v0 =>
      intro hc
      show wv (v0 + i) yv = _
      rw [T.wvP htri v0 h0 i yv hi' (lt_of_lt_of_le hyv' T.cols), if_pos hyv',
        ← Option.some.inj hc, getD_amap_range _ _ _ hj, div_grid i b.ny yv hyv',
        mod_grid i b.ny yv hyv']
    | none =>
      cases hB : b.B with
      | none =>
        intro hc
        cases hc
      | some B =>
        intro hc
        have g2 := amapM_range_get _ hc hj zeroE
        rw [div_grid i b.ny yv hyv', mod_grid i b.ny yv hyv'] at g2
        obtain ⟨g, q1, q2⟩ := Option.bind_eq_some_iff.mp g2
        show (if yv < b.ny then sideK Reading.gl Wo (some B) i yv else 0) = _
        rw [if_pos hyv']
        show ov Reading.gl Wo (B i yv) = _
        rw [q1]
        exact (T.valB B i yv g _ hB q1 q2).symm
  rw [← Option.some.inj ga, eA, eB, Reading.gl.mul, Reading.gl.mul, Reading.gl.mul]
  unfold omK rowW wtK
  rw [if_neg (by rw [htri]; decide)]
  ring

/-- **ONE PANEL**: the sum of the products of the honest side's two sides is the weight of the
panel's claim times the library's share. CONDITIONAL: on the ties. -/
theorem panel_share (T : PanelTies S val F hZ hR Wo hv wv b) {x : Array E × Array E}
    (hx : panelTabs S val om F hZ hR b = some x) :
    ∑ j ∈ Finset.range (b.ni * b.ny),
        Reading.gl.val (x.1.getD j zeroE) * Reading.gl.val (x.2.getD j zeroE) =
      omK Reading.gl om b * shareP Reading.gl Wo S.v.y hv wv b := by
  cases htri : b.tri with
  | true => exact share_tri T htri hx
  | false =>
    cases hk : b.virt with
    | some k => exact share_virt T htri hk hx
    | none => exact share_plain T htri hk hx

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sum_cut
#print axioms ProofFile.Honest.K4.grid_lt
#print axioms ProofFile.Honest.K4.share_tri
#print axioms ProofFile.Honest.K4.share_virt
#print axioms ProofFile.Honest.K4.share_plain
#print axioms ProofFile.Honest.K4.panel_share
