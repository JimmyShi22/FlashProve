-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OpenShapes.lean: CONDITIONAL.

What is here. The honest side's table of one weight claim (`openOf`, `at2`,
Johnson/Desc/K4/Honest/Sides.lean) at the three shapes of a unit: the groups kk, x; the groups kk,
e, x; the groups hd, cd, kk. Entry by entry it reads as the sum that the claim speaks of, at the
picked indices of the open groups, written out.

  `getD_beyond`, `openOf_parts`   an array beyond its end; what a return of `openOf` says
  `open_two`, `open_three`, `open_last`   the open names, the extents
  `tab_two`, `tab_three`, `tab_last`   **the entries**

Limits. At the reading `Reading.gl`. The unit's list of groups is given by its members and their
names; the unit meets the library's condition `UnitOK`; the honest function returns. The claim's
factors are letters. AT THE THIRD SHAPE (`tab_last`): of the array itself, not of `at2`, and inside
the two extents alone; nothing on an entry outside; the two others are total (0 outside). Nothing on
which units a layout has. Nothing on a commitment, a slot or a world.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.UnitsSel
import Johnson.Desc.K4.Honest.Sides

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE)
open OnBytes.Model (Reading WsLay WsUnit WsGrp WsFac WsClaim)
open OnBytes.Road (UnitOK sumSel sumSel_some sumSel_none wgtOf)
open OnBytes.Desc.First.K4.Honest

/-- **What a return of `openOf` says.** -/
theorem openOf_parts {lay : WsLay} {w : ℕ → ℕ → F} {g0 : ℕ} {c : WsClaim} {o : Open} {u : WsUnit}
    (hu : lay.U[c.ui]? = some u) (h : openOf lay w g0 c = some o) :
    fbFree lay w c (["cd", "e", "kk"].filter fun n => u.g.any fun G => G.name == n) = some o.tab ∧
      o.kk = ((u.g.find? fun G => G.name == "kk").map (·.R)).getD 0 ∧
      o.cd = ((u.g.find? fun G => G.name == "cd").map (·.R)).getD 0 ∧ o.lam = u.l - g0 := by
  unfold openOf at h
  rw [hu] at h
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
  split at h
  · simp at h
  · obtain ⟨tab, ht, e⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj e
    exact ⟨ht, rfl, rfl, rfl⟩

variable {lay : WsLay} {w : ℕ → ℕ → F} {g0 : ℕ} {c : WsClaim} {o : Open} {u : WsUnit}

/-! ## 1 The groups kk, x -/

section Two
variable {g1 g2 : WsGrp} (hg : u.g = [g1, g2]) (n1 : g1.name = "kk") (n2 : g2.name = "x")
include hg n1 n2

/-- The one open name; the extents. -/
theorem open_two (hu : lay.U[c.ui]? = some u) (h : openOf lay w g0 c = some o) :
    fbFree lay w c ["kk"] = some o.tab ∧ o.kk = g1.R ∧ o.cd = 0 := by
  obtain ⟨a, b, d, _⟩ := openOf_parts hu h
  rw [hg] at a b d
  simp [n1, n2] at a b d
  exact ⟨a, b, d⟩

/-- **An entry**, at the column yv. -/
theorem tab_two (hu : lay.U[c.ui]? = some u) (U : UnitOK lay.lk u)
    (h : openOf lay w g0 c = some o) {X1 X2 : WsFac} (hf : c.f = [X1, X2]) (yv : ℕ) :
    Reading.gl.val (at2 o.tab o.kk 0 yv) = if yv < g1.R then
      ∑ x ∈ Finset.range g2.R,
        OnBytes.Road.facAt Reading.gl X2 g2 x * wgtOf u (wmOf w) [yv, x] else 0 := by
  obtain ⟨ht, hk, _⟩ := open_two hg n1 n2 hu h
  unfold at2
  rw [hk]
  by_cases hy : yv < g1.R
  · rw [if_pos hy, if_pos hy]
    have hnd : (u.g.map (·.name)).Nodup := by
      rw [hg]
      simp [n1, n2]
    have e := fbFree_sel w ["kk"] hu U hnd (by simp) ht (fun _ => yv) (by
      intro g hgm hn
      rw [hg] at hgm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm hn
      rcases hgm with rfl | rfl
      · exact hy
      · rw [n2] at hn
        exact absurd hn (by decide))
    have en : numFree (stridesOf u ["kk"]).1 (fun _ => yv) = 0 * g1.R + yv := by
      simp [numFree, stridesOf]
    rw [en] at e
    rw [e, hg, hf]
    show sumSel Reading.gl _ [(X1, g1), (X2, g2)] _ = _
    rw [sumSel_some Reading.gl (v := yv) (by simp [selFree, n1]), if_pos hy,
      sumSel_none Reading.gl (by simp [selFree, n2])]
    rfl
  · rw [if_neg hy, if_neg hy]
    exact Reading.gl.zero

end Two

/-- An entry beyond an array's end. -/
theorem getD_beyond (a : Array E) {i : ℕ} (h : a.size ≤ i) : a.getD i zeroE = zeroE := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

/-! ## 2 The groups kk, e, x -/

section Three
variable {g1 g2 g3 : WsGrp} (hg : u.g = [g1, g2, g3]) (n1 : g1.name = "kk") (n2 : g2.name = "e")
  (n3 : g3.name = "x")
include hg n1 n2 n3

/-- The two open names; the extents. -/
theorem open_three (hu : lay.U[c.ui]? = some u) (h : openOf lay w g0 c = some o) :
    fbFree lay w c ["e", "kk"] = some o.tab ∧ o.kk = g1.R ∧ o.cd = 0 := by
  obtain ⟨a, b, d, _⟩ := openOf_parts hu h
  rw [hg] at a b d
  simp [n1, n2, n3] at a b d
  exact ⟨a, b, d⟩

/-- **An entry**, at the row hi and the column yv. -/
theorem tab_three (hu : lay.U[c.ui]? = some u) (U : UnitOK lay.lk u)
    (h : openOf lay w g0 c = some o) {X1 X2 X3 : WsFac} (hf : c.f = [X1, X2, X3]) (hi yv : ℕ) :
    Reading.gl.val (at2 o.tab o.kk hi yv) = if yv < g1.R then (if hi < g2.R then
      ∑ x ∈ Finset.range g3.R,
        OnBytes.Road.facAt Reading.gl X3 g3 x * wgtOf u (wmOf w) [yv, hi, x] else 0)
      else 0 := by
  obtain ⟨ht, hk, _⟩ := open_three hg n1 n2 n3 hu h
  unfold at2
  rw [hk]
  by_cases hy : yv < g1.R
  · rw [if_pos hy, if_pos hy]
    by_cases hh : hi < g2.R
    · rw [if_pos hh]
      have hnd : (u.g.map (·.name)).Nodup := by
        rw [hg]
        simp [n1, n2, n3]
      have e := fbFree_sel w ["e", "kk"] hu U hnd (by simp) ht
        (fun n => if n = "e" then hi else yv) (by
          intro g hgm hn
          rw [hg] at hgm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm hn
          rcases hgm with rfl | rfl | rfl
          · rw [n1]
            exact hy
          · rw [n2]
            exact hh
          · rw [n3] at hn
            exact absurd hn (by decide))
      have en : numFree (stridesOf u ["e", "kk"]).1 (fun n => if n = "e" then hi else yv) =
          hi * g1.R + yv := by
        simp [numFree, stridesOf, hg, n1]
        ring
      rw [en] at e
      rw [e, hg, hf]
      show sumSel Reading.gl _ [(X1, g1), (X2, g2), (X3, g3)] _ = _
      rw [sumSel_some Reading.gl (v := yv) (by simp [selFree, n1]), if_pos hy,
        sumSel_some Reading.gl (v := hi) (by simp [selFree, n2]), if_pos hh,
        sumSel_none Reading.gl (by simp [selFree, n3])]
      rfl
    · rw [if_neg hh, getD_beyond _ (by
        rw [fbFree_size hu ht]
        have es : (stridesOf u ["e", "kk"]).2 = g1.R * g2.R := by
          simp [stridesOf, hg, n1, n2]
        rw [es]
        have : g1.R * g2.R ≤ hi * g1.R := by
          rw [Nat.mul_comm]
          exact Nat.mul_le_mul_right _ (by omega)
        omega)]
      exact Reading.gl.zero
  · rw [if_neg hy, if_neg hy]
    exact Reading.gl.zero

end Three

/-! ## 3 The groups hd, cd, kk -/

section Last
variable {g1 g2 g3 : WsGrp} (hg : u.g = [g1, g2, g3]) (n1 : g1.name = "hd") (n2 : g2.name = "cd")
  (n3 : g3.name = "kk")
include hg n1 n2 n3

/-- The two open names; the extents; the layer's number in the group. -/
theorem open_last (hu : lay.U[c.ui]? = some u) (h : openOf lay w g0 c = some o) :
    fbFree lay w c ["cd", "kk"] = some o.tab ∧ o.kk = g3.R ∧ o.cd = g2.R ∧ o.lam = u.l - g0 := by
  obtain ⟨a, b, d, e⟩ := openOf_parts hu h
  rw [hg] at a b d
  simp [n1, n2, n3] at a b d
  exact ⟨a, b, d, e⟩

/-- **An entry**, at the coordinate cc within a head and the column yv. -/
theorem tab_last (hu : lay.U[c.ui]? = some u) (U : UnitOK lay.lk u)
    (h : openOf lay w g0 c = some o) {X1 X2 X3 : WsFac} (hf : c.f = [X1, X2, X3]) {cc yv : ℕ}
    (hc : cc < g2.R) (hy : yv < g3.R) :
    Reading.gl.val (o.tab.getD (cc * o.kk + yv) zeroE) =
      ∑ a ∈ Finset.range g1.R,
        OnBytes.Road.facAt Reading.gl X1 g1 a * wgtOf u (wmOf w) [a, cc, yv] := by
  obtain ⟨ht, hk, _, _⟩ := open_last hg n1 n2 n3 hu h
  rw [hk]
  have hnd : (u.g.map (·.name)).Nodup := by
    rw [hg]
    simp [n1, n2, n3]
  have e := fbFree_sel w ["cd", "kk"] hu U hnd (by simp) ht
    (fun n => if n = "cd" then cc else yv) (by
      intro g hgm hn
      rw [hg] at hgm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm hn
      rcases hgm with rfl | rfl | rfl
      · rw [n1] at hn
        exact absurd hn (by decide)
      · rw [n2]
        exact hc
      · rw [n3]
        exact hy)
  have en : numFree (stridesOf u ["cd", "kk"]).1 (fun n => if n = "cd" then cc else yv) =
      cc * g3.R + yv := by
    simp [numFree, stridesOf, hg, n1, n2, n3]
    ring
  rw [en] at e
  rw [e, hg, hf]
  show sumSel Reading.gl _ [(X1, g1), (X2, g2), (X3, g3)] _ = _
  rw [sumSel_none Reading.gl (by simp [selFree, n1])]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sumSel_some Reading.gl (v := cc) (by simp [selFree, n2]), if_pos hc,
    sumSel_some Reading.gl (v := yv) (by simp [selFree, n3]), if_pos hy]
  rfl

end Last

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.openOf_parts
#print axioms ProofFile.Honest.K4.open_two
#print axioms ProofFile.Honest.K4.tab_two
#print axioms ProofFile.Honest.K4.getD_beyond
#print axioms ProofFile.Honest.K4.open_three
#print axioms ProofFile.Honest.K4.tab_three
#print axioms ProofFile.Honest.K4.open_last
#print axioms ProofFile.Honest.K4.tab_last
