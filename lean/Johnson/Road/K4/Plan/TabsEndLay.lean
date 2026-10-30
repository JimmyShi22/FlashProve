-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Plan/TabsEndLay.lean: AT A LAYERS' SEGMENT THE TABLES OF THE SMALLNESS TEST END AT
OR BELOW THE PLANNED LENGTH OF THE VECTOR OF READS. "The tables' end": the second component of
K8.tabs' own fold (Johnson/Desc/First/K8/Hear.lean): the first entry behind the last table. General:
wherever the layers' layout and readsOf return; no scope, no numeral.

  (The tables' end as a sum of the families' entries: TabsEndSum.lean.)
  `readsOf_nW`: Reads.nW as readsOf's text writes it.
  **`end_lay`**: where p's families are K8.Asks.layers y rd g and p's columns and rows are those of
    the list of tailsOf: the tables' end is at most rd.nW, with one long table of the stream more at
    g = 0. By the six inequalities of FilledOf.lean; the matrix b's three tables have kbm entries
    each.
  `planG_nU2`: what planG lays as nU[2]: rd.nW, with that one table more at g = 0, in the plan's own
    list of matrices. `ks_at`, `ms_at`, `pair_of`: a list of matrices read as columns, rows, pairs.
Limits. That the layout, readsOf or the planner return anywhere is not said. AN INEQUALITY: by a run
at the full size both sides are equal at all twelve segments (evaluated): not
shown here. Nothing on soundness.

-/
import Johnson.Road.K4.Plan.FilledOf
import Johnson.Road.K4.Plan.TabsEndSum
import Johnson.Road.FormsKeysTab
import Johnson.Desc.First.K8.Hear
import Johnson.Desc.First.K8.Asks
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Plan

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay Reads readsOf matIx)
open OnBytes.Road (Laid2 matsR tails_pair tails_pairs getD_three)
open VerifiableInference.Desc.First.K8 (Par layFamily)
open Fo.BatRows (bindE_ok)

/-! ## The planned length, as the texts write it -/

/-- Reads.nW, as readsOf makes it. -/
theorem readsOf_nW {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) :
    rd.nW = rd.rdAF.length * (y.filled.getD 0 0 * y.T / 2 ^ y.h.la) +
      rd.rdQA.length * (y.filled.getD 3 0 * y.T / 2 ^ y.h.la) +
      (rd.rdXI.length + rd.rdXO.length) * (y.xbFilled * y.T / 2 ^ y.h.la) +
      rd.rdAD.length * y.filled.getD 1 0 + rd.rdAR.length * y.filled.getD 2 0 +
      rd.rdQS.length * y.filled.getD 3 0 + 3 * y.kbm := by
  unfold Layer.readsOf at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    rfl

/-- **The tables' end at a layers' segment.** -/
theorem end_lay {y : Lay} {rd : Reads} {g : ℕ} (L : Laid2 y) (F : Filled y)
    (hrd : readsOf y = .ok rd) (hg : g < y.NGr) (p : Par)
    (ha : p.asks = VerifiableInference.Desc.First.K8.Asks.layers y rd g)
    (hk : ∀ M, p.ks.getD M 0 = ((matsR y g).getD M (0, 0)).2)
    (hm : ∀ M, p.ms.getD M 0 = ((matsR y g).getD M (0, 0)).1) :
    (p.asks.foldl (fun x a => let z := layFamily p a x.2; (x.1 ++ z.1, z.2)) ([], 0)).2 ≤
      rd.nW + (if g == 0 then y.kxb * (y.mxb / 2 ^ y.h.la) else 0) := by
  have at' : ∀ {M m k : ℕ}, (matsR y g).getD M (0, 0) = (m, k) →
      p.ks.getD M 0 = k ∧ p.ms.getD M 0 = m := fun t => ⟨by rw [hk, t], by rw [hm, t]⟩
  have tB : (matsR y g).getD (y.parts.getD 0 0 + y.parts.getD 1 0 + 1) (0, 0) =
      (2 ^ y.h.lmb, y.kbm) := by
    have t3 := (getD_three (y.parts.getD 0 0) (y.parts.getD 1 0)
      (y.mrow.getD 0 0, y.kcol.getD 0 0) (y.mrow.getD 1 0, y.kcol.getD 1 0)
      [(y.mrow.getD 2 0, y.kcol.getD 2 0), (2 ^ y.h.lmb, y.kbm),
       (y.mrow.getD 3 0, y.kcol.getD 3 0), (y.mxb, y.kxb), (y.mxb, y.kxb)] (0, 0)).2.2 1
    unfold matsR
    rw [tails_pairs y hg, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      ← List.getD_eq_getElem?_getD]
    exact t3
  have fAF : famSum p (0, y.parts.getD 0 0, 2 ^ y.h.la) =
      y.parts.getD 0 0 * (y.kcol.getD 0 0 * (y.mrow.getD 0 0 / 2 ^ y.h.la)) :=
    famSum_const p fun q hq => at' (tails_pair y hg (mat := 0) (by decide) hq)
  have fAD : famSum p (y.parts.getD 0 0, y.parts.getD 1 0, y.T) =
      y.parts.getD 1 0 * (y.kcol.getD 1 0 * (y.mrow.getD 1 0 / y.T)) :=
    famSum_const p fun q hq => at' (tails_pair y hg (mat := 1) (by decide) hq)
  have fAR : famSum p (y.parts.getD 0 0 + y.parts.getD 1 0, 1, y.T) =
      y.kcol.getD 2 0 * (y.mrow.getD 2 0 / y.T) :=
    famSum_one p fun q hq => at' (tails_pair y hg (mat := 2) (by decide) hq)
  have fQA : famSum p (y.parts.getD 0 0 + y.parts.getD 1 0 + 2, 1, 2 ^ y.h.la) =
      y.kcol.getD 3 0 * (y.mrow.getD 3 0 / 2 ^ y.h.la) :=
    famSum_one p fun q hq => at' (tails_pair y hg (mat := 3) (by decide) hq)
  have fQS : famSum p (y.parts.getD 0 0 + y.parts.getD 1 0 + 2, 1, y.T) =
      y.kcol.getD 3 0 * (y.mrow.getD 3 0 / y.T) :=
    famSum_one p fun q hq => at' (tails_pair y hg (mat := 3) (by decide) hq)
  have fXI : famSum p (y.parts.getD 0 0 + y.parts.getD 1 0 + 4, 1, 2 ^ y.h.la) =
      y.kxb * (y.mxb / 2 ^ y.h.la) :=
    famSum_one p fun q hq => at' (tails_pair y hg (mat := 4) (by decide) hq)
  have fXO : famSum p (y.parts.getD 0 0 + y.parts.getD 1 0 + 3, 1, 2 ^ y.h.la) =
      y.kxb * (y.mxb / 2 ^ y.h.la) :=
    famSum_one p fun q hq => at' (tails_pair y hg (mat := 5) (by decide) hq)
  have fB : famSum p (y.parts.getD 0 0 + y.parts.getD 1 0 + 1, 1, 2 ^ y.h.lmb) = y.kbm := by
    rw [famSum_one p (k := y.kbm) (m := 2 ^ y.h.lmb) fun q hq => by
      obtain rfl : q = 0 := by omega
      exact at' tB, Nat.div_self (Nat.two_pow_pos _), Nat.mul_one]
  have i1 := Nat.mul_le_mul_left rd.rdAF.length (af_long L F)
  have i2 := Nat.mul_le_mul_left rd.rdQA.length (qa_long L F)
  have i3 := Nat.mul_le_mul_left rd.rdXI.length (xb_long L F)
  have i4 := Nat.mul_le_mul_left rd.rdXO.length (xb_long L F)
  have i5 := Nat.mul_le_mul_left rd.rdAD.length (ad_short L F)
  have i6 := Nat.mul_le_mul_left rd.rdAR.length (ar_short L F)
  have i7 := Nat.mul_le_mul_left rd.rdQS.length (qa_short L F)
  rw [end_sum0, ha, readsOf_nW hrd, Nat.add_mul]
  unfold VerifiableInference.Desc.First.K8.Asks.layers
  by_cases h0 : (g == 0) = true <;> by_cases h4 : y.h.p4 = true <;>
    simp only [h0, h4, Bool.false_eq_true, ↓reduceIte, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate, smul_eq_mul, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, fAF, fAD, fAR, fQA, fQS, fXI, fXO, fB] <;>
    omega

/-! ## The plan's own number -/

/-- **What planG lays as nU[2].** -/
theorem planG_nU2 (P : Layer.Pub) (g : ℕ) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) :
    hp.nU.getD 2 0 = P.rd.nW + (if g == 0 then
      (hp.tl.mats.getD (matIx P.y).iXI {}).k *
        ((hp.tl.mats.getD (matIx P.y).iXI {}).m / 2 ^ P.y.h.la) else 0) := by
  obtain ⟨r, hr, em⟩ := Fo.PlaneMatG.planG_mats P g O hp h
  rw [em]
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, hb, h⟩ := bindE_ok h
  obtain rfl : r = (mats, txOf, ft) := Except.ok.inj (hr.symm.trans hb)
  obtain ⟨tl, _, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, _, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, _, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    rfl
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      rfl
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- A list of matrices, read as columns. -/
theorem ks_at (a : Array TMat) (M : ℕ) : (a.toList.map (·.k)).getD M 0 = (a.getD M {}).k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases a[M]? <;> rfl

/-- As rows. -/
theorem ms_at (a : Array TMat) (M : ℕ) : (a.toList.map (·.m)).getD M 0 = (a.getD M {}).m := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases a[M]? <;> rfl

/-- As pairs. -/
theorem pair_of (a : Array TMat) (M : ℕ) :
    (a.map fun X => (X.m, X.k)).getD M (0, 0) = ((a.getD M {}).m, (a.getD M {}).k) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getD_eq_getD_getElem?]
  cases a[M]? <;> rfl

end OnBytes.Road.K4.Plan

#print axioms OnBytes.Road.K4.Plan.readsOf_nW
#print axioms OnBytes.Road.K4.Plan.end_lay
#print axioms OnBytes.Road.K4.Plan.planG_nU2
#print axioms OnBytes.Road.K4.Plan.ks_at
#print axioms OnBytes.Road.K4.Plan.ms_at
#print axioms OnBytes.Road.K4.Plan.pair_of
