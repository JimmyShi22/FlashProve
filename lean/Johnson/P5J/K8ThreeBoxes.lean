-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K8ThreeBoxes.lean: THE SMALLNESS TEST's NAMED TEST ON SIZES (K9.smallSizesB, Johnson/Desc/First/Batch/SmallSizesPlan.lean) FOLLOWS FROM THREE SORTS OF BOX. A reduction of a test with code: NO HEAD, NO SCOPE, NO WRITTEN VALUE. Two definitions, ten theorems.
  Why. The test walks every tie and every read of a segment's plan and asks of each array that is named: has the layout's array of that name rows and columns enough (sizeBoxOf). It reads the tables' shapes (K8.tabs p), which hang on the model's shapes. Gathered into boxes, the tables' shapes are read AT ONE NUMBER ALONE: the tables' end.
  tabsEnd p           THE TABLES' END: the first entry behind the last table: the other half of K8.tabs' own fold (Johnson/Desc/First/K8/Hear.lean keeps the first half alone).
  Below · fam_inv · fam_below · asks_inv · **tabs_below**: every table of K8.tabs p ends at or before tabsEnd p.
  sizeBoxOf_anti      a box is antitone in its two sizes.
  zz_le               under DgP.colsTest (the matrices lie one behind the other; the last ends at mz): every column of the digits' array that a stretch of rows of a matrix names lies below 2 * mz.
  tab_le · getD_k · getD_m   small steps.
  **smallSizes_of_boxes**: UNDER colsTest tl · planFitsB tl (the shapes have their matrices' numbers) · p.ks | p.ms are tl.mats' columns | rows (k8Par's own two fields): FROM (G) at each matrix's tree: (m + 2) / 3 rows, k columns · (Z) at ZZ: p.tau rows, 2 * mz columns · (U) at the third vector of reads: 1 row, tabsEnd p columns: THE TEST ACCEPTS.
(Z) AND (U) ASK MORE THAN THE TEST: the whole width 2 * mz; the whole end. They could fail where the test holds. That they hold at the release's values is not shown here.
Limits. One direction alone. Nothing says that any premise holds at any files. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Batch.SmallSizesPlan
import Johnson.Desc.First.K8.PlanFits
import OnBytes.Tie.Pv.Lookup.Digits.PortCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.K8N
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (sizeBoxOf smallSizesB smallFits tieFits readFits tablesOf ofShape
  readsP_all)
open VerifiableInference.Desc.First.K8 (Par tabs layFamily)
open VerifiableInference.Desc.First.K8.Ready (planFitsB)

/-- **The tables' end**: the first entry behind the last table: the other half of K8.tabs' own fold. -/
def tabsEnd (p : Par) : ℕ :=
  (p.asks.foldl (fun x a => let y := layFamily p a x.2; (x.1 ++ y.1, y.2)) ([], 0)).2

/-- Every table of L ends at or before e. -/
def Below (p : Par) (L : List (ℕ × ℕ × ℕ)) (e : ℕ) : Prop :=
  ∀ x ∈ L, x.2.2 + p.ks.getD x.1 0 * (p.ms.getD x.1 0 / x.2.1) ≤ e

theorem fam_inv (p : Par) (a : ℕ × ℕ × ℕ) : ∀ (l : List ℕ) (x : List (ℕ × ℕ × ℕ) × ℕ),
    Below p x.1 x.2 →
    Below p (l.foldl (fun x q => (x.1 ++ [(a.1 + q, a.2.2, x.2)],
      x.2 + p.ks.getD (a.1 + q) 0 * (p.ms.getD (a.1 + q) 0 / a.2.2))) x).1
      (l.foldl (fun x q => (x.1 ++ [(a.1 + q, a.2.2, x.2)],
      x.2 + p.ks.getD (a.1 + q) 0 * (p.ms.getD (a.1 + q) 0 / a.2.2))) x).2 ∧
    x.2 ≤ (l.foldl (fun x q => (x.1 ++ [(a.1 + q, a.2.2, x.2)],
      x.2 + p.ks.getD (a.1 + q) 0 * (p.ms.getD (a.1 + q) 0 / a.2.2))) x).2
  | [], x, h => ⟨h, Nat.le_refl _⟩
  | q :: l, x, h => by
    rw [List.foldl_cons]
    have h' : Below p (x.1 ++ [(a.1 + q, a.2.2, x.2)])
        (x.2 + p.ks.getD (a.1 + q) 0 * (p.ms.getD (a.1 + q) 0 / a.2.2)) := by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact Nat.le_trans (h y hy) (Nat.le_add_right _ _)
      · obtain rfl := List.mem_singleton.1 hy
        exact Nat.le_refl _
    obtain ⟨k1, k2⟩ := fam_inv p a l (x.1 ++ [(a.1 + q, a.2.2, x.2)],
      x.2 + p.ks.getD (a.1 + q) 0 * (p.ms.getD (a.1 + q) 0 / a.2.2)) h'
    exact ⟨k1, Nat.le_trans (Nat.le_add_right _ _) k2⟩

theorem fam_below (p : Par) (a : ℕ × ℕ × ℕ) (e : ℕ) :
    Below p (layFamily p a e).1 (layFamily p a e).2 ∧ e ≤ (layFamily p a e).2 :=
  fam_inv p a (List.range a.2.1) ([], e) (fun _ hx => by cases hx)

theorem asks_inv (p : Par) : ∀ (l : List (ℕ × ℕ × ℕ)) (x : List (ℕ × ℕ × ℕ) × ℕ),
    Below p x.1 x.2 →
    Below p (l.foldl (fun x a => let y := layFamily p a x.2; (x.1 ++ y.1, y.2)) x).1
      (l.foldl (fun x a => let y := layFamily p a x.2; (x.1 ++ y.1, y.2)) x).2
  | [], _, h => h
  | a :: l, x, h => by
    rw [List.foldl_cons]
    refine asks_inv p l _ ?_
    obtain ⟨k1, k2⟩ := fam_below p a x.2
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact Nat.le_trans (h y hy) k2
    · exact k1 y hy

/-- **Every table ends at or before the tables' end.** -/
theorem tabs_below (p : Par) :
    ∀ x ∈ tabs p, x.2.2 + p.ks.getD x.1 0 * (p.ms.getD x.1 0 / x.2.1) ≤ tabsEnd p :=
  asks_inv p p.asks ([], 0) (fun _ hx => by cases hx)

/-- **A box is antitone in its two sizes.** -/
theorem sizeBoxOf_anti (arr : Array (ℕ × String)) (lay : Params.ReqLayout) (t : ℕ) {R C R' C' : ℕ}
    (hR : R' ≤ R) (hC : C' ≤ C) :
    sizeBoxOf arr lay t R C = true → sizeBoxOf arr lay t R' C' = true := by
  unfold sizeBoxOf
  cases (arr[t]?).bind fun b => reqArray lay b.1 b.2 with
  | none => exact fun h => h
  | some A =>
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact fun h => ⟨Nat.le_trans hR h.1, Nat.le_trans hC h.2⟩

/-- Every column of the digits' array that a stretch of w rows of matrix μ from row i on names lies
below twice mz. -/
theorem zz_le (tl : HTailF2) (hc : DgP.colsTest tl = true) {μ i w : ℕ} (hμ : μ < tl.NM)
    (hi : i + w ≤ (tl.mats.getD μ {}).m) :
    max ((tl.zzCol μ 0 i).getD 0) ((tl.zzCol μ 1 i).getD 0) + w ≤ 2 * tl.mz := by
  have hle : DgP.offOf tl μ + DgP.mOf tl μ ≤ tl.mz := DgP.dgP_col_le hc (tl.NM - μ - 1) μ (by omega)
  unfold DgP.offOf DgP.mOf at hle
  have a0 : (tl.zzCol μ 0 i).getD 0 ≤ tl.off.getD μ 0 + i := by
    unfold HTailF2.zzCol
    split <;> simp
  have a1 : (tl.zzCol μ 1 i).getD 0 ≤ tl.mz + tl.off.getD μ 0 + i := by
    unfold HTailF2.zzCol
    split <;> simp
  have hm : max ((tl.zzCol μ 0 i).getD 0) ((tl.zzCol μ 1 i).getD 0) ≤
      tl.mz + tl.off.getD μ 0 + i := Nat.max_le.2 ⟨by omega, a1⟩
  omega

theorem tab_le (tl : HTailF2) (Fn : HFun) (c sg : ℕ) :
    (tl.tabAt Fn c sg).getD 0 ≤ Fn.start + c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg := by
  unfold HTailF2.tabAt
  split
  · dsimp only
    split <;> simp
  · simp

theorem getD_k (mats : Array TMat) (i : ℕ) :
    (mats.toList.map (·.k)).getD i 0 = (mats.getD i {}).k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases mats[i]? <;> rfl

theorem getD_m (mats : Array TMat) (i : ℕ) :
    (mats.toList.map (·.m)).getD i 0 = (mats.getD i {}).m := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases mats[i]? <;> rfl

/-- **THE NAMED TEST ON SIZES FROM THREE SORTS OF BOX.** -/
theorem smallSizes_of_boxes (arr : Array (ℕ × String)) (lay : Params.ReqLayout) (tl : HTailF2)
    (p : Par) (hc : DgP.colsTest tl = true) (hf : planFitsB tl = true)
    (hk : p.ks = tl.mats.toList.map (·.k)) (hm : p.ms = tl.mats.toList.map (·.m))
    (hG : ∀ μ < tl.NM, sizeBoxOf arr lay (tl.gtTree.getD μ 0) (((tl.mats.getD μ {}).m + 2) / 3)
      (tl.mats.getD μ {}).k = true)
    (hZ : sizeBoxOf arr lay tl.ix.ZZ p.tau (2 * tl.mz) = true)
    (hU : sizeBoxOf arr lay ((tl.ix.U.getD 2 none).getD 0) 1 (tabsEnd p) = true) :
    smallSizesB arr lay tl p = true := by
  have hs : ∀ μ < tl.NM, (tl.shp.getD μ {}).m = (tl.mats.getD μ {}).m ∧
      (tl.shp.getD μ {}).k = (tl.mats.getD μ {}).k := by
    unfold planFitsB at hf
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hf
    exact hf.1.1
  unfold smallSizesB smallFits
  rw [Bool.and_eq_true]
  constructor
  · refine List.all_eq_true.2 fun μ hμ => ?_
    have hμ' : μ < tl.NM := List.mem_range.1 hμ
    obtain ⟨s1, s2⟩ := hs μ hμ'
    show (sizeBoxOf arr lay tl.ix.ZZ p.tau
        (max ((tl.zzCol μ 0 0).getD 0) ((tl.zzCol μ 1 0).getD 0) + (tl.shp.getD μ {}).m) &&
      sizeBoxOf arr lay (tl.gtTree.getD μ 0) (((tl.shp.getD μ {}).m + 2) / 3)
        (tl.shp.getD μ {}).k) = true
    rw [Bool.and_eq_true, s1, s2]
    exact ⟨sizeBoxOf_anti arr lay _ (Nat.le_refl _) (zz_le tl hc hμ' (by omega)) hZ, hG μ hμ'⟩
  · rw [readsP_all]
    refine List.all_eq_true.2 fun μ hμ => List.all_eq_true.2 fun un _ =>
      List.all_eq_true.2 fun Fn hFn => ?_
    have hμ' : μ < tl.NM := List.mem_range.1 hμ
    split
    · rename_i hc1
      refine List.all_eq_true.2 fun sg hsg => ?_
      have hsg' : sg < (tl.mats.getD μ {}).m / Fn.len := List.mem_range.1 hsg
      unfold tablesOf at hFn
      simp only [List.mem_map] at hFn
      obtain ⟨x, hx, rfl⟩ := hFn
      have e1 : x.1 = μ := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hc1
        exact hc1.1
      have hb := tabs_below p x hx
      rw [hk, hm, getD_k, getD_m, e1] at hb
      have hsg2 : sg < (tl.mats.getD μ {}).m / x.2.1 := hsg'
      have hl : sg * x.2.1 + x.2.1 ≤ (tl.mats.getD μ {}).m := by
        have a := Nat.mul_le_mul_right x.2.1 (Nat.succ_le_of_lt hsg2)
        have b := Nat.div_mul_le_self (tl.mats.getD μ {}).m x.2.1
        rw [Nat.succ_mul] at a
        omega
      show (sizeBoxOf arr lay tl.ix.ZZ p.tau
          (max ((tl.zzCol x.1 0 (sg * x.2.1)).getD 0) ((tl.zzCol x.1 1 (sg * x.2.1)).getD 0) +
            x.2.1) &&
        (List.range (tl.mats.getD x.1 {}).k).all fun d =>
          sizeBoxOf arr lay ((tl.ix.U.getD 2 none).getD 0) 1
            ((tl.tabAt (ofShape (x.1, x.2.1, x.2.2, 2)) d sg).getD 0 + 1)) = true
      rw [Bool.and_eq_true, e1]
      refine ⟨sizeBoxOf_anti arr lay _ (Nat.le_refl _) (zz_le tl hc hμ' hl) hZ,
        List.all_eq_true.2 fun d hd => sizeBoxOf_anti arr lay _ (Nat.le_refl _) ?_ hU⟩
      have hd' : d < (tl.mats.getD μ {}).k := List.mem_range.1 hd
      have ht := tab_le tl (ofShape (μ, x.2.1, x.2.2, 2)) d sg
      have ht' : (tl.tabAt (ofShape (μ, x.2.1, x.2.2, 2)) d sg).getD 0 ≤
          x.2.2 + d * ((tl.mats.getD μ {}).m / x.2.1) + sg := ht
      have a := Nat.mul_le_mul_right ((tl.mats.getD μ {}).m / x.2.1) (Nat.succ_le_of_lt hd')
      rw [Nat.succ_mul] at a
      omega
    · rfl

end P5J.K8N

#print axioms P5J.K8N.fam_inv
#print axioms P5J.K8N.fam_below
#print axioms P5J.K8N.asks_inv
#print axioms P5J.K8N.getD_k
#print axioms P5J.K8N.getD_m
#print axioms P5J.K8N.tabs_below
#print axioms P5J.K8N.sizeBoxOf_anti
#print axioms P5J.K8N.zz_le
#print axioms P5J.K8N.tab_le
#print axioms P5J.K8N.smallSizes_of_boxes
