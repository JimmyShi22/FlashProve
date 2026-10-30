-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/SharesBound.lean: the smallness test's stated numbers at the full size are small: each has a
positive denominator, and its numerator times 2 ^ 124, at the first fall, or 2 ^ 109, at a mark, is at most
the denominator. The public data's shape at each of the 25 segments is the written one
(xShapeFull), which bounds the matrices' columns.

  view_at             a built segment's list of matrices is the written view's
  view_cols           a closed fact on the written view, by Lean's kernel
  view_cols_tight     a control: one column fewer and the fact is false
  cols_le             so a built segment's matrices have at most 24086 columns together
  tau_at              and 128 combinations
  **front_bound**     the first fall's number
  **marks_bound**     the marks' numbers: of no mark of the kinds K3 or K6

Limits. Under the library's head, at the blank ground. A stated number bounds no chance here. Nothing is claimed on completeness, soundness or
hiding.
-/
import Johnson.P5J.K8OwnSizesAt
import Johnson.P1K8R.Part1MarksCode
import Johnson.Desc.ProofFile.Honest.K8.FallNumbers
import Johnson.Desc.ProofFile.Honest.K8.Falls
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsF9Reach
import Johnson.Desc.Sound.K11Tests.NumsHeadInScope
import Johnson.Top.H0.MergeLaw.PlanNumsAt
import Johnson.K8Q14R.TauAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.PlanWritten (tailView xShapeOf)
open Johnson.G (xShapeFull)
open Meaning (viewTail)
open ProofFile.Honest (Odds Mark)
open ProofFile.Honest.K8 (frontFallShare k8ColsAt k8TauAt)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {G₀ : ProofFile.Ground}

/-- The written view: at most 24086 columns at each of the 25 segments. -/
theorem view_cols : (List.range 25).all (fun l =>
    decide (((viewTail xShapeFull l).2.1.map (·.2.2)).sum ≤ 24086)) = true := by decide +kernel

/-- A control: the written view holds data: the bound of view_cols is met with nothing to spare. -/
theorem view_cols_tight : (List.range 25).all (fun l =>
    decide (((viewTail xShapeFull l).2.1.map (·.2.2)).sum ≤ 24085)) = false := by decide +kernel

theorem front_num : 24086 * 127 * (2 ^ 128 + 1) ^ 3 * 2 ^ 124 ≤ Code.pGold ^ 3 * 2 ^ 384 := by
  decide +kernel

theorem den_pos : 0 < Code.pGold ^ 3 * 2 ^ 384 := by decide +kernel

theorem merge_num :
    2 * (18 + 1) * (2 ^ 128 + 1) ^ 3 * 2 ^ 109 ≤ Code.pGold ^ 3 * (2 ^ 128) ^ 3 := by
  decide +kernel

theorem merge_den : 0 < Code.pGold ^ 3 * (2 ^ 128) ^ 3 := by decide +kernel

/-- A built segment's list of matrices is the written view's. -/
theorem view_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : Nat} (hl : l < 25) {Xl : LinkH}
    (hX : G₀.built[l]? = some Xl) : tailView Xl.tl = viewTail xShapeFull l := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have et := ProofFile.Honest.K3.Law.AtThr.built_tl_head h l hl O hX
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  have hV : xShapeOf Zp.p.X = xShapeFull :=
    VerifiableInference.PlanWritten.Joined.xShape_in_scope (o := OnBytes.secondHashFunction) h.scope h.laid.pub hy
  rw [← hV]
  have e : (xShapeOf Zp.p.X).1[l]? = some (some (tailView Xl.tl)) := by
    show ((List.range 25).map fun k =>
      (VerifiableInference.Desc.First.Look.tlAt Zp.p.X k).map tailView)[l]? = _
    rw [List.getElem?_map, List.getElem?_range hl]
    simp [et]
  show tailView Xl.tl = (((xShapeOf Zp.p.X).1[l]?).getD none).getD (0, [], [])
  rw [e]
  rfl

/-- A built segment's matrices have at most 24086 columns together. -/
theorem cols_le (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : Nat} (hl : l < 25) {Xl : LinkH}
    (hX : G₀.built[l]? = some Xl) : (Xl.tl.mats.toList.map (·.k)).sum ≤ 24086 := by
  have hk : Xl.tl.mats.toList.map (·.k) = (viewTail xShapeFull l).2.1.map (·.2.2) := by
    rw [← view_at h hG hl hX]
    simp [tailView, Function.comp_def]
  rw [hk]
  exact of_decide_eq_true (List.all_eq_true.1 view_cols l (List.mem_range.2 hl))

/-- And 128 combinations. -/
theorem tau_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : Nat} (hl : l < 25) {Xl : LinkH}
    (hX : G₀.built[l]? = some Xl) : Xl.tl.tau = 128 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  exact IM.k8_tau_128 h.scope h.reads O (by omega) hX

/-- A sum over the first n entries of a list is at most the list's sum. -/
theorem sum_getD_le : ∀ (L : List Nat) (n : Nat), ∑ i ∈ Finset.range n, L.getD i 0 ≤ L.sum
  | [], n => by simp
  | a :: t, 0 => by simp
  | a :: t, n + 1 => by
    rw [Finset.sum_range_succ']
    have ih := sum_getD_le t n
    simpa [List.sum_cons, Nat.add_comm] using ih

theorem front_of_le {c t : Nat} (hc : c ≤ 24086) (ht : t ≤ 128) :
    0 < (frontFallShare c t).den ∧
      (frontFallShare c t).num * 2 ^ 124 ≤ (frontFallShare c t).den := by
  have e : c * (t - 1) ≤ 24086 * 127 := Nat.mul_le_mul hc (by omega)
  refine ⟨den_pos, ?_⟩
  show c * (t - 1) * (2 ^ 128 + 1) ^ 3 * 2 ^ 124 ≤ Code.pGold ^ 3 * 2 ^ 384
  exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ e)) front_num

/-- **The first fall's number at each of the 25 segments.** -/
theorem front_bound (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : Nat} (hl : l < 25) :
    0 < (frontFallShare (k8ColsAt G₀ l) (k8TauAt G₀ l)).den ∧
      (frontFallShare (k8ColsAt G₀ l) (k8TauAt G₀ l)).num * 2 ^ 124 ≤
        (frontFallShare (k8ColsAt G₀ l) (k8TauAt G₀ l)).den := by
  cases hX : G₀.built[l]? with
  | none =>
    have e1 : k8ColsAt G₀ l = 0 := by unfold k8ColsAt; rw [hX]; rfl
    have e2 : k8TauAt G₀ l = 0 := by unfold k8TauAt; rw [hX]; rfl
    rw [e1, e2]
    exact front_of_le (by omega) (by omega)
  | some Xl =>
    have e1 : k8ColsAt G₀ l = ∑ mu ∈ Finset.range Xl.tl.NM, (Xl.tl.mats.getD mu {}).k := by
      unfold k8ColsAt; rw [hX]; rfl
    have e2 : k8TauAt G₀ l = Xl.tl.tau := by unfold k8TauAt; rw [hX]; rfl
    have hs : ∑ mu ∈ Finset.range Xl.tl.NM, (Xl.tl.mats.getD mu {}).k ≤ 24086 := by
      have e3 : ∀ mu, (Xl.tl.mats.getD mu {}).k = (Xl.tl.mats.toList.map (·.k)).getD mu 0 :=
        fun mu => (P5J.K8N.getD_k _ mu).symm
      simp only [e3]
      exact Nat.le_trans (sum_getD_le _ _) (cols_le h hG hl hX)
    rw [e1, e2, tau_at h hG hl hX]
    exact front_of_le hs (by omega)

/-- A dead mark's number. -/
theorem dead_bound (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : Nat} (hl : l < 25) {Xl : LinkH}
    (hX : G₀.built[l]? = some Xl) (o : Nat) :
    0 < (P1K8.deadRec l o (P1K8.szAt Zp G₀ Xl l)).share.den ∧
      (P1K8.deadRec l o (P1K8.szAt Zp G₀ Xl l)).share.num * 2 ^ 109 ≤
        (P1K8.deadRec l o (P1K8.szAt Zp G₀ Xl l)).share.den := by
  have hc : (P1K8.szAt Zp G₀ Xl l).columns ≤ 24086 := by
    have e := VerifiableInference.Desc.First.K8.columns_eq
      (VerifiableInference.Desc.First.K8.fits_sizeAt (ProofFile.k8Par Zp G₀ Xl l)
        ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, 0, 0, 0⟩)
    have e' : (P1K8.szAt Zp G₀ Xl l).columns =
        VerifiableInference.Desc.First.K8.columns (ProofFile.k8Par Zp G₀ Xl l) := e
    rw [e']
    show (Xl.tl.mats.toList.map (·.k)).foldl (· + ·) 0 ≤ 24086
    rw [VerifiableInference.Desc.First.K8.foldl_add]
    simpa using cols_le h hG hl hX
  have ht : (P1K8.szAt Zp G₀ Xl l).tau = 128 := tau_at h hG hl hX
  show 0 < 2 ^ (P1K8.szAt Zp G₀ Xl l).tau ∧
    (P1K8.szAt Zp G₀ Xl l).columns * 2 ^ 109 ≤ 2 ^ (P1K8.szAt Zp G₀ Xl l).tau
  rw [ht]
  refine ⟨by positivity, ?_⟩
  calc (P1K8.szAt Zp G₀ Xl l).columns * 2 ^ 109 ≤ 24086 * 2 ^ 109 := Nat.mul_le_mul_right _ hc
    _ ≤ 2 ^ 128 := by norm_num

/-- The merge's mark's number. -/
theorem merge_bound (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) :
    0 < (P1K8.mergeRec (_root_.K11.parOf Zp G₀)).share.den ∧
      (P1K8.mergeRec (_root_.K11.parOf Zp G₀)).share.num * 2 ^ 109 ≤
        (P1K8.mergeRec (_root_.K11.parOf Zp G₀)).share.den := by
  have l1 : (_root_.K11.parOf Zp G₀).lay.lk = 18 := by
    rw [← VerifiableInference.Desc.First.MergeLaw.hlay_at hG]
    exact (LT28.K11Tests.m0lk_in_scope h.scope h.pubOne).2
  refine ⟨merge_den, ?_⟩
  show 2 * (List.range' 1 ((_root_.K11.parOf Zp G₀).lay.lk + 1)).length * (2 ^ 128 + 1) ^ 3 * 2 ^ 109 ≤
    Code.pGold ^ 3 * (2 ^ 128) ^ 3
  rw [List.length_range', l1]
  exact merge_num

/-- **The marks' numbers.** -/
theorem marks_bound (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) :
    ∀ mk ∈ P1K8.part1Marks Zp G₀, mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6 ∧
      0 < mk.share.den ∧ mk.share.num * 2 ^ 109 ≤ mk.share.den := by
  intro mk hm
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨l, hl, hf⟩ := List.mem_filterMap.1 hm
    have hl' : l < 25 := List.mem_range.1 hl
    obtain ⟨Xl, hX, rfl⟩ := Option.map_eq_some_iff.1 hf
    exact ⟨fun e => absurd (show KindName.K8 = KindName.K3 from e) (by decide),
      fun e => absurd (show KindName.K8 = KindName.K6 from e) (by decide), dead_bound h hG hl' hX _⟩
  · obtain rfl := List.mem_singleton.1 hm
    exact ⟨fun e => absurd (show KindName.K11 = KindName.K3 from e) (by decide),
      fun e => absurd (show KindName.K11 = KindName.K6 from e) (by decide), merge_bound h hG⟩

end AtFullSide.K8

#print axioms AtFullSide.K8.view_cols
#print axioms AtFullSide.K8.view_cols_tight
#print axioms AtFullSide.K8.view_at
#print axioms AtFullSide.K8.cols_le
#print axioms AtFullSide.K8.front_bound
#print axioms AtFullSide.K8.marks_bound
