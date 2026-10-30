-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K8OwnSizesAt.lean: THE SMALLNESS TEST's NAMED TEST ON SIZES AT EVERY BUILT SEGMENT (ProofFile.smallSizesOwnB, Johnson/Desc/ProofFile/Lot/K8SmallSizes.lean: the fourth conjunct of the kind's frozen condition) FROM THE HEAD AND TWO THINGS THAT STAY IN FRONT. One definition, ten theorems.
NOT THE END THAT WAS ASKED FOR: TWO PREMISES STAY IN FRONT OF ownSizes_of_ends BESIDE THE HEAD: hW : planFitsAllB Zp.p.X = true (the frozen condition's own second conjunct) · hE: ONE BOX A SEGMENT: the written layout's array (l, "U3") has a row, and at least as many columns as the tables' end of the segment's place (tabsEnd (ProofFile.k8Par Zp G Xl l), Johnson/P5J/K8ThreeBoxes.lean). hE IS TRIED AT NO VALUE. It is the one place where ProofFile.k8Asks is read: the model's shapes (the layers' layout and lists of reads · the attention's shape · the head's shape): in no view, fixed by no pin.
 THE ROAD. smallSizes_of_boxes (K8ThreeBoxes.lean) cuts the test into three sorts of box. A box reads the list of names at ONE index (sizeBoxOf_at): there the names' laws say what stands: at a matrix's tree names_tie_all · at ZZ zz_at_ground · at the third vector u3_at_ground (Johnson/P5J/K8U3Named.lean). Under the head the two pins fix the layout and the view of the plans' tails (how many matrices; each one's label, rows, columns, tree); the digits' width mz is in no view, but under DgP.colsTest (a theorem at whatever publicOf returns: Fo.ZPlan.public_cols) it is the sum of the matrices' rows (mz_of_cols); the number of combinations is 128 in scope.
  K8N.mzW l           the digits' width at the written view.
  BY LEAN's KERNEL:   zzBoxW: the written layout's (l, "ZZ") has 128 rows and 2 * mzW l columns, at all 25 · NEGATIVE TESTS: zzBoxW_cols (one column more) · zzBoxW_rows (one row more): each rejects AT EACH of the 25: the box is tight · gtBoxW: at every matrix of all 25 · gtBoxW_rows: a negative test: one row more: rejects at each · nmPos: every segment has a matrix.
  K8N.sizeBoxOf_at · mz_of_cols · tails_all (what holds at every plan's tail holds at Meaning.tlAt X k, k < 25, where the 24 plans are there).
  **ownSizes_of_ends (h : AtMgA OnBytes.secondHashFunction …) hW hE : ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true.**
Limits. The head is a premise: over the entry tests' asksAt2 and asksAt3 (both pins are spent). At OnBytes.secondHashFunction. The full size alone. The written values rest on their files' own heads. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K8ThreeBoxes
import Johnson.P5J.K8U3Named
import Johnson.P5J.MgAtAll
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.P2LawR.NamesTieAll
import Johnson.HB.LLHARD.TailAtView
import Johnson.HB.LLHARD.BuiltAtName
import Johnson.IMR.NamedOfHeld
import Johnson.IMR.ArraysOpen
import Johnson.Desc.First.Look.ColsAt
import Johnson.P1K8R.PlanFitsTest
import Johnson.P1K8R.FoldAtDraw
import Johnson.Goal.Numbers.TauInScope
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Meaning.PlanNames
import Johnson.Desc.ProofFile.Lot.K8SmallSizes
import Johnson.G.XShapeLit
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J.K8N
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (sizeBoxOf)
open Johnson.G (xShapeFull layoutFull)
open Meaning (viewTail viewEntry ownerK ownerA nameOf)

/-- The digits' width at the written view: the sum of the matrices' rows of cells. -/
def mzW (l : ℕ) : ℕ :=
  ((List.range (viewTail xShapeFull l).1).map fun μ => (viewEntry xShapeFull l μ).2.1).sum

set_option maxRecDepth 1000000 in
theorem zzBoxW :
    (List.range 25).all (fun l => sizeBoxOf #[(l, "ZZ")] layoutFull 0 128 (2 * mzW l)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one column more: it rejects AT EACH of the 25. -/
theorem zzBoxW_cols :
    (List.range 25).all (fun l => !sizeBoxOf #[(l, "ZZ")] layoutFull 0 128 (2 * mzW l + 1)) =
      true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one row more: it rejects AT EACH of the 25. -/
theorem zzBoxW_rows :
    (List.range 25).all (fun l => !sizeBoxOf #[(l, "ZZ")] layoutFull 0 129 (2 * mzW l)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem gtBoxW :
    (List.range 25).all (fun l => (List.range (viewTail xShapeFull l).1).all fun μ =>
      sizeBoxOf #[(ownerK (viewEntry xShapeFull l μ).1, nameOf (ownerA (viewEntry xShapeFull l μ).1))]
        layoutFull 0 (((viewEntry xShapeFull l μ).2.1 + 2) / 3) (viewEntry xShapeFull l μ).2.2) =
      true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one row more: it rejects at each matrix of each of the 25. -/
theorem gtBoxW_rows :
    (List.range 25).all (fun l => (List.range (viewTail xShapeFull l).1).all fun μ =>
      !sizeBoxOf #[(ownerK (viewEntry xShapeFull l μ).1,
          nameOf (ownerA (viewEntry xShapeFull l μ).1))]
        layoutFull 0 (((viewEntry xShapeFull l μ).2.1 + 2) / 3 + 1)
        (viewEntry xShapeFull l μ).2.2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem nmPos : (List.range 25).all (fun l => decide (0 < (viewTail xShapeFull l).1)) = true := by
  decide +kernel

/-- **A box reads the list of names at one index.** -/
theorem sizeBoxOf_at {arr : Array (ℕ × String)} {t : ℕ} {b : ℕ × String} (h : arr[t]? = some b)
    (lay : Params.ReqLayout) (R C : ℕ) :
    sizeBoxOf arr lay t R C = sizeBoxOf #[b] lay 0 R C := by
  unfold sizeBoxOf
  rw [h]
  rfl

/-- **Under colsTest the digits' width is the sum of the matrices' rows of cells.** -/
theorem mz_of_cols (tl : HTailF2) (hc : DgP.colsTest tl = true) (h0 : 0 < tl.NM) :
    tl.mz = ((List.range tl.NM).map fun μ => (tl.mats.getD μ {}).m).sum := by
  unfold DgP.colsTest at hc
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
  obtain ⟨h', h00⟩ := hc
  have off_sum : ∀ μ, μ < tl.NM →
      DgP.offOf tl μ = ((List.range μ).map fun ν => (tl.mats.getD ν {}).m).sum := by
    intro μ
    induction μ with
    | zero => exact fun _ => h00
    | succ n ih =>
      intro hn
      have e := h' n (by omega)
      rw [if_pos hn] at e
      rw [← e, ih (by omega), List.range_succ, List.map_append, List.sum_append]
      simp [DgP.mOf]
  obtain ⟨n, hn⟩ : ∃ n, tl.NM = n + 1 := ⟨tl.NM - 1, by omega⟩
  have e := h' n (by omega)
  rw [if_neg (by omega), off_sum n (by omega)] at e
  rw [hn, List.range_succ, List.map_append, List.sum_append, ← e]
  simp [DgP.mOf]

/-- What holds at every plan's tail holds at Meaning.tlAt X k. -/
theorem tails_all {X : Verify.Public} {P : HTailF2 → Prop}
    (hE : ∀ g < 12, (∃ hp, X.G[g]? = some hp) ∧ ∃ a, X.A[g]? = some a)
    (hG : ∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → P hp.tl)
    (hA : ∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → P a.seam.tl) (hH : P X.H.tl) {k : ℕ}
    (hk : k < 25) : P (Meaning.tlAt X k) := by
  unfold Meaning.tlAt
  rw [if_neg (by omega)]
  by_cases h24 : k = 24
  · rw [if_pos h24]
    exact hH
  · rw [if_neg h24]
    by_cases h2 : k % 2 = 0
    · rw [if_pos h2]
      obtain ⟨hp, e⟩ := (hE (k / 2) (by omega)).1
      rw [e]
      exact hG _ hp e
    · rw [if_neg h2]
      obtain ⟨a, e⟩ := (hE (k / 2) (by omega)).2
      rw [e]
      exact hA _ a e

end P5J.K8N

namespace P5J
open OnBytes OnBytes.Model OnBytes.Model.Stages
open VerifiableInference.Desc
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.K9 (sizeBoxOf)
open VerifiableInference.Desc.First.K8.Ready (planFitsB planFitsAllB)
open Johnson.G (xShapeFull layoutFull)
open Meaning (viewTail viewEntry viewTail_at viewEntry_at ownerK ownerA nameOf labAt)
open VerifiableInference.PlanWritten (xShapeOf)
open VerifiableInference.PlanWritten.Joined (layout_in_scope xShape_in_scope)
open K8N

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE NAMED TEST ON SIZES AT EVERY BUILT SEGMENT, FROM THE HEAD, THE TEST planFitsAllB AND ONE BOX A
SEGMENT.** -/
theorem ownSizes_of_ends (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hW : planFitsAllB Zp.p.X = true)
    (hE : ∀ (G : ProofFile.Ground) (l : ℕ) (Xl : LinkH), ProofFile.blankBy ProofFile.pureRoad.links Zp = some G →
      G.built[l]? = some Xl →
      sizeBoxOf #[(l, "U3")] layoutFull 0 1 (tabsEnd (ProofFile.k8Par Zp G Xl l)) = true) :
    ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true := by
  intro G hG
  have hS := h.toAtMg.scope
  have hR := h.toAtMg.reads
  have hZ : ProofFile.pubPlain OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := h.toAtMg.laid.pub
  have hX : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.toAtMg.pubOne
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  have hy := (pins_of_laid hS h.toAtMg.laid).1
  have hV : xShapeOf Zp.p.X = xShapeFull := xShape_in_scope hS hZ hy
  have hLay : G.first.layout = layoutFull :=
    (P1K8T.layout_at hG).trans (layout_in_scope hS hZ hy)
  have h24 := Meaning.scope_plans24 hS hR hX
  have hEx : ∀ g < 12, (∃ hp, Zp.p.X.G[g]? = some hp) ∧ ∃ a, Zp.p.X.A[g]? = some a :=
    fun g hg => ⟨(h24 g hg).1, (h24 g hg).2.imp fun _ e => e.1⟩
  have hC := Fo.ZPlan.public_cols hX
  have hF := P1K8S.planFitsAll_of_test hW
  have hT := Meaning.Tau.tau_in_scope hS hR hX
  unfold ProofFile.smallSizesOwnB
  refine List.all_eq_true.2 fun y hy' => ?_
  obtain ⟨Xl, l⟩ := y
  have e3 : G.built[l]? = some Xl := by
    rw [List.mk_mem_zipIdx_iff_getElem?, Array.getElem?_toList] at hy'
    exact hy'
  obtain ⟨links, eB⟩ := Meaning.K2.blank_built hG
  have hsz : Zp.p.built.links.size = 25 := built_size hS h.toAtMg.laid
  have hl : l < 25 := by
    have a := (Array.getElem?_eq_some_iff.1 e3).1
    rw [eB, Array.size_zipWith] at a
    omega
  obtain ⟨Y, hY, eY, -⟩ := IM.Own.ownLaid_built hS hR hZ hl
  have etl : Xl.tl = Meaning.tlAt Zp.p.X l := by
    have e4 := e3
    rw [eB] at e4
    obtain ⟨hl', e'⟩ := Array.getElem?_eq_some_iff.1 e4
    rw [Array.getElem_zipWith] at e'
    have hl1 : l < Zp.p.built.links.size := by omega
    obtain rfl : Y = Zp.p.built.links[l]'hl1 :=
      Option.some.inj (hY.symm.trans (Array.getElem?_eq_getElem hl1))
    rw [← e']
    exact eY
  have earr : Xl.arrayOf = Meaning.K2.arrOf Zp l := Meaning.K2.built_arr hG e3
  have hc : DgP.colsTest Xl.tl = true := by
    rw [etl]
    exact tails_all (P := fun t => DgP.colsTest t = true) hEx hC.1 hC.2.1 hC.2.2 hl
  have hf : planFitsB Xl.tl = true := by
    rw [etl]
    exact tails_all (P := fun t => planFitsB t = true) hEx hF.1 hF.2.1 hF.2.2 hl
  have hτ : Xl.tl.tau = 128 := by
    rw [etl]
    exact tails_all (P := fun t => t.tau = 128) hEx hT.1 hT.2.1 hT.2.2 hl
  have a1 : (viewTail xShapeFull l).1 = Xl.tl.NM := by
    rw [← hV, viewTail_at h4 hN hl, etl]
    rfl
  have a3 : ∀ μ, viewEntry xShapeFull l μ =
      (labAt Zp.p.X l μ, (Xl.tl.mats.getD μ {}).m, (Xl.tl.mats.getD μ {}).k) := fun μ => by
    rw [← hV, viewEntry_at h4 hN hl μ, etl]
    rfl
  show K9.smallSizesB Xl.arrayOf G.first.layout Xl.tl (ProofFile.k8Par Zp G Xl l) = true
  refine smallSizes_of_boxes _ _ _ _ hc hf rfl rfl ?_ ?_ ?_
  · intro μ hμ
    have hn := P2Law.Names.names_tie_all hS hR hZ hl (μ := μ) (by rw [etl] at hμ; exact hμ)
    have hn' : Xl.arrayOf[Xl.tl.gtTree.getD μ 0]? =
        some (ownerK (labAt Zp.p.X l μ), nameOf (ownerA (labAt Zp.p.X l μ))) := by
      rw [earr, etl]
      exact hn
    rw [sizeBoxOf_at hn', hLay]
    have g := List.all_eq_true.1 (List.all_eq_true.1 gtBoxW l (List.mem_range.2 hl)) μ
      (List.mem_range.2 (a1 ▸ hμ))
    rw [a3 μ] at g
    exact g
  · rw [sizeBoxOf_at (IM.Own.zz_at_ground hZ hG e3), hLay]
    show sizeBoxOf #[(l, "ZZ")] layoutFull 0 Xl.tl.tau (2 * Xl.tl.mz) = true
    have h0 : 0 < Xl.tl.NM := by
      have b := of_decide_eq_true (List.all_eq_true.1 nmPos l (List.mem_range.2 hl))
      omega
    have em : Xl.tl.mz = mzW l := by
      rw [mz_of_cols Xl.tl hc h0]
      unfold mzW
      rw [a1]
      refine congrArg List.sum (List.map_congr_left fun μ _ => ?_)
      rw [a3 μ]
    rw [hτ, em]
    exact List.all_eq_true.1 zzBoxW l (List.mem_range.2 hl)
  · obtain ⟨tree, ht⟩ : ∃ tree, Xl.tl.ix.U[2]? = some (some tree) := by
      unfold planFitsB at hf
      rw [Bool.and_eq_true] at hf
      have h3 := hf.2
      cases hu : Xl.tl.ix.U[2]? with
      | none =>
        rw [hu] at h3
        cases h3
      | some o =>
        cases o with
        | none =>
          rw [hu] at h3
          cases h3
        | some tree => exact ⟨tree, rfl⟩
    have ei : (Xl.tl.ix.U.getD 2 none).getD 0 = tree := by
      rw [Array.getD_eq_getD_getElem?, ht]
      rfl
    rw [ei, sizeBoxOf_at (u3_at_ground hZ hG e3 tree ht), hLay]
    exact hE G l Xl hG e3

end P5J

#print axioms P5J.K8N.zzBoxW
#print axioms P5J.K8N.zzBoxW_cols
#print axioms P5J.K8N.zzBoxW_rows
#print axioms P5J.K8N.gtBoxW
#print axioms P5J.K8N.gtBoxW_rows
#print axioms P5J.K8N.nmPos
#print axioms P5J.K8N.sizeBoxOf_at
#print axioms P5J.K8N.mz_of_cols
#print axioms P5J.K8N.tails_all
#print axioms P5J.ownSizes_of_ends
