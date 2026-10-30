-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WeightTwin.lean: THE OUTPUT HEAD's CLAIM ON THE WEIGHTS (Kinds/HeadCells.lean: forTheMerge; Law/K06Statement.lean: WeightTrue) AND THE CLAIM THAT `verify-on-bytes` MAKES (OnBytes/Model/Head.lean:
weightsClaim, in the closed form of Johnson/Road/HeadWeight.lean: avOf, facKK) SPEAK OF ONE SUM: STATED AND PROVED AT THE LEVEL OF VALUES, UNDER NAMED TIES OF THE LETTERS. Why: K6's block lays no claim
(the real seat's setWeightClaim leaves the record as it is); the merge takes a claim that another text makes of what was heard: the two were twins by reading alone.
  rd_eq_eqN · rd_eq_eqTab   the text's equality weight eq z i reads as the library's kernel, and as entry i of the verifier's table eqTab z.
  rd_eq_eqR                 THE TURN: eq rs k (the first coordinate with k's top bit) is eqR of the REVERSED list (rs[v] with bit v): the program keeps the channels' challenges reversed.
  TwinTies R ew             THE TIES THAT ARE ASKED, BY NAME: T, V · hOn = checked · win · tH.r = rH · x.rs = rs reversed · ew[v] reads as ew .marginTop v · wxOf reads as wx .marginTop.
  twin_vocabulary           under them: avOf R ew at v reads as forTheMerge.onVocabulary v (through avOf_value).
  twin_sum                  AT THE REFERENCE SIZES (V = 202,048 · d = 5,120 · lPd = 13; claimVal_head's premises): the sum that the program's claim speaks of in a matrix W IS the reading of WeightTrue's
                            right side, WHERE THE CELLS' Wh k v READS AS THE LIBRARY's Hof W k v (two byte planes).
  weightTrue_says           so WeightTrue gives K11's sentence: the hidden value under the second end value's variable is the claim's sum over W.
WHAT IT IS NOT. NOT rfl AND NO TIE OF TEXTS: (a) it speaks of the record {ui, [avOf R ew, facKK R.x.rs 10 5 13]}: that the PROGRAM's weightsClaim returns it is weightsClaim_ok; THAT THE DESCRIPTION's OWN TEXT
(Desc/First/Look/LookQuiet.lean: weightsClaim, a plain copy) RETURNS IT IS SHOWN BY NOBODY · (b) TwinTies ARE PREMISES: that the seat's record meets them (heardOf reverses rs: by reading; fromLookup's ew | wx against
ewOf "HD0" | wxOf: by runs alone) is not shown · (c) "Wh reads as Hof W" is a premise: our cells are tied to no witness · (d) the reference sizes alone. Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06Statement
import Johnson.Desc.Kinds.Law.NormPoint
import Johnson.Road.HeadWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Reading eqTab Fork)
open OnBytes.Road (eqR claimVal Wm)
open OnBytes.Road.Hd (avOf facKK avOf_value claimVal_head)
open Norm (lt ls d lPd T S2)

/-! ## The equality weights -/

theorem ptK_eq_pt (z : Point) : ptK z = OnBytes.Road.pt Reading.gl z := by
  funext j
  unfold ptK Blocks.ofList OnBytes.Road.pt
  by_cases hj : j < z.size
  · simp [List.getD_eq_getElem?_getD, Array.getD, hj]
    rfl
  · simp [List.getD_eq_getElem?_getD, Array.getD, hj]
    exact (Reading.gl.zero).symm

theorem rd_eq_eqN (z : Point) (i : Nat) (hi : i < 2 ^ z.size) :
    rd (eq z i) = Blocks.eqN z.size 0 (ptK z) i := by
  rw [rd_eq, if_pos hi, wt_eq_eqN, List.length_map, Array.length_toList]
  rfl

/-- The text's equality weight is the verifier's table's entry. -/
theorem rd_eq_eqTab (z : Point) (i : Nat) (hi : i < 2 ^ z.size) :
    rd (eq z i) = rd ((eqTab z).getD i zeroE) := by
  rw [rd_eq_eqN z i hi, ptK_eq_pt]
  exact (OnBytes.Road.eqTab_value Reading.gl z i hi).symm

/-- **The turn.** -/
theorem rd_eq_eqR (z : Point) (k : Nat) (hk : k < 2 ^ z.size) :
    rd (eq z k) = eqR Reading.gl z.reverse 0 z.size k := by
  rw [rd_eq_eqN z k hk, ptK_eq_pt]
  unfold eqR Blocks.eqN
  rw [Nat.sub_zero]
  refine Finset.prod_congr rfl fun t ht => ?_
  have ht' : t < z.size := Finset.mem_range.mp ht
  have e : OnBytes.Road.pt Reading.gl z (0 + t)
      = Reading.gl.val (z.reverse.getD (z.size - 1 - t) zeroE) := by
    unfold OnBytes.Road.pt
    rw [Nat.zero_add]
    congr 1
    have h1 : z.size - 1 - t < z.reverse.size := by rw [Array.size_reverse]; omega
    have a1 : z.getD t zeroE = z[t]'ht' := by simp [Array.getD, ht']
    have a2 : z.reverse.getD (z.size - 1 - t) zeroE = z.reverse[z.size - 1 - t]'h1 := by
      unfold Array.getD
      rw [dif_pos h1]
      rfl
    rw [a1, a2, Array.getElem_reverse]
    congr 1
    omega
  rw [e]
  simp only [Nat.zero_add]

/-! ## The twin -/

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Heard]

/-- **The ties of the letters that are asked.** R: `verify-on-bytes`'s record of a run at the head; ew: the weights of the segment HD0's entries. -/
structure TwinTies (R : OnBytes.Model.Head.Run) (ew : Array E) : Prop where
  hT : R.h.T = T
  hV : R.h.V = V
  hOn : ∀ t, t < T → R.cov.hOn.getD t false = checked t
  hWin : ∀ t, t < T → checked t = true → R.x.win.getD t 0 = win t
  hrH : R.x.tH.r = rH
  hrHs : (rH : Point).size = lt
  hrs : R.x.rs = (rs : Point).reverse
  hew : ∀ v, v < V → rd (ew.getD v zeroE) = rd (In.ew .marginTop v)
  hwx : rd (OnBytes.Model.Head.wxOf R ew) = rd (In.wx .marginTop)

theorem rd_ite (b : Bool) (x : E) : rd (if b then x else 0) = if b then rd x else 0 := by
  cases b
  · exact rd_zero
  · rfl

/-- **The vocabulary's factor.** -/
theorem twin_vocabulary {R : OnBytes.Model.Head.Run} {ew : Array E} (h : TwinTies R ew) {v : Nat}
    (hv : v < V) : rd ((avOf R ew).getD v zeroE) = rd (forTheMerge.onVocabulary v) := by
  have hv' : v < R.h.V := by rw [h.hV]; exact hv
  have e0 : rd ((avOf R ew).getD v zeroE) = _ := avOf_value Reading.gl R ew hv'
  have hsR : rd (OnBytes.Model.Head.onSum R R.x.tH.r) = (Finset.range R.h.T).sum fun t =>
      if R.cov.hOn.getD t false = true then rd ((eqTab R.x.tH.r).getD t zeroE) else 0 :=
    OnBytes.Road.Hd.foldl_on Reading.gl (fun t => R.cov.hOn.getD t false) (eqTab R.x.tH.r) R.h.T
  have hw : ∀ t, t < T → rd ((eqTab R.x.tH.r).getD t zeroE) = rd (eq rH t) := fun t ht => by
    rw [h.hrH]
    exact (rd_eq_eqTab rH t (by rw [h.hrHs]; exact ht)).symm
  rw [e0]
  show _ = rd (In.wx .marginTop * (sumTo T fun t => if checked t && win t == v then eq rH t else 0)
    - (sumTo T fun t => if checked t then eq rH t else 0) * In.ew .marginTop v)
  rw [rd_sub, rd_mul, rd_mul, rd_sumTo, rd_sumTo]
  have a1 : Reading.gl.val (OnBytes.Model.Head.wxOf R ew) = rd (In.wx .marginTop) := h.hwx
  have a2 : Reading.gl.val (ew.getD v zeroE) = rd (In.ew .marginTop v) := h.hew v hv
  have a3 : Reading.gl.val (OnBytes.Model.Head.onSum R R.x.tH.r) = _ := hsR
  rw [a1, a2, a3, h.hT]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    rw [rd_ite, h.hOn t ht']
    have hw' : Reading.gl.val ((eqTab R.x.tH.r).getD t zeroE) = rd (eq rH t) := hw t ht'
    rw [hw']
    cases hc : checked t
    · simp
    · rw [h.hWin t ht' hc]
      by_cases hq : win t = v
      · simp [hq]
      · simp [hq]
  · congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    rw [rd_ite, h.hOn t ht', hw t ht']

open Inst.Model (ppref) in
open Inst.Model.Layout (kRef) in
open Inst.Model.Head (Hof nV nD) in
/-- **ONE SUM**, at the reference sizes. -/
theorem twin_sum {R : OnBytes.Model.Head.Run} {ew : Array E} (h : TwinTies R ew)
    {s : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW s ppref) {lay : OnBytes.Model.WsLay}
    (hl : OnBytes.Model.wsLayOf s true kRef = .ok lay) (W : Wm K) (c : Cells) (hV : V = nV)
    (hd : d = nD) (hrs : (rs : Point).size = 13)
    (hWh : ∀ k v, k < d → v < V → ((c.Wh k v : Int) : K) = Hof W k v) :
    claimVal Reading.gl lay W
        { ui := lay.U.size - 1, f := [{ AV := avOf R ew }, facKK R.x.rs 10 5 13] } =
      rd (∑ v < V, ∑ k < d,
        forTheMerge.onVocabulary v * eq forTheMerge.onFeatures k * ofInt (c.Wh k v)) := by
  rw [claimVal_head Reading.gl Z hl W (avOf R ew) R.x.rs
    (by rw [h.hrs, Array.size_reverse, hrs]), rd_sumTo, ← hV, ← hd]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [rd_sumTo]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hv' := Finset.mem_range.mp hv
  have hk' := Finset.mem_range.mp hk
  have hk2 : k < 2 ^ (rs : Point).size := by
    rw [hrs]
    have : d = 5120 := hd
    omega
  have b1 : Reading.gl.val ((avOf R ew).getD v zeroE) = rd (forTheMerge.onVocabulary v) :=
    twin_vocabulary h hv'
  have b2 : rd (eq forTheMerge.onFeatures k) = eqR Reading.gl R.x.rs 0 13 k := by
    show rd (eq rs k) = _
    rw [rd_eq_eqR rs k hk2, h.hrs, hrs]
  rw [rd_mul, rd_mul, rd_ofInt, b1, b2, hWh k v hk' hv']

open Inst.Model (ppref) in
open Inst.Model.Layout (kRef) in
open Inst.Model.Head (Hof nV nD) in
/-- **WeightTrue gives K11's sentence**: the hidden value under the second end value's variable is the claim's sum over W. -/
theorem weightTrue_says {R : OnBytes.Model.Head.Run} {ew : Array E} (h : TwinTies R ew)
    {s : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW s ppref) {lay : OnBytes.Model.WsLay}
    (hl : OnBytes.Model.wsLayOf s true kRef = .ok lay) (W : Wm K) (c : Cells) (hV : V = nV)
    (hd : d = nD) (hrs : (rs : Point).size = 13)
    (hWh : ∀ k v, k < d → v < V → ((c.Wh k v : Int) : K) = Hof W k v)
    (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) (hw : WeightTrue c F mask ent) :
    rd (atWorld F mask ent (logits.end_ 1).var) = claimVal Reading.gl lay W
      { ui := lay.U.size - 1, f := [{ AV := avOf R ew }, facKK R.x.rs 10 5 13] } := by
  rw [twin_sum h Z hl W c hV hd hrs hWh]
  exact congrArg rd hw

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.rd_eq_eqR
#print axioms VerifiableInference.Desc.Kinds.Head.Law.twin_vocabulary
#print axioms VerifiableInference.Desc.Kinds.Head.Law.twin_sum
#print axioms VerifiableInference.Desc.Kinds.Head.Law.weightTrue_says
