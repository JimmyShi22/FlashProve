-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/PlanValues/KeySizedReturns.lean: at the full size's 32 written lines and the layout of
its ten written sizes the planner's sizing of a key returns, and what it returns is a typed value.

Johnson/Goal/PlanValues/KeySizesAtPlan.lean says what Plan.keySized returns there IF it returns.
Here every test at which the sizing could refuse is evaluated too, each as a closed statement by
Lean's kernel, and the parts are put together by the forward laws of
OnBytes/Params/Fit/KeySizedForward.lean. So the statements "at what the sizing returns" are not idle
at the full size.

Two of the sizing's tests sort a list by List.mergeSort, which the kernel does not reduce. The
layout of the multiplicities: the sorting of six typed blocks is unfolded by simp (keyBlocks_sorted,
KeySizesAtPlan.lean). "Some lookup reaches every row of the matrix": by
Johnson.Pack.coversAllRows_of (Johnson/Top/H/KeyRangesThm.lean), over another sorting of the same
stretches.

Main names.
  keyLin_returns     Params.linSized returns the typed sizes of the test on the table.
  layout_full        the layout of the multiplicities, with the sorting done.
  keyX, admitted_full   the item "ranges", typed through its parts; Wf.admitted says yes of it.
  keyRanges_returns  Plan.rangesSized returns.
  keyFull, keySized_returns   the typed sizes of a key; **Plan.keySized returns them.**
  shape_of_rangesLinesOf   where the planner's steps to the lines of the proof of the ranges
                     return, the first two of them have returned: at all lines and sizes.
  shape_returns      the layout of the committed matrix and what the proof of the ranges looks up
                     are made too: there are Y and sh.
  keySized_exists    so: there are Y, sh with Plan.keySized recordLines sh = some keyFull.

Limits. The sizing alone: that the three plans of a key's chains are made and hold in the planner's
reckoning (Plan.oneTimePlan and its like), that their parameter bytes are read back, and that
Model.Verify.planned returns at any file, is not shown here. Nothing on soundness.

-/
import Johnson.Goal.PlanValues.KeySizesAtPlan
import Johnson.Top.H.KeyRangesThm
import OnBytes.Params.Fit.KeySizedForward

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes OnBytes.Params OnBytes.Plan
open Johnson.Top.H (csKey shMul)

/-! ## 1. The test on the table -/

/-- **The sizing of the test on the table returns.** -/
theorem keyLin_returns :
    linSized recordSet keyLin recordTable {} = some (keyOnceRec, keyCodes1) := by
  have hU : solveStages recordSet (linScopeShared keyLin) keyX1.group keyX1.t keyLin.folded.stages
      = some keyUStages := keyU_stages
  have hO : (if linSplit keyLin then
        solveStages recordSet (linScopeShared keyLin) keyY1.group keyY1.t keyLin.omega.stages
         
      else pure []) = some keyOStages := by
    rw [if_pos (show linSplit keyLin = true by decide)]
    exact keyO_stages
  have hW : solveStages recordSet (linScopeOwn keyLin) keyZ1.group keyZ1.t keyLin.own.stages
      = some keyWStages := keyW_stages
  exact (linSized_of (X := keyX1) (Y := keyY1) (Z := keyZ1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) record_admitted (by decide +kernel)
    (by decide +kernel) keyTurns (by decide +kernel) hU hO hW).trans keyFinish

/-! ## 2. The proof of the ranges -/

/-- The layout of the multiplicities, with the sorting done. -/
theorem layout_full : Wf.layout keyRangesLines.lookups (2 ^ keyRangesLines.group.logL) =
    Wf.layFrom (2 ^ keyRangesLines.group.logL) 0 0
      [⟨1, 0, 5, 18, 0, 0⟩, ⟨1, 32, 2, 15, 0, 0⟩, ⟨1, 36, 1, 14, 0, 0⟩, ⟨0, 0, 5, 13, 0, 0⟩,
        ⟨1, 38, 0, 13, 0, 0⟩, ⟨0, 32, 3, 11, 0, 0⟩] := by
  unfold Wf.layout
  dsimp only
  rw [keyBlocks_eq, keyBlocks_sorted]

/-- The last block of that layout. -/
def keyLast : Wf.Block := ⟨0, 32, 3, 11, 1, 65536⟩

theorem layout_last :
    (Wf.layout keyRangesLines.lookups (2 ^ keyRangesLines.group.logL)).getLast? = some keyLast := by
  rw [layout_full]
  decide +kernel

theorem layout_fits : ((Wf.layout keyRangesLines.lookups (2 ^ keyRangesLines.group.logL)).all
    fun b => decide (2 ^ b.bits ≤ 2 ^ keyRangesLines.group.logL)) = true := by
  rw [layout_full]
  decide +kernel

/-- The item "ranges" of a key of full size. -/
def keyX : WfPublic :=
  rangesX recordSet keyRangesLines 1
    [⟨12, 11, 4, 4⟩, ⟨13, 12, 4, 3⟩, ⟨14, 13, 3, 3⟩, ⟨15, 14, 0, 0⟩] ⟨12, 11, 4, 4⟩

/-- The first lookup reaches every row of the matrix. -/
theorem covers_full : Wf.coversAllRows ⟨18, 3076096⟩ Johnson.Pack.lk0Full = true :=
  Johnson.Pack.coversAllRows_of ⟨18, 3076096⟩ Johnson.Pack.lk0Full rfl
    (fun s hs => of_decide_eq_true (List.all_eq_true.1 Johnson.Pack.full_begin₀ s hs))
    Johnson.Pack.full_cover₀

set_option maxRecDepth 1000000 in
theorem admitted_a : (Wf.publicOk keyX && (⟨18, 3076096⟩ : Wf.Matrix).ok &&
    keyX.lookups.all (Wf.fitsMatrix ⟨18, 3076096⟩)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem admitted_b : (decide (keyX.message.shape.code < csKey.base.size) &&
    decide (keyX.message.shape.maskCode < csKey.mask.size)) = true := by decide +kernel

theorem admitted_c :
    (((Wf.layout keyX.lookups (csKey.base.getD keyX.message.shape.code default).ell).head?.any
      fun b => decide (2 ^ b.bits ≤ (csKey.base.getD keyX.message.shape.code default).ell)) &&
    ((Wf.layout keyX.lookups (csKey.base.getD keyX.message.shape.code default).ell).getLast?.any
      fun b => b.row + 1 == keyX.message.shape.mainRows)) = true := by
  have e : Wf.layout keyX.lookups (csKey.base.getD keyX.message.shape.code default).ell =
      Wf.layout keyRangesLines.lookups (2 ^ keyRangesLines.group.logL) := by
    have e1 : (csKey.base.getD keyX.message.shape.code default).ell =
        2 ^ keyRangesLines.group.logL := by decide +kernel
    rw [e1]
    rfl
  rw [e, layout_full]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem admitted_d : (decide (Wf.ownMasks keyX ⟨18, 3076096⟩ ≤
      Send.freeMaskEntries keyX.message.shape.maskRows
        (csKey.mask.getD keyX.message.shape.maskCode default).ell keyX.message.shape.answers) &&
    (keyX.stages.head?.any fun t =>
      t.code == keyX.message.shape.code && t.maskCode == keyX.message.shape.maskCode) &&
    ioppOk csKey keyX.stages keyX.message.shape.answers) = true := by decide +kernel

/-- **The test on the item "ranges" with the matrix's size and the codes says yes.** -/
theorem admitted_full : Wf.admitted csKey keyX ⟨18, 3076096⟩ = true := by
  have a := admitted_a
  have b := admitted_b
  have c := admitted_c
  have d := admitted_d
  have v : keyX.lookups.any (Wf.coversAllRows ⟨18, 3076096⟩) = true :=
    List.any_eq_true.2 ⟨Johnson.Pack.lk0Full, List.mem_cons_self, covers_full⟩
  simp only [Bool.and_eq_true] at a b c d
  unfold Wf.admitted
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨a.1.1, a.1.2⟩, a.2⟩, v⟩, b.1⟩, b.2⟩, c⟩, d.1.1⟩, d.1.2⟩, d.2⟩

/-- The sizes of the proof of the ranges of a key of full size. -/
def keyRanges : RangesSized :=
  ⟨keyRangesLines, ⟨18, 3076096⟩, keyX, ⟨keyR1, 49, keyRStages⟩, 24⟩

set_option maxRecDepth 1000000 in
/-- **The sizing of the proof of the ranges returns.** -/
theorem keyRanges_returns : rangesSized recordSet keyRangesLines keyCodes1 =
    some (keyRanges, csKey) := by
  have h := rangesSized_of (s := recordSet) (L := keyRangesLines) (codes := keyCodes1)
    (codes' := csKey) (last := keyLast) (test := ⟨keyR1, 49, keyRStages⟩)
    (stages := [⟨12, 11, 4, 4⟩, ⟨13, 12, 4, 3⟩, ⟨14, 13, 3, 3⟩, ⟨15, 14, 0, 0⟩])
    (first := ⟨12, 11, 4, 4⟩) (by decide +kernel) (by decide +kernel) layout_fits layout_last
    (by decide +kernel) (by decide +kernel)
    (by
      show solveTest recordSet .once recordLines.onceRanges
        (rangesLoad recordSet keyRangesLines 1) id (rangesGroup recordSet keyRangesLines 1) = _
      rw [rangesLoad_full, rangesGroup_full]
      exact keyR_test)
    numbering_full rfl admitted_full
  rw [h]
  have e : (keyRangesLines.lookups.map (·.parts.length)).sum = 24 := by decide +kernel
  rw [e]
  rfl

/-! ## 3. A key's sizes -/

/-- The sizes of the blocks of a key of full size. -/
def keyFull : KeySized := ⟨recordSet, keyOnceRec, keyRanges, csKey⟩

/-- **The sizing of a key returns**, at the written lines and at what the proof of the ranges looks
up in the layout of the ten written sizes. -/
theorem keySized_returns {Y : Model.WsLay} {sh : Shape}
    (hY : Model.wsLayOf wsFull true recordLines.blockLog = .ok Y)
    (hs : shapeOfLayout Y Y.lk = some sh) : keySized recordLines sh = some keyFull :=
  keySized_of record_table (rangesLines_full hY hs) (by rw [keyMaskRows_full]; rfl)
    (by rw [keyMaskRows_full]; exact keyLin_returns) keyRanges_returns

/-- Where the planner's steps to the lines of the proof of the ranges return, the first two of them
have returned: at all lines and sizes. -/
theorem shape_of_rangesLinesOf {l : Lines} {w : Model.WsShape} {p3 : Bool} {r : RangesLines}
    (h : rangesLinesOf l w p3 = some r) :
    ∃ Y sh, Model.wsLayOf w p3 l.blockLog = .ok Y ∧ shapeOfLayout Y Y.lk = some sh := by
  unfold rangesLinesOf at h
  cases hY : Model.wsLayOf w p3 l.blockLog with
  | error e =>
    rw [hY] at h
    cases h
  | ok Y =>
    rw [hY] at h
    dsimp only at h
    cases hs : shapeOfLayout Y Y.lk with
    | none =>
      rw [hs] at h
      cases h
    | some sh => exact ⟨Y, sh, rfl, hs⟩

/-- The layout of the committed matrix and what the proof of the ranges looks up are made. -/
theorem shape_returns : ∃ Y sh, Model.wsLayOf wsFull true recordLines.blockLog = .ok Y ∧
    shapeOfLayout Y Y.lk = some sh :=
  shape_of_rangesLinesOf rangesLinesOf_full

/-- **So the sizing of a key of full size is made.** -/
theorem keySized_exists : ∃ Y sh, Model.wsLayOf wsFull true recordLines.blockLog = .ok Y ∧
    shapeOfLayout Y Y.lk = some sh ∧ keySized recordLines sh = some keyFull := by
  obtain ⟨Y, sh, hY, hs⟩ := shape_returns
  exact ⟨Y, sh, hY, hs, keySized_returns hY hs⟩

end Lk6.AtPlan

#print axioms Lk6.AtPlan.keyLin_returns
#print axioms Lk6.AtPlan.admitted_full
#print axioms Lk6.AtPlan.keyRanges_returns
#print axioms Lk6.AtPlan.keySized_returns
#print axioms Lk6.AtPlan.keySized_exists
