-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/PlanValues/KeySizesAtPlan.lean: at every three public files in the scope of the goals,
the sizes of the key file's blocks in what the program computes are typed values; and the codes, the
oracle messages' shapes and the proximity tests' stages that Johnson/Top/H/ writes out for a key
file of full size are these.

Johnson/Top/H/KeyRows.lean, KeyFamilies.lean and KeyTowers.lean write out the codes of a key file's
chains (csKey), six shapes of oracle messages (shIdx, shMul, shW, shU, shO, shSp) and the stages of
four proximity tests (sRng1 and so on). Their heads say that the numbers were read off prints of the
planner. Here they are held against the planner's own functions, by Lean's kernel.

The way. Johnson/Goal/PlanValues/ScopeAtPlan.lean: at every file in scope the key's sizes are what
Plan.keySized returns at the written 32 lines and the layout of ten written sizes.
OnBytes/Params/Fit/KeySizedParts.lean takes what it returns apart, every argument named.
OnBytes/Params/KeyOnceRecord.lean and KeyStagesRecordRanges.lean evaluate the parts, turn by turn.
New here: the lines of the proof of the ranges as a typed value; the mask rows of the index-mask
message; the load, the shape and the oracle message of the proof of the ranges; the last block's row
in the layout of the multiplicities (the sorting in Wf.layout is unfolded by simp on six typed
blocks: the kernel does not reduce List.mergeSort); the numbering of the codes.

Main names.
  keyRangesLines, rangesLines_full   the lines of the proof of the ranges, typed; the planner's.
  layout_lastRow                     the last block of the layout lies in row 1.
  keySized_full                      what Plan.keySized returns there: z.once = Params.keyOnceRec,
                                     z.codes = csKey, the test, the stages and the oracle message of
                                     the proof of the ranges, the matrix, the setting.
  keySizes_at_scope                  the same at every three files in scope.
  shapes_written                     shIdx, shW, shU, shO, shSp are the shapes in these sizes
                                     (shMul: in keySized_full).
  FitsStage, towers_written          the 18 written stages have the sizes of the planner's stages,
                                     by the library's relation Sg.FitsGroup, and their numbers of
                                     positions.

Limits. One direction: from a program that returns. Sg.FitsGroup compares the two codes and the two
numbers of row variables; the fields slots, rule and m of a group, overE of its codes and rOod of a
stage are tied to nothing by it. The 18 written radii: Johnson/Top/H/KeyRadiiAtPlan.lean. That the
typed tests at these stages are the tests that a description of the protocol makes is not said here.
Nothing on soundness.
-/
import Johnson.Goal.PlanValues.ScopeAtPlan
import OnBytes.Params.KeyOnceRecord
import OnBytes.Params.KeyStagesRecordRanges
import Johnson.Top.H.KeyFamilies
import OnBytes.Slice.GroupFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes OnBytes.Params OnBytes.Plan
open Johnson.Top.H (csKey shIdx shMul shW shU shO shSp)

deriving instance DecidableEq for RangesLines

/-! ## 1. The lines of the proof of the ranges -/

/-- The lines of the proof of the ranges at full size. -/
def keyRangesLines : RangesLines :=
  ⟨18, 3076096, [Johnson.Pack.lk0Full, Johnson.Pack.lk1Full], recordLines.onceRanges, true, 1⟩

/-- The planner's steps to these lines. -/
def rangesLinesOf (l : Lines) (w : Model.WsShape) (p3 : Bool) : Option RangesLines :=
  match Model.wsLayOf w p3 l.blockLog with
  | .error _ => none
  | .ok Y =>
    match shapeOfLayout Y Y.lk with
    | none => none
    | some sh => rangesLines { sh with kCol := l.blockLog } l.onceRanges l.rangesPart

set_option maxRecDepth 1000000 in
theorem rangesLinesOf_full : rangesLinesOf recordLines wsFull true = some keyRangesLines := by
  decide +kernel

/-- The typed lines are the planner's. -/
theorem rangesLines_full {Y : Model.WsLay} {sh : Shape}
    (hY : Model.wsLayOf wsFull true recordLines.blockLog = .ok Y)
    (hs : shapeOfLayout Y Y.lk = some sh) :
    rangesLines { sh with kCol := recordLines.blockLog } recordLines.onceRanges
      recordLines.rangesPart = some keyRangesLines := by
  have h := rangesLinesOf_full
  unfold rangesLinesOf at h
  rw [hY] at h
  dsimp only at h
  rw [hs] at h
  exact h

/-! ## 2. Closed statements on the proof of the ranges -/

set_option maxRecDepth 1000000 in
theorem keyMaskRows_full : keyMaskRows recordLines keyRangesLines = 1 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rangesGroup_full : rangesGroup recordSet keyRangesLines 1 = keyRShape1 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rangesLoad_full : rangesLoad recordSet keyRangesLines 1 = ⟨23, 1, 981⟩ := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rangesO_full : rangesO recordSet keyRangesLines 1 =
    { mainRows := 2, mainDeg := 1, maskRows := 9, answers := 1 } := by decide +kernel

theorem numbering_full : ioppStages keyRStages keyCodes1 =
    ([⟨12, 11, 4, 4⟩, ⟨13, 12, 4, 3⟩, ⟨14, 13, 3, 3⟩, ⟨15, 14, 0, 0⟩], csKey) := by decide +kernel

/-- The six blocks of the two lookups' planes, in the lookups' order. -/
def keyBlocks : List Wf.Block :=
  [⟨0, 0, 5, 13, 0, 0⟩, ⟨0, 32, 3, 11, 0, 0⟩, ⟨1, 0, 5, 18, 0, 0⟩, ⟨1, 32, 2, 15, 0, 0⟩,
    ⟨1, 36, 1, 14, 0, 0⟩, ⟨1, 38, 0, 13, 0, 0⟩]

set_option maxRecDepth 1000000 in
theorem keyBlocks_eq : (keyRangesLines.lookups.zipIdx.flatMap fun x =>
    (Lkp.liveBlocks (Wf.planesOf x.1)).map fun b =>
      (⟨x.2, b.1, b.2, b.2 + x.1.d, 0, 0⟩ : Wf.Block)) = keyBlocks := by decide +kernel

/-- The blocks, the largest first. -/
theorem keyBlocks_sorted : (keyBlocks.mergeSort fun a b => decide (b.bits ≤ a.bits)) =
    [⟨1, 0, 5, 18, 0, 0⟩, ⟨1, 32, 2, 15, 0, 0⟩, ⟨1, 36, 1, 14, 0, 0⟩, ⟨0, 0, 5, 13, 0, 0⟩,
      ⟨1, 38, 0, 13, 0, 0⟩, ⟨0, 32, 3, 11, 0, 0⟩] := by
  simp [keyBlocks, List.mergeSort, List.MergeSort.Internal.splitInTwo, List.merge]

/-- **The last block of the layout of the multiplicities lies in row 1.** -/
theorem layout_lastRow {last : Wf.Block}
    (h : (Wf.layout keyRangesLines.lookups (2 ^ keyRangesLines.group.logL)).getLast? = some last) :
    last.row = 1 := by
  unfold Wf.layout at h
  dsimp only at h
  rw [keyBlocks_eq, keyBlocks_sorted] at h
  have e : (Wf.layFrom (2 ^ keyRangesLines.group.logL) 0 0
      [⟨1, 0, 5, 18, 0, 0⟩, ⟨1, 32, 2, 15, 0, 0⟩, ⟨1, 36, 1, 14, 0, 0⟩, ⟨0, 0, 5, 13, 0, 0⟩,
        ⟨1, 38, 0, 13, 0, 0⟩, ⟨0, 32, 3, 11, 0, 0⟩]).getLast?.map (·.row) = some 1 := by
    decide +kernel
  rw [h] at e
  exact Option.some.inj e

/-! ## 3. A key's sizes -/

/-- **What the sizing of a key returns at the full size's lines and sizes.** -/
theorem keySized_full {Y : Model.WsLay} {sh : Shape} {z : KeySized}
    (hY : Model.wsLayOf wsFull true recordLines.blockLog = .ok Y)
    (hs : shapeOfLayout Y Y.lk = some sh) (hz : keySized recordLines sh = some z) :
    z.set = recordSet ∧ z.once = keyOnceRec ∧ z.codes = csKey ∧
      z.ranges.test = ⟨keyR1, 49, keyRStages⟩ ∧
      z.ranges.x.stages = [⟨12, 11, 4, 4⟩, ⟨13, 12, 4, 3⟩, ⟨14, 13, 3, 3⟩, ⟨15, 14, 0, 0⟩] ∧
      z.ranges.x.message = ⟨shMul, 0⟩ ∧ z.ranges.x.choice = ⟨true⟩ ∧ z.ranges.pending = 24 := by
  obtain ⟨T, L, codes1, hT, hL, ho, hr, hset⟩ := keySized_named hz
  obtain rfl : T = recordTable := Option.some.inj (hT.symm.trans record_table)
  obtain rfl : L = keyRangesLines := Option.some.inj (hL.symm.trans (rangesLines_full hY hs))
  rw [keyMaskRows_full] at ho
  obtain ⟨e1, rfl⟩ := keyLin_sized ho
  obtain ⟨last, first, hl, ht, hio, hf, hm, hc, hp⟩ := rangesSized_named hr
  have hrow := layout_lastRow hl
  rw [hrow] at ht hm
  have ht' : solveTest recordSet .once recordLines.onceRanges
      (rangesLoad recordSet keyRangesLines 1) id (rangesGroup recordSet keyRangesLines 1) =
        some z.ranges.test := ht
  rw [rangesLoad_full, rangesGroup_full] at ht'
  have et : z.ranges.test = ⟨keyR1, 49, keyRStages⟩ := Option.some.inj (ht'.symm.trans keyR_test)
  rw [et] at hio
  have e2 := hio.symm.trans numbering_full
  have es := (Prod.mk.inj e2).1
  have ec := (Prod.mk.inj e2).2
  rw [es] at hf
  obtain rfl : (⟨12, 11, 4, 4⟩ : IoppStage) = first := Option.some.inj hf
  have hm' : z.ranges.x.message =
      ⟨{ rangesO recordSet keyRangesLines 1 with code := 12, maskCode := 11 }, 0⟩ := hm
  rw [rangesO_full] at hm'
  exact ⟨hset, e1, ec, et, es, hm', hc, hp.trans (by decide +kernel)⟩

/-- **The same at every three public files in the goals' scope.** -/
theorem keySizes_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.key.set = recordSet ∧ p.chains.made.sized.key.once = keyOnceRec ∧
      p.chains.made.sized.key.codes = csKey ∧
      p.chains.made.sized.key.ranges.test = ⟨keyR1, 49, keyRStages⟩ ∧
      p.chains.made.sized.key.ranges.x.stages =
        [⟨12, 11, 4, 4⟩, ⟨13, 12, 4, 3⟩, ⟨14, 13, 3, 3⟩, ⟨15, 14, 0, 0⟩] ∧
      p.chains.made.sized.key.ranges.x.message = ⟨shMul, 0⟩ ∧
      p.chains.made.sized.key.ranges.x.choice = ⟨true⟩ ∧
      p.chains.made.sized.key.ranges.pending = 24 := by
  obtain ⟨Y, sh, hY, hs, hz⟩ := key_at_scope hZ hp
  exact keySized_full hY hs hz

/-! ## 4. The written shapes and stages -/

/-- Five of the six written shapes of oracle messages are the shapes in the typed sizes of the test
on the table (the sixth, shMul: keySized_full). -/
theorem shapes_written : keyOnceRec.input.shape = shIdx ∧ keyOnceRec.shape.w = shW ∧
    keyOnceRec.shape.fold.u = shU ∧ keyOnceRec.shape.omega = shO ∧
    keyOnceRec.shape.sharedSplit = shSp := by decide

/-- A written stage has the sizes of a stage of the planner: the library's own relation between a
stage and a group of the planner (OnBytes/Slice/GroupFit.lean), and the same number of positions. -/
def FitsStage (s : OnBytes.Slice.Sg) (y : StageSize) : Prop := s.FitsGroup y.g ∧ s.t = y.t

open Johnson.Top.H in
/-- **The 18 written stages have the sizes of the planner's stages**, one by one, in their order. -/
theorem towers_written : List.Forall₂ FitsStage [sRng1, sRng2, sRng3, sRng4] keyRStages ∧
    List.Forall₂ FitsStage [sRow1, sRow2, sRow3, sRow4, sRow5] keyUStages ∧
    List.Forall₂ FitsStage [sOmg1, sOmg2, sOmg3, sOmg4] keyOStages ∧
    List.Forall₂ FitsStage [sOwn1, sOwn2, sOwn3, sOwn4, sOwn5] keyWStages := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    repeat' first
      | exact List.Forall₂.nil
      | refine List.Forall₂.cons ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ ?_

end Lk6.AtPlan

#print axioms Lk6.AtPlan.rangesLines_full
#print axioms Lk6.AtPlan.layout_lastRow
#print axioms Lk6.AtPlan.keySized_full
#print axioms Lk6.AtPlan.keySizes_at_scope
#print axioms Lk6.AtPlan.shapes_written
#print axioms Lk6.AtPlan.towers_written
