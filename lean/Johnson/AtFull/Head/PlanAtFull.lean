-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Head/PlanAtFull.lean: the plan of the output head's sub-proof returns at the full
size's written numbers: Head.planH2 P.settings (headShape P y) HLy (borderOf y) owner y.NGr P.lkW =
.ok HW, at P := the written value of the parameter file's scan at the stored free numbers, with the
layout HLy and the owner as letters under what planH2 reads of them; HW is one closed term. This is
the premise p19 of the ledger of publicOfO (publicOfO_of_parts), to its letter. Closed
facts by Lean's kernel, and joins. No sub-protocol imports this file.
  PW                the scan's written value (VerifierAndGoals.Lines.scanAt frameRef storedLines)
  headReadsW        the nineteen numbers · ownerW: the owner's four things: AS AN EVALUATION PRINTED
                    THEM at what publicOf returns at VerifierAndGoals.storedPublicFiles (by a sheet for
                    Lean's evaluator that is not in this repository)
  runW              planH2 at the stand-ins made of these (PlanStandIns.lean) · HW: its value
  factsB H          one test with code on a plan: seven numbers · the eight matrices are matsW
                    (Johnson/Desc/Kinds/Law/HeadPlanWritten.lean) · the list of eleven arrays ·
                    their rows and columns · the reader's one entry IS THE OWNER's OWN ENTRY · no
                    entry as an owner · the map of the arrays · the list is closed · the view that
                    the proof file's entry test on shapes compares (headViewH) is xShapeFull's
                    (Johnson/G/XShapeLit.lean), and so is the view of its smallness test
  walkW             BY THE KERNEL, ONE WALK: runW returns and factsB accepts its value
  walk_bent         a negative test by the kernel: with the planes' columns raised by one planH2
                    refuses under "internal-h-forest"
  runW_ok · factsW  runW = .ok HW · factsB HW = true · headView_W | tailView_W: the two views'
                    equations, drawn out of it
  planH2_at         the row at the closed letters hFull | bFull | 12
  planH2_returns    THE ROW, to p19's letter, under three small equations on y
Premises of planH2_returns, by name. h1 : y.lPd = 13 · h2 : borderOf y = Cond.bFull · h3 : y.NGr =
12 (all that p19's term reads of y) · hL : headReads HLy = headReadsW · hO : ownerReads owner =
ownerW.reads.
Who pays. hL: layout_returns (LayoutAtFull.lean beside): by Lean. hO: whoever has the layers' plans
as closed facts: ownerOf takes the last plan and (Layer.matIx y).iXO: one more small equation on y,
on that side. That the ledger's letter P is PW is its p1's to say.
A member of hO: `ownerReads_W` (Johnson/AtFull/Public/OwnerCross.lean), by Lean's kernel.
What the steps behind read. publicOfO lays { H with Fp := H.Fp.trimL }: of the facts here none reads
Fp but "trees"; crossPlans is handed the untrimmed ⟨H.tl, H.Fp, H.Tp⟩ and reads of it plFor, ix.PK,
ix.TX, the records' a at PK, and the matrices' kinds and labels: all in factsB.
Limits. The full size, at the stored free numbers alone. No soundness is claimed. On hiding nothing.

-/
import Johnson.AtFull.Head.PlanStandIns
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.G.XShapeLit
import Johnson.Desc.Ok.PlanWritten.XShapeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtFull.Head
open OnBytes OnBytes.Model OnBytes.Model.Head
open OnBytes.Model.Verify (headShape borderOf)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull Cond.bFull)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (matsW shape_at_stored)
open VerifiableInference.PlanWritten (HeadView callView forestView tailView sameHeadV sameTailO)

/-- The written value of the parameter file's scan at the stored free numbers. -/
abbrev PW : PolScan := VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines

/-- The nineteen numbers. -/
def headReadsW : List Nat :=
  [6, 6, 9, 9, 27, 4, 16, 3, 6, 384, 65536, 4816, 16384, 640, 8192, 15, 1232896, 10240, 120]

/-- The shape of a symbol array with one row of symbols a row. -/
def shOf (m k mS aX a : Nat) : ShP :=
  { m := m, k := k, mS := mS, J := 1, cJ := 0, aX := aX, a := a, R := mS, Rd := 0, Rr := mS,
    K1 := k, Kc := k }

/-- The shape of the stream's symbol array. -/
def shW : ShP := shOf 65536 400 21846 15 2

/-- The owner's own entry for the stream. -/
def entryW : PlaceF :=
  { owner := some 11, rootIndex := some 7, sh := some shW, matrix := some (0, 400, 65536),
    hb := 108, mS := 21846, lanes := 3, padRows := 21846, J := 1, K := 400, off := 0 }

/-- What is read of the owner. -/
def ownerW : OwnerW :=
  { label := 3079, R := 21846, K := 400, ec := 1, a := 2, p := some shW, count := 8,
    entry := entryW }

/-- planH2 at the stand-ins. -/
def runW : Except String HPlanH2 :=
  planH2 PW.settings Cond.hFull (standL headReadsW) Cond.bFull (standO ownerW) 12 PW.lkW

/-- Its value. -/
def HW : HPlanH2 :=
  match runW with
  | .ok H => H
  | .error _ => { tl := {}, Fp := {}, Tp := {} }

/-- The list of the head's eleven arrays. -/
def ntW : Array N2 :=
  #[{ ec := 3 }, { p := some (shOf 65536 4816 21846 15 1) },
    { p := some (shOf 65536 4816 21846 15 1) }, { p := some (shOf 65536 4816 21846 15 1) },
    { p := some (shOf 65536 4816 21846 15 1) }, { p := some (shOf 16384 640 5462 13 1) },
    { p := some (shOf 8192 15 2731 12 1) }, { p := some (shOf 32768 384 10923 14 1) }, {}, {},
    { a := 2, foreign := true, p := some shW }]

/-- The map of the arrays. -/
def ixW : T2Map :=
  { U := #[none, none, some 0, none], ZZ := 8, BZ := 9, TX := #[], FT := #[10],
    PK := #[1, 2, 3, 4, 5, 6, 7], count := 11 }

/-- headView (Johnson/Desc/Ok/PlanWritten/XShape.lean) of a plan. -/
def headViewH (H : HPlanH2) : HeadView :=
  (H.nU.toList, H.ns, H.tl.funClosed, H.tl.lidb, callView H.tl.z1.call, callView H.tl.z2.call,
    forestView H.tl.f9)

/-- One test on a plan. -/
def factsB (H : HPlanH2) : Bool :=
  decide (H.nU = #[0, 0, 61680]) && H.nMsg == 3570 && H.nLin == 297 && H.NCL == 1 &&
    H.lamS == 13 && H.lkW == 18 && H.rows == 24653737 && decide (H.tl.mats = matsW) &&
    H.tl.NM == 8 && decide (H.Tp.nt = ntW) && H.Tp.planned &&
    decide ((H.Fp.trees.map fun X => (X.R, X.K)) = #[(1, 61680), (21846, 4816), (21846, 4816),
      (21846, 4816), (21846, 4816), (5462, 640), (2731, 15), (10923, 384), (128, 770048),
      (32, 2048), (21846, 400)]) &&
    decide (H.tl.plFor = #[entryW]) && decide (H.tl.plOwn = #[]) && decide (H.tl.ix = ixW) &&
    sameHeadV (headViewH H) Johnson.G.xShapeFull.2 &&
    sameTailO (some (tailView H.tl)) (Johnson.G.xShapeFull.1.getD 24 none)

/-- **By the kernel, one walk**: the run returns, and the test accepts its value. -/
theorem walkW : (match runW with
    | .ok H => factsB H
    | .error _ => false) = true := by decide +kernel

/-- A negative test: the planes' columns raised by one. -/
theorem walk_bent : (match planH2 PW.settings Cond.hFull (standL (headReadsW.set 9 385)) Cond.bFull
      (standO ownerW) 12 PW.lkW with
    | .ok _ => false
    | .error e => e == "internal-h-forest") = true := by decide +kernel

theorem runW_ok : runW = .ok HW := by
  have h := walkW
  unfold HW
  cases e : runW with
  | ok H => rfl
  | error s => rw [e] at h; cases h

theorem factsW : factsB HW = true := by
  have h := walkW
  rw [runW_ok] at h
  exact h

/-- The view that the proof file's entry test on shapes compares is the written one. -/
theorem headView_W : headViewH HW = Johnson.G.xShapeFull.2 := by
  have h := factsW
  unfold factsB at h
  simp only [Bool.and_eq_true] at h
  exact (VerifiableInference.PlanWritten.sameHeadV_iff _ _).1 h.1.2

/-- And so is the view of its smallness test. -/
theorem tailView_W : some (tailView HW.tl) = Johnson.G.xShapeFull.1.getD 24 none := by
  have h := factsW
  unfold factsB at h
  simp only [Bool.and_eq_true] at h
  exact (VerifiableInference.PlanWritten.sameTailO_iff _ _).1 h.2

/-- The row at the closed letters. -/
theorem planH2_at {HLy : HL} {owner : Owner} (hL : headReads HLy = headReadsW)
    (hO : ownerReads owner = ownerW.reads) :
    planH2 PW.settings Cond.hFull HLy Cond.bFull owner 12 PW.lkW = .ok HW := by
  have eL : headReads (standL headReadsW) = headReadsW := reads_standL ..
  have eO : ownerReads (standO ownerW) = ownerW.reads :=
    reads_standO ownerW (by decide) (by decide)
  rw [planH2_congr _ _ _ _ _ (hL.trans eL.symm) (hO.trans eO.symm)]
  exact runW_ok

/-- **THE HEAD's PLAN RETURNS**: the premise p19 of the ledger of publicOfO, to its letter. -/
theorem planH2_returns {y : Layer.Lay} {HLy : HL} {owner : Owner} (h1 : y.lPd = 13)
    (h2 : borderOf y = Cond.bFull) (h3 : y.NGr = 12) (hL : headReads HLy = headReadsW)
    (hO : ownerReads owner = ownerW.reads) :
    Head.planH2 PW.settings (headShape PW y) HLy (borderOf y) owner y.NGr PW.lkW = .ok HW := by
  rw [shape_at_stored, h1, h2, h3]
  exact planH2_at hL hO

end AtFull.Head

#print axioms AtFull.Head.walkW
#print axioms AtFull.Head.walk_bent
#print axioms AtFull.Head.runW_ok
#print axioms AtFull.Head.factsW
#print axioms AtFull.Head.headView_W
#print axioms AtFull.Head.tailView_W
#print axioms AtFull.Head.planH2_at
#print axioms AtFull.Head.planH2_returns
