-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K1/Written.lean: THE ROW OF THE LOT OF THE COMMITMENTS AT THE WRITTEN
VALUES OF THE FULL SIZE: under five hypotheses by field the lot less its functions is one closed
term, `k1LotW`; and closed facts on that term by Lean's kernel, each looked at with the evaluator
first, with negative tests that are stated positively. Definitions, statements and proofs.

THE FIVE HYPOTHESES OF `k1_row_at` ARE TO BE PAID WITHOUT THE ENTRY TESTS' COMPARISONS. In the
goals' scope the first four are known only under the entry tests' first comparison; whoever spends
that here, to show that the description is made, goes in a circle that Lean does not see. (The
fifth is paid in Johnson/AtFull/Desc/Lots/K1/View.lean.)

  `qW`, `gpW`, `viewAt`, `viewW`, `k1LotW`   the written values. qW: the placeholder of
      Johnson/Desc/K1/Law/QFull.lean with the written layout: the three fields that the lot reads
  `k1_row_at`   **MAIN**: codes, shape, layout, the answers to a sample, the 25 views
  `Row`, `k1Rows`, `asRows`, `rowsB`   the test against the written table of the cut ITSELF
      (`cutFirstFull`, Johnson/Desc/Ok/PlanWritten/CutLit.lean): as many skeletons
      as that table has rows at places of kind K1 inside a link, and the same rows, by
      `sameRows` (Johnson/Desc/Ok/PlanWritten/CutTest.lean)
  `plansB`   each passes its test on the plan and names no run
  `rows_written`, `plans_written`   **BY THE KERNEL: both true at k1LotW's 51 skeletons**
  `nameAt`, `ofCut`, `k1SkW`; `blocks_written`, `k1SkW_length`   **BY THE KERNEL: ONE EQUATION:
      k1LotW.blocks = k1SkW**, the 51 skeletons made of the written table's own rows: the row
      on the blocks' skeletons
  `k1_blocks_at`   **so: ((ProofFile.k1Pure Z).blocks G).map skel = k1SkW**, under the five hypotheses
  `viewBut`; `quiet_bites`, `reads_bites`, `view_bites`, `first_bites`   the tests can fail
  `tree_idle`   at another first tree nothing turns

`rows_written` AND `plans_written` ARE TO BE SPENT TOGETHER. A row of the cut has no column for
the test on the plan: with a block that refuses behind each of the 25 sendings the 51 rows would
stand unturned (`quiet_bites`: the rows: true; the plans: false).
THE NAME COLUMN IS NOT TESTED: in `asRows` each skeleton stands under the written row's own name:
in the description a block bears its spot's name, not the lot's. THE POSITION among the 358 rows
is not tested as a number: the filter keeps the order, and each row bears its own place.

What is not claimed. That any public part has these values. Nothing on soundness. No example of the
head is shown in this file; two, at storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and
headMember_zGap, whose own Limits say what they are worth.

-/
import Johnson.AtFull.Desc.Lots.K1.Twin
import Johnson.Desc.Ok.PlanWritten.CutTest
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc.K1Lot

open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Place)
open _root_.Desc.Plain (GPar)
open VerifiableInference.Desc.K1 (qFull gpOf)
open VerifiableInference.PlanWritten (cutFirstFull sameRows proofSizedFull)
open Johnson.G (codesFull2 layoutFull)
open ProofFile (Ground Pub)
open ProofFile.Sk

/-! ## 1 The written values -/

/-- The first chain's parameters as far as the lot reads them: the placeholder of
Johnson/Desc/K1/Law/QFull.lean with the written layout. -/
def qW : Params.First := { qFull with layout := layoutFull }

/-- One answer to each OOD sample; the chain's first tree is number 0. -/
def gpW : GPar := ⟨1, 0⟩

/-- A segment's view: the head's segment has its two places one piece later. -/
def viewAt (l : ℕ) : View := (if l == 24 then 5 else 4, if l == 24 then 7 else 6, true, true, true)

/-- The 25 views. -/
def viewW : List (ℕ × Option View) := (List.range 25).map fun l => (l, some (viewAt l))

/-- **The lot's written row.** -/
def k1LotW : LotSk := k1LotSk qW gpW viewW

/-! ## 2 The row, under hypotheses by field -/

/-- **K1's lot's row.** The five hypotheses are to be paid WITHOUT the entry tests' comparisons. -/
theorem k1_row_at {Z : Pub} {G : Ground} (hc : G.first.codes = codesFull2)
    (hs : G.first.shape = proofSizedFull.request) (hl : G.first.layout = layoutFull)
    (hgs : Z.P.samples = 1)
    (hv : (G.built.toList.zipIdx.map fun x => (x.2, segView G x)) = viewW) :
    lotSk G (ProofFile.k1Pure Z) = k1LotW := by
  rw [lotSk_k1, hv]
  unfold k1LotW k1LotSk
  rw [k1Sk_congr (q' := qW) hc hs hl, k1Sk_gp qW (gp' := gpW) hgs]

/-! ## 3 Closed facts -/

/-- A row of the cut (Johnson/Desc/Ok/PlanWritten/CutTest.lean). -/
abbrev Row : Type :=
  String × Place × ℕ × ℕ × List (ℕ × List VerifiableInference.Desc.Oracle) × List (ℕ × ℕ)

/-- The written rows at the places of kind K1 inside a link. -/
def k1Rows : List Row :=
  cutFirstFull.filter fun r => r.2.1.kind == .K1 && r.2.1.link.isSome

/-- Skeletons as rows of the cut, each under the name of the written row beside it (the name
column is the spot's, not the lot's). -/
def asRows (ks : List Skel) (ws : List Row) : List Row :=
  (ks.zip ws).map fun x => (x.2.1, x.1.place, x.1.nRounds, x.1.nOracles, x.1.told, x.1.before)

/-- The test: as many as the written rows, and these rows. -/
def rowsB (ks : List Skel) : Bool :=
  decide (ks.length = k1Rows.length) && sameRows (asRows ks k1Rows) k1Rows

/-- The test: each passes its test on the plan and names no run. -/
def plansB (ks : List Skel) : Bool :=
  ks.all fun k => k.planOk && k.claims.isEmpty && k.after.isEmpty

/-- The views with one turned. -/
def viewBut (l : ℕ) (v : Option View) : List (ℕ × Option View) :=
  viewW.map fun y => if y.1 == l then (y.1, v) else y

set_option maxRecDepth 1000000 in
/-- **BY LEAN's KERNEL: the written row's 51 skeletons are the written table's rows** at the
places of kind K1 inside a link, the name aside. -/
theorem rows_written : rowsB k1LotW.blocks = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **BY LEAN's KERNEL: all 51 pass their tests on the plan and name no run.** To be spent with
`rows_written`: a row of the cut has no column for the test on the plan. -/
theorem plans_written : plansB k1LotW.blocks = true := by decide +kernel

/-! ## 4 The row on the blocks' skeletons: the skeletons ARE rows made of the written table -/

/-- The lot's own name for the block at a place: the first segment's opening is piece 1. -/
def nameAt (a : Place) : String :=
  if a.piece == 1 then "K1: the first segment's opening" else "K1: a commitment"

/-- A skeleton made of a written row: the row's five columns behind the name; the lot's own name;
the test on the plan passed; no run. -/
def ofCut (r : Row) : Skel :=
  { name := nameAt r.2.1, place := r.2.1, nRounds := r.2.2.1, nOracles := r.2.2.2.1
    told := r.2.2.2.2.1, before := r.2.2.2.2.2, planOk := true, claims := [], after := [] }

/-- **The lot's written rows**: made of the written table's 51 rows at K1's places inside a link. -/
def k1SkW : List Skel := k1Rows.map ofCut

set_option maxRecDepth 1000000 in
/-- **BY LEAN's KERNEL: ONE EQUATION: the written row's skeletons are these.** It holds
`rows_written` and `plans_written` in one. -/
theorem blocks_written : k1LotW.blocks = k1SkW := by decide +kernel

set_option maxRecDepth 1000000 in
/-- There are 51. -/
theorem k1SkW_length : k1SkW.length = 51 := by decide +kernel

/-- **K1's lot's row on the blocks' skeletons.** The five hypotheses: as at `k1_row_at`. -/
theorem k1_blocks_at {Z : Pub} {G : Ground} (hc : G.first.codes = codesFull2)
    (hs : G.first.shape = proofSizedFull.request) (hl : G.first.layout = layoutFull)
    (hgs : Z.P.samples = 1)
    (hv : (G.built.toList.zipIdx.map fun x => (x.2, segView G x)) = viewW) :
    ((ProofFile.k1Pure Z).blocks G).map skel = k1SkW := by
  have h := congrArg LotSk.blocks (k1_row_at hc hs hl hgs hv)
  rw [blocks_written] at h
  exact h

/-! ## 5 The tests can fail -/

set_option maxRecDepth 1000000 in
/-- Where the quiet step fails (so too where the refuser stands): THE ROWS DO NOT TURN; the test on
the plan fails. -/
theorem quiet_bites : rowsB (k1Sk qW gpW (viewBut 7 (some (4, 6, true, true, false)))) = true ∧
    plansB (k1Sk qW gpW (viewBut 7 (some (4, 6, true, true, false)))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Where the plan names no array at the reads. -/
theorem reads_bites :
    plansB (k1Sk qW gpW (viewBut 24 (some (5, 7, false, true, true)))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Where a segment has no view; where its two pieces are swapped. -/
theorem view_bites : rowsB (k1Sk qW gpW (viewBut 3 none)) = false ∧
    rowsB (k1Sk qW gpW (viewBut 5 (some (6, 4, true, true, true)))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At two answers to a sample; at the placeholder's empty layout. -/
theorem first_bites : plansB (k1Sk qW ⟨2, 0⟩ viewW) = false ∧
    plansB (k1Sk qFull gpW viewW) = false := by
  decide +kernel

/-- At another first tree nothing turns. -/
theorem tree_idle : k1Sk qW ⟨1, 7⟩ viewW = k1Sk qW gpW viewW := k1Sk_gp qW rfl viewW

end Johnson.AtFull.Desc.K1Lot

#print axioms Johnson.AtFull.Desc.K1Lot.k1_row_at
#print axioms Johnson.AtFull.Desc.K1Lot.rows_written
#print axioms Johnson.AtFull.Desc.K1Lot.plans_written
#print axioms Johnson.AtFull.Desc.K1Lot.blocks_written
#print axioms Johnson.AtFull.Desc.K1Lot.k1SkW_length
#print axioms Johnson.AtFull.Desc.K1Lot.k1_blocks_at
#print axioms Johnson.AtFull.Desc.K1Lot.quiet_bites
#print axioms Johnson.AtFull.Desc.K1Lot.reads_bites
#print axioms Johnson.AtFull.Desc.K1Lot.view_bites
#print axioms Johnson.AtFull.Desc.K1Lot.first_bites
#print axioms Johnson.AtFull.Desc.K1Lot.tree_idle
