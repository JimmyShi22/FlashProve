-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/SizedReturns.lean: THE PLANNER's SIZING OF ALL THREE FILES (`Params.sized`,
OnBytes/Params/Configure.lean) RETURNS AT THE WRITTEN LINES OF THE FULL SIZE, AND RETURNS THE
WRITTEN SIZES (`writtenSized`, Johnson/Goal/Written/Made.lean). A forward law at all lines; closed
tests by Lean's kernel; a joining. A law file; no running text imports it. Nothing on codes as such.

  `testsIn`, `longestIn`: two terms of `sized`'s text, named. `sized_of`: **the forward law, at all
    lines and shapes**: five tests that do not refuse · the three sizings return ⊢ sized l x = .ok
    ⟨l, settingOf l, proof, key, link, entryCodes⟩.
  `shape_rows`: what `Plan.shapeOfLayout` returns has the layout's number of rows.
  `proofTests_full`, `keyTests_full`, `table_full`, `linkTest_full`, `listed_full`: the closed tests
    at the written sizes. `tests_bend`: three of them say no without the mask codes.
  `sized_returns`: the four premises of `proofSized_returns` (ProofSizedReturns.lean) on x.sub ·
    x.ranges has 3076096 rows · the key file's sizing returns `keyFull` at x.ranges ⊢ sized
    recordLines x = .ok writtenSized. A VALUE.
  `sized_at_layout`: the same with the last two, and the number of rows, paid by the committed
    table's layout: `keySized_returns` (Johnson/Goal/PlanValues/KeySizedReturns.lean), `m0_full`
    (Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean).

Limits. THE PREMISES ARE PREMISES: none is shown here at any files. What they ask of a public part:
the links as filled (99 typed group lines of the layout file; 25 declared links), 25 open rows, 13
pending rows, and the committed table's layout. `writtenSized` was printed by the library's own
planner: here it is what the sizing returns at written arguments; at no files. `listed_full` holds
by its first clause (no position is listed): the longest code is never weighed. The full size alone.
Nothing on soundness.

-/
import Johnson.AtFull.Made.ProofSizedReturns
import Johnson.Goal.Written.Made
import OnBytes.Tie.EntryPlanAtCfg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open OnBytes.Tie (exc_step exc_go)
open H2K.Sizes VerifiableInference.PlanWritten VerifiableInference.PlanWritten.Joined
open VerifiableInference.Number.ByRuns (writtenLink writtenLink_sized)
open Lk6.AtPlan (keyFull wsFull keySized_returns)

/-! ## 1 The sizing of all three files, forward: at all lines -/

/-- The tests on a finished test on the table: `sized`'s term. -/
def testsIn (l : Lines) (codes : Codes) (S : LinShape) : Bool :=
  linOk codes S && [S.testU, S.testOmega, S.testOwn].all fun t =>
    t.isEmpty || ioppOk codes t (settingOf l).samples

/-- The longest code of a proof's chains and the table: `sized`'s term. -/
def longestIn (l : Lines) (proof : ProofSized) : Nat :=
  (proof.codes.base ++ proof.codes.mask).foldl (fun m c => max m c.logN) l.tableLogN

/-- **The sizing of a proof, a key and an entry, forward.** -/
theorem sized_of {l : Lines} {x : Shapes} {proof : ProofSized} {key : Plan.KeySized}
    {link : LinkSized} {entryCodes : Codes}
    (g1 : (x.sub.matrixRows != x.ranges.matrixRows) = false)
    (hp : proofSized l x.sub = some proof)
    (g2 : (!testsIn l proof.codes proof.batch.shape || !reqOk proof.codes proof.request) = false)
    (hk : Plan.keySized l x.ranges = some key)
    (g3 : (!testsIn l key.codes key.once.shape) = false)
    (hl : linkSized (settingOf l) l proof.batch.table {} = some (link, entryCodes))
    (g4 : (!linkOk entryCodes link.shape (settingOf l).samples) = false)
    (g5 : (l.listed != 0 && l.listed < 8 && 8 * l.listed < longestIn l proof) = false) :
    sized l x = .ok ⟨l, settingOf l, proof, key, link, entryCodes⟩ := by
  unfold sized
  extract_lets
  refine (exc_go _ (not_true_of g1)).trans ?_
  refine (exc_step _ (show orRefuse (proofSized l x.sub) = .ok proof by rw [hp]; rfl)).trans ?_
  refine (exc_go _ (not_true_of g2)).trans ?_
  refine (exc_step _ (show orRefuse (Plan.keySized l x.ranges) = .ok key by rw [hk]; rfl)).trans ?_
  refine (exc_go _ (not_true_of g3)).trans ?_
  refine (exc_step _ (show orRefuse (linkSized (settingOf l) l proof.batch.table {}) =
    .ok (link, entryCodes) by rw [hl]; rfl)).trans ?_
  refine (exc_go _ (not_true_of g4)).trans ?_
  refine (exc_go _ (not_true_of g5)).trans ?_
  rfl

/-- What the key's proof of the ranges looks up has the layout's number of rows. -/
theorem shape_rows {Y : Model.WsLay} {k : Nat} {sh : Plan.Shape}
    (h : Plan.shapeOfLayout Y k = some sh) : sh.matrixRows = Y.m0 := by
  unfold Plan.shapeOfLayout Plan.shapeOfUnits at h
  dsimp only at h
  split at h
  · rw [← Option.some.inj h]
  · cases h

/-! ## 2 The closed tests at the written sizes -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem proofTests_full :
    (!testsIn recordLines proofSizedFull.codes proofSizedFull.batch.shape ||
      !reqOk proofSizedFull.codes proofSizedFull.request) = false := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem keyTests_full : (!testsIn recordLines keyFull.codes keyFull.once.shape) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem table_full : proofSizedFull.batch.table = recordTable := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem linkTest_full : (!linkOk recordCodes writtenLink.shape recordSet.samples) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem listed_full :
    (recordLines.listed != 0 && recordLines.listed < 8 &&
      8 * recordLines.listed < longestIn recordLines proofSizedFull) = false := by
  decide +kernel

/-! ## 3 The whole -/

/-- **`sized` RETURNS THE WRITTEN SIZES** at the written lines: the premise c₂ of
`configure_of_parts` and `chainsOf_of_parts` (Johnson/AtFull/Made/Ledger.lean) at z := writtenSized.
-/
theorem sized_returns {x : Shapes} (h1 : fillLinks x.sub.links = linksFull)
    (h2 : x.sub.openRows = List.replicate 25 1) (h3 : x.sub.pendingRows = 13)
    (h4 : x.sub.matrixRows = 3076096) (h5 : x.ranges.matrixRows = 3076096)
    (hk : Plan.keySized recordLines x.ranges = some keyFull) :
    sized recordLines x = .ok writtenSized :=
  sized_of (by rw [h4, h5]; simp) (proofSized_returns h1 h2 h3 h4) proofTests_full hk keyTests_full
    (by rw [table_full]; exact writtenLink_sized) linkTest_full listed_full

/-- **The same where the ranges are those of the committed table's layout.** -/
theorem sized_at_layout {x : Shapes} {Y : Model.WsLay}
    (hY : Model.wsLayOf wsFull true recordLines.blockLog = .ok Y)
    (hs : Plan.shapeOfLayout Y Y.lk = some x.ranges) (h1 : fillLinks x.sub.links = linksFull)
    (h2 : x.sub.openRows = List.replicate 25 1) (h3 : x.sub.pendingRows = 13)
    (h4 : x.sub.matrixRows = Y.m0) : sized recordLines x = .ok writtenSized :=
  sized_returns h1 h2 h3 (h4.trans (m0_full hY)) ((shape_rows hs).trans (m0_full hY))
    (keySized_returns hY hs)

/-! ## 4 The closed tests can say no -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Without the mask codes each of the three tests on finished shapes says no: by an early clause of
`linOk` or `linkOk`: `ioppOk` is reached in no bend, and what `reqOk` says in the first is not
shown. -/
theorem tests_bend :
    (!testsIn recordLines { proofSizedFull.codes with mask := #[] } proofSizedFull.batch.shape ||
      !reqOk { proofSizedFull.codes with mask := #[] } proofSizedFull.request) = true ∧
    (!testsIn recordLines { keyFull.codes with mask := #[] } keyFull.once.shape) = true ∧
    (!linkOk { recordCodes with mask := #[] } writtenLink.shape recordSet.samples) = true := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.sized_of
#print axioms Johnson.AtFull.Made.shape_rows
#print axioms Johnson.AtFull.Made.proofTests_full
#print axioms Johnson.AtFull.Made.keyTests_full
#print axioms Johnson.AtFull.Made.table_full
#print axioms Johnson.AtFull.Made.linkTest_full
#print axioms Johnson.AtFull.Made.listed_full
#print axioms Johnson.AtFull.Made.sized_returns
#print axioms Johnson.AtFull.Made.sized_at_layout
#print axioms Johnson.AtFull.Made.tests_bend
