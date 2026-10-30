-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/TocR/RowsReadOfFour.lean: THE NAMED CONDITION `P5J.rowsRead`
(Johnson/Goal/Skeleton/RowsRead.lean: the maker of the rows of the sendings returns at three public
files, and one shape has one radius) FROM TWO RETURNS, FOUR EQUATIONS AND TWO CLOSED FACTS. AT EVERY
Z. A joining: calls alone; nothing is counted or evaluated here. A law file; no running text imports
it. Nothing on codes.

  `returns_of_B` the closed Bool `rowsWB` (Johnson/LPFE1R/RowsAtWritten.lean) says that the closed
    term `rowsW` returns some rows.
  `rowsRead_of_four` the planner of the program `verify-on-bytes` returns p at the files' own digest
    · shapesOf returns · FOUR EQUATIONS: the four fields of p.chains.made that do not hang on the
    digest are the written ones · the open rows are 25 times 1 · the pending rows are 13 · the 26
    links' arms are the written ones · rowsW = .ok R · one shape has one radius at R's ⊢ rowsRead Z.
How: `sendRowsOf_of` (Johnson/Desc/First/Link/Law/RowsFrom.lean) · `rowsFrom_four`, `rowsFrom_congr`
(…/Law/RowsFromCongr.lean) · `groups_W` (Johnson/LPFE1R/RowsAtArms.lean).

Limits. EVERY PREMISE IS A PREMISE: NONE IS SHOWN HERE AT ANY FILES: NO MEMBER. The first equation
is on the FOUR fields that do not hang on the digest: "p.chains.made = writtenMade.at Hung.none" is
not asked: Hung.none has eight empty strings where a plan has the digest and the seven chains'
parameter bytes. The full size alone. Nothing on what a radius means. Nothing on soundness.

-/
import Johnson.LPFE1R.RowsAtArms
import Johnson.Goal.Skeleton.RowsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TocR
open OnBytes OnBytes.Params
open Johnson.G (sendRowsOf SendRow)
open Johnson.G.MadeFree (Free Hung freeOf)
open VerifiableInference.PlanWritten.Joined (writtenMade)
open VerifiableInference.Desc.LinkJoin

/-- The closed Bool says that the closed term returns. -/
theorem returns_of_B (K : rowsWB = true) : ∃ R, rowsW = .ok R := by
  unfold rowsWB at K
  cases hR : rowsW with
  | ok R => exact ⟨R, rfl⟩
  | error e =>
    rw [hR] at K
    cases K

/-- **From the two returns, four equations, the closed term's return and "one shape, one radius".**
At every Z. -/
theorem rowsRead_of_four {Z : VerifierAndGoals.PublicFiles} {p : OnBytes.Model.Verify.Planned}
    {ls : Array OnBytes.Model.Stages.LinkH} {shapes : Shapes} {R : List SendRow}
    (hp : OnBytes.Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p)
    (hs : OnBytes.Model.Verify.shapesOf p.X (some Z.lay) = .ok (ls, shapes))
    (e1 : freeOf p.chains.made = writtenMade)
    (e2 : shapes.sub.openRows = List.replicate 25 1) (e3 : shapes.sub.pendingRows = 13)
    (e4 : ∀ j, j < 26 → armOf p.X j = armAtW j) (hR : rowsW = .ok R)
    (hc : P5T.radOneB ((P5T.firstRows R).flatMap (·.sampled)) = true) : P5J.rowsRead Z := by
  refine P5J.rowsRead_iff.2 ⟨R, ?_, hc⟩
  rw [sendRowsOf_of hp hs, e2, e3,
    rowsFrom_four (c := p.chains.made) (c' := writtenMade.at Hung.none) (congrArg Free.sized e1)
      (congrArg Free.key e1) (congrArg Free.proof e1) (congrArg Free.entry e1), ← hR]
  unfold rowsW
  exact rowsFrom_congr _ _ _ fun j hj => e4 j (by
    have := groups_W
    exact this ▸ hj)

end TocR

#print axioms TocR.returns_of_B
#print axioms TocR.rowsRead_of_four
