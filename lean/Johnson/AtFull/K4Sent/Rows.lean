-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/K4Sent/Rows.lean: at the written values K4's lot lays twelve pairs, and their plain
fields are those of the twelve rows at K4's places in the written table of the first chain's
sub-protocols. By Lean's kernel.

What it says.
  `views_written`  the twin `k4FromSk` (Johnson/Road/K4/K4FromSk.lean) at the written table of
                   steps, the written entries, twelve groups and the scope's skeleton gives
                   twelve views, and each passes `viewOkB`: its Bool is true; its name is
                   "G‹g›:3"; its link is 2 g; its piece is 3; and row number 28 g + 4 of
                   `cutFirstFull` (Johnson/Desc/Ok/PlanWritten/CutLit.lean) is: that name ·
                   chain 1, that link, that piece, K4 · 170 rounds at g = 0, 168 else, twice ·
                   no told round · the view's `before`.
  `views_oneRootMore_no`  a negative test: with one root more at round number 2, which lies in no
                   window: there are twelve views still, the Bool of each is true, the first
                   group's view passes `viewOkB`, and not all do: the numbering in `before` is
                   held against the written table.

Limits. Closed facts on written values of one set of public files, with synthetic weights. That any
public part has these values is shown nowhere here. Nothing on soundness.
-/
import Johnson.Road.K4.K4FromSk
import Johnson.AtFull.K4Sent.Written
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K4Sent

open OnBytes.Road.K4 (k4FromSk skW)
open Johnson.AtFull.Cut (cutWritten)
open VerifiableInference.PlanWritten (cutFirstFull sameRow)

/-- How many rounds K4 has at group g, at the full size. -/
def roundsW (g : Nat) : Nat := if g == 0 then 170 else 168

/-- A view is the written table's row at K4's place of its group. -/
def viewOkB (v : Bool × String × Nat × Nat × List (Nat × Nat) × Nat) : Bool :=
  v.1 && decide (v.2.1 = "G" ++ toString v.2.2.2.2.2 ++ ":3") &&
    decide (v.2.2.1 = 2 * v.2.2.2.2.2) && decide (v.2.2.2.1 = 3) &&
    (cutFirstFull[28 * v.2.2.2.2.2 + 4]?).any fun r =>
      sameRow r (v.2.1, ⟨1, some v.2.2.1, v.2.2.2.1, .K4⟩, roundsW v.2.2.2.2.2,
        roundsW v.2.2.2.2.2, [], v.2.2.2.2.1)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At the written values: twelve views, each the written table's row.** -/
theorem views_written :
    (decide ((k4FromSk cutWritten esWritten 12 skW 0 none).length = 12) &&
      (k4FromSk cutWritten esWritten 12 skW 0 none).all viewOkB) = true := by
  decide +kernel

/-- The entries with one root more at round number i. -/
def bumpAt (i : Nat) (es : List Fmt.Entry) : List Fmt.Entry :=
  es.zipIdx.map fun x => if x.2 == i then { x.1 with roots := x.1.roots + 1 } else x.1

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A negative test: one root more at round number 2: twelve views, each Bool true, the first
group's view passes, and not all pass. -/
theorem views_oneRootMore_no :
    (fun V : List (Bool × String × Nat × Nat × List (Nat × Nat) × Nat) =>
      decide (V.length = 12) && V.all (·.1) && V.head?.any viewOkB && !V.all viewOkB)
      (k4FromSk cutWritten (bumpAt 2 esWritten) 12 skW 0 none) = true := by
  decide +kernel

#print axioms Johnson.AtFull.K4Sent.views_written
#print axioms Johnson.AtFull.K4Sent.views_oneRootMore_no

end Johnson.AtFull.K4Sent
