-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/RefusalNames.lean: every name under which a function of this directory refuses.

A refusal's name is one of a fixed list. It holds nothing that was read from a file. The reader of
the parameter file joins the name of a test to the name of the line at which it failed; both come
from fixed lists, so all such names are listed here. The list is written by hand: no theorem says
that it is complete. It pairs each test on a line's form with each line, also where the pair
cannot occur, as in "parameter-line-values: stages link" (a line `stages` may have any number of
values). The readers of this directory that return an `Option` refuse without a name. A name that a
caller's routine throws (`Subproofs.plan`) is handed on as it is and is not listed here. The callers
of `readLines` below the program's root rename that reader's names before they are printed.

Main definitions: `lineHeads`, `names`.
-/
import OnBytes.Params.Planner

namespace OnBytes.Params

/-- The names of the eight groups of the parameter file. -/
def groupNames : List String :=
  ["link", "folded", "omega", "own", "once-folded", "once-omega", "once-own", "once-ranges"]

/-- The names of the lines whose numbers have a range: those with one number, and the five with
three numbers of bits of work. -/
def rangedHeads : List String :=
  ["sec", "reading", "rowcost", "slots", "answers", "record", "work field", "work sample",
   "work closeness", "work positions", "work smallness", "salt", "listed", "ranges-part"]

/-- The names of the 32 lines of the parameter file's frame. The order is not the file's:
`ranges-part` comes before the groups here. -/
def lineHeads : List String :=
  ["version"] ++ rangedHeads ++ groupNames.flatMap (fun g => ["group " ++ g, "stages " ++ g]) ++
    ["table"]

/-- Every name under which a function of this directory refuses. -/
def names : List String :=
  ["parameter-line-missing: ", "parameter-line-order: ", "parameter-line-blanks: ",
   "parameter-line-values: "].flatMap (fun t => lineHeads.map (t ++ ·)) ++
  rangedHeads.map ("parameter-range: " ++ ·) ++
  ["parameter-group-shape: ", "parameter-stages-count: ", "parameter-stages-shape: "].flatMap
    (fun t => groupNames.map (t ++ ·)) ++
  ["parameter-number-spelling", "parameter-own-code", "parameter-one-mask-code",
   "parameter-table-shape", "version-of-an-earlier-format", "version-of-another-field",
   "version-of-another-hash", "version-unknown", notAdmitted, "plan-tau", "security-bits"]

end OnBytes.Params
