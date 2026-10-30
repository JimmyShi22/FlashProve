-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/TestOpened.lean: tests of OnBytes/Chain/Opened.lean. No program imports this file.

The example is the made-up chain of Fmt/Rules8X.lean. Its first round draws the positions
0, 1, 3, 1, 1 and gives the first two to one stored tree and the other three to a second one.
Its second round opens nothing.
-/
import OnBytes.Chain.Opened
import Fmt.Rules8XFast

namespace OnBytes.TestOpened

open Fmt.ToyX8

/-- The example's opened columns by place. -/
def cut : Option (Array (Array Opening)) :=
  (Fmt.wholeChainXF spec honest).bind fun o => openedByPlace spec (Fmt.viewX spec o)

-- the positions, by round and opening
#guard cut.map (fun a => a.toList.map fun r => r.toList.map fun o => o.map (·.1)) ==
  some [[[0, 1], [1, 3]], []]

-- the columns are those of the view, in its order
#guard cut.map (fun a => a.toList.flatMap fun r => r.toList.flatMap fun o => o.map (·.2)) ==
  (Fmt.wholeChainXF spec honest).map fun o => (Fmt.viewX spec o).opened.map (·.2.2)

-- position 1 is in both openings; position 3 in the second alone
#guard (cut.bind fun a => openingAt a 0 0).any fun o => (o.column 1).isSome && (o.column 3).isNone
#guard (cut.bind fun a => openingAt a 0 1).any fun o => (o.column 1).isSome && (o.column 3).isSome
#guard (cut.bind fun a => openingAt a 0 2).isNone && (cut.bind fun a => openingAt a 2 0).isNone

-- a view with a column too few or too many is no view of this description
#guard ((Fmt.wholeChainXF spec honest).bind fun o =>
  openedByPlace spec { Fmt.viewX spec o with opened := (Fmt.viewX spec o).opened.drop 1 }).isNone
#guard ((Fmt.wholeChainXF spec honest).bind fun o =>
  openedByPlace spec { Fmt.viewX spec o with
    opened := (Fmt.viewX spec o).opened ++ [(0, 0, [])] }).isNone

end OnBytes.TestOpened
