-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestStored.lean: tests of the limits for chains that open stored tables.

Each test is evaluated when the file compiles. The description is the one that Entry.read makes of
the entry file's chain at the toy of OnBytes/Entry/RecordToyFiles.lean
(OnBytes/Entry/TestRecordToyDeclared.lean), on whose files Entry.check is run
(OnBytes/Entry/TestRecordToy.lean). The tests show that it meets the limits of
OnBytes/Tie/StoredMain.lean and that two of them are noticed where they are broken: no random bytes,
and a table opened twice. The last tests join that toy's stored parameter bytes and public files to
the planner: what OnBytes/Plan/ToyShapes.lean derives from the public files that
OnBytes/Plan/TestKeyOneTime.lean spells out are these bytes. The six limits on the tables are not
tested one by one in this library. The tests show what is so at this description, and nothing beyond
it.
-/
import OnBytes.Tie.StoredMain
import OnBytes.Entry.TestRecordToyDeclared
import OnBytes.Plan.TestToyShapes

set_option autoImplicit false

namespace OnBytes.Tie
open OnBytes.Entry.RecordToy (linkSpec publicFileOne publicFileTwo oneTimeParameters
  sharedParameters secondParameters entryParameters)

-- The entry file's chain at the toy's parameters is covered.
#guard linkSpec.map withinX == some true
-- The same chain with its random bytes given by the description is covered too.
#guard (linkSpec.map fun S => withinX { S with base := { S.base with rand := .given Fmt.zero32 } })
  == some true
-- Without random bytes it is not covered.
#guard (linkSpec.map fun S => withinX { S with base := { S.base with rand := .none } }) ==
  some false
-- A table that is opened twice is not covered. Here both parts of the draws go to the first table.
-- The library's own limits still hold, so it is the clause "at most once" that says no.
#guard (linkSpec.map fun S =>
  let S' : Fmt.SpecX := { S with stored := S.stored.map (·.map fun t => { t with item := 0 }) }
  ((xdOf S' fun _ _ => ByteArray.empty).ok, withinX S')) == some (true, false)

-- The toy's two public files are those that OnBytes/Plan/TestKeyOneTime.lean spells out.
#guard publicFileOne == Params.TestFile.fileOf Plan.TestKeyOneTime.toyFile
#guard publicFileTwo == Plan.TestKeyOneTime.toyShapes.toUTF8
-- The parameter bytes of the four chains, as the planner derives them from these files, are the
-- toy's stored ones, byte for byte.
#guard ((Plan.toyConfigure Plan.toyShapes (Params.TestFile.fileOf Plan.TestKeyOneTime.toyFile)
    Plan.TestKeyOneTime.toyShapes.toUTF8).toOption.map fun c =>
  (c.keyOneTime == oneTimeParameters, c.keyShared == sharedParameters,
    c.keySecond == secondParameters, c.entryLink == entryParameters)) ==
  some (true, true, true, true)

end OnBytes.Tie
