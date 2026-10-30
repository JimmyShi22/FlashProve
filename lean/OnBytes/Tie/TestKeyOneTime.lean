-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestKeyOneTime.lean: the program's own description of the test key's one-time chain
breaks no limit.

The tests, made when the file compiles, evaluate the limits of OnBytes/Tie/Limits.lean on the
description that the program itself makes of a key file's one-time chain, at the public files of
the toy key of the C++ tool blocks/frame/handover_files.cpp (OnBytes/Plan/TestKeyOneTime.lean). The
chain sends trees that it never opens, which the limits allow. So the condition on the limits in
`key_check_oneTime` (OnBytes/Tie/KeyFile.lean) holds at these parameters and at a table of this
shape. The test key is made-up test data, no model's key. That `Key.check` says yes on some file
under these parameters is not tested in this directory. The tests show what is so at these files
and parameters, and nothing beyond them.

Main definitions: `testKey`, `testTable`, `testOneTime`.
-/
import OnBytes.Key.File
import OnBytes.Plan.ToyShapes
import OnBytes.Tie.Limits
import OnBytes.Plan.TestKeyOneTime

set_option autoImplicit false

namespace OnBytes.Tie

/-- The parameter bytes of the test key's three chains, read. -/
def testKey : Option Params.KeyChains :=
  (Plan.toyForCommitters (Params.TestFile.fileOf Plan.TestKeyOneTime.toyFile)
    Plan.TestKeyOneTime.toyShapes.toUTF8 128).toOption.bind fun c =>
    Params.KeyChains.read c.keyOneTime c.keyShared c.keySecond

/-- A table of the test key's shape: 32 zero bytes for its root, and as many zero answers as the
record asks. No limit looks at their values. -/
def testTable : Params.TableName :=
  let n := (testKey.map fun k =>
    k.oneTime.lin.fold.index.rows * k.oneTime.lin.fold.index.answers).getD 0
  ⟨Fmt.zero32, List.replicate n (E.mk3 0 0 0)⟩

/-- The program's description of the one-time chain. -/
def testOneTime : Option Fmt.SpecX :=
  testKey.bind fun k =>
    ((Key.oneTime k.oneTime).dryRun (Key.startOf k.oneTime)).bind fun x =>
      k.oneTime.describe testTable x.1

-- The table has an admitted form (`Key.tableOk`).
#guard testKey.any fun k => Key.tableOk k.oneTime.lin.fold.index k.oneTime.given.cfg testTable
-- The description is in order and breaks no limit.
#guard testOneTime.any fun S => S.ok && limitsOfX S == []
-- It sends five trees and never opens the first and the last.
#guard testOneTime.any fun S => (S.base.rounds.map (·.entry.roots)).sum == 5 &&
  (List.range 5).map (fun n =>
    ((opensOf S.base).filter fun o => ownNumber o == some n).length) == [0, 1, 1, 1, 0]
-- So the test `eachOnce` says no of it.
#guard testOneTime.any fun S => !eachOnce S.base

end OnBytes.Tie
