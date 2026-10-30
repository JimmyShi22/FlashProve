-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestNotCovered.lean: a chain of a key file that the theorems of this directory do not
cover.

A key file has three chains: one-time, shared, second. The test, made when the file compiles,
evaluates the limits on the program's own description of the shared chain, at the C++ programs'
public files for the test key. It breaks three limits: one round sends two roots, one tree is opened
twice, and it opens a stored table. The guard shows the limits' names. Which trees are meant is read
off docs/format/FORMAT.md (R13.19, R14.9).

Not tested here, because their descriptions are made from what was read of earlier chains: the three
chains of a proof file, and the chain named second, which opens trees that it has taken over. A
proof's first chain sends two roots in one round (it also sends two trees that it never opens, which
the limits allow). The test shows what is so at these files and parameters, and nothing beyond
them.
-/
import OnBytes.Tie.StoredMain
import OnBytes.Tie.TestKeyOneTime

set_option autoImplicit false

namespace OnBytes.Tie

/-- The program's description of the shared chain. Its statement holds a second root beside the
table's, that of the binding tree (docs/format/FORMAT.md, R13.6; the tree is R7.18's). Here 32
zero bytes stand for it. No limit looks at them. -/
def testShared : Option Fmt.SpecX :=
  testKey.bind fun k =>
    let p := Key.tailPublic k testTable
    (tableKey p.shared.given.plan.field p.shared.given.cfg p.lin.fold.index testTable 0).bind
      fun key => ((Proof.sharedBlock p.lin key).dryRun (Proof.sharedStart p)).bind fun x =>
        p.shared.describe p.lab₂ testTable Fmt.zero32 x.1

#guard testShared.any fun S =>
  S.ok && limitsOfX S == [.severalRoots, .notOnce, .storedTable] && !withinX S

end OnBytes.Tie
