-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/MaxRt.lean: the greatest number of Merkle roots in one query of a chain. One definition.

`maxRt` is read by one definition, `Compile.Batch.takeRts` (Compile/Batch/Verifier.lean): the step
that takes the roots of a component of a round (Iop/Batch.lean) with a list of Merkle trees from a
proof string. A component with more than `maxRt` trees is refused (`takeRts_succ_maxRt` at
`maxRt` + 1; in general `length_of_takeRts`). The roots
of such a component are meant for one query: a Fiat-Shamir query or, for a slot's component in the
joining round, the query to g (Compile/Batch/Oracles.lean). No verifier of this library calls
`takeRts`: a component has at most one tree (`has0`, `hasJ`, Iop/BatchWire.lean), a query has one
field for its root (`FbIn.rt`, `JoiningRoundQuery.rt`), and `recomputeChain` takes it with `takeRt`.

Main names: `maxRt`.

Why 2: the programs' byte format may send two roots in one query. And it is the most that the bound
on the hash events can bear as it is stated (`hashEvents`, Compile/Batch/Hash.lean: at most
2 t² / 2^lam). That bound is proved from at most 3 root fields in a query, one of them the
component's root, which gives 3 t² / 2. With two roots they are 4, which gives 2 t²; with three the
statement would not follow so.

Limits: the number is a limit of the step `takeRts`, not of the programs' byte format. The
format has no such cap: its only limit is 2^16 trees in a chain. No shipped setting sends more than
two roots in a round. So a proof in the format with three roots in one hash call would be refused
by that step though the format allows it.
Not claimed: that `hashEvents` holds with two roots in a query: a query holds at most one root
(`FbIn.rt`, `JoiningRoundQuery.rt`, Compile/Batch/Oracles.lean). No wire record reads the number: a law of the
wire (Iop/BatchWire.lean) that a component has at most `maxRt` trees is not stated. The second form
of the compiler's verifier side has a number of the same name and value of its own
(`TypedOracleCompiler.Iop.maxRt`, OnBytes/TypedOracleCompiler/Iop/BatchWire.lean), which its plans do read: nothing here
speaks of it.

Terms: lean/GLOSSARY.md.

-/
import Iop.Shape

namespace Iop

/-- at most so many trees for a component of a round, and so many roots in one query -/
def maxRt : ℕ := 2

end Iop
