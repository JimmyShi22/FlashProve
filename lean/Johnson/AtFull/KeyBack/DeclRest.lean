-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/DeclRest.lean: of the key file's written declared rounds at the full size,
only rounds that draw positions open anything.

  `restOk r`: r draws positions, or it opens neither a stored table nor a tree.
  `recs_rest`: so it is at each of the distinct written declared rounds (`declRecsFull`,
    Johnson/HB/LLHARD/KB8/Written.lean). A closed fact, by an evaluation in Lean's kernel (`decide
    +kernel`).
  `decl_rest0`, `decl_rest1`, `decl_rest2`: so it is at every round of the three lists, by
    `all_of_recs` (Johnson/G/Runs.lean).

Limits. A fact on a written file. That the written declared rounds are what any routine returns at
any public files is not said. Nothing on soundness, nothing on hiding.

-/
import Johnson.HB.LLHARD.KB8.Written
import Johnson.G.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Johnson.KB8 (declKeyFull declRecsFull)
open Johnson.G (dryKeyRunsFull0 dryKeyRunsFull1 dryKeyRunsFull2)
open Johnson.G.Runs (all_of_recs)

/-- A declared round draws positions, or opens neither a stored table nor a tree. -/
def restOk (r : Fmt.DeclaredRound) : Bool :=
  Fmt.kindOf r.entry.name == some .positions || (r.stored.isEmpty && r.opens.isEmpty)

/-- So it is at each of the distinct written declared rounds. -/
theorem recs_rest : declRecsFull.all restOk = true := by decide +kernel

/-- So it is at every round of the first chain's list. -/
theorem decl_rest0 : declKeyFull.1.all restOk = true := all_of_recs dryKeyRunsFull0 recs_rest

/-- The like for the shared chain. -/
theorem decl_rest1 : declKeyFull.2.1.all restOk = true := all_of_recs dryKeyRunsFull1 recs_rest

/-- The like for the second chain. -/
theorem decl_rest2 : declKeyFull.2.2.all restOk = true := all_of_recs dryKeyRunsFull2 recs_rest

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.recs_rest
#print axioms Johnson.AtFull.KeyBack.decl_rest0
#print axioms Johnson.AtFull.KeyBack.decl_rest1
#print axioms Johnson.AtFull.KeyBack.decl_rest2
