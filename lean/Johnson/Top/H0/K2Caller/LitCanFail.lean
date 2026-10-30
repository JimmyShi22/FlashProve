-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LitCanFail.lean: the test of Row.lean can fail at the written records of the
small example: at each of the 5 it says no if the group's k is one more, if the radius is one less,
if the first sample's cube is one more, if the joint radius and every radius in front are the main
code's length, if every radius in front alone is that length. Evaluations in Lean's kernel, a
theorem for each record.
  altered: five altered records of a record
  small_can_fail: the test says no at each
A file of controls: LitCanFailFull.lean alone imports it.
Limits: written numbers; five alterations. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.LitRows

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Lean checks this file's theorems one after another, not side by side: as measured, the peak of
-- memory is then lower and steadier.
set_option Elab.async false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params Johnson.G

/-- Five altered records of a record. -/
def altered (r : SwRow) : List SwRow :=
  [{ r with g := { r.g with k := r.g.k + 1 } }, { r with rad := r.rad - 1 },
    { r with o := r.o.modifyHead fun x => { x with cubeBits := x.cubeBits + 1 } },
    { r with rad := 2 ^ r.g.main.logN, lo := r.lo.map fun x => (x.1, 2 ^ r.g.main.logN) },
    { r with lo := r.lo.map fun x => (x.1, 2 ^ r.g.main.logN) }]

set_option maxRecDepth 1000000 in
theorem small0_fails : ((altered (smallAt 0)).all fun x => !x.ok) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small1_fails : ((altered (smallAt 1)).all fun x => !x.ok) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small2_fails : ((altered (smallAt 2)).all fun x => !x.ok) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small3_fails : ((altered (smallAt 3)).all fun x => !x.ok) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small4_fails : ((altered (smallAt 4)).all fun x => !x.ok) = true := by decide +kernel

/-- The test can fail. -/
theorem small_can_fail : (tableSmallLit.all fun r => (altered r).all fun x => !x.ok) = true :=
  small_all _ small0_fails small1_fails small2_fails small3_fails small4_fails

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.small_can_fail
