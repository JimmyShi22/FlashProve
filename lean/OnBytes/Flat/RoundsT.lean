-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/RoundsT.lean: a written round that may send the roots of several trees, beside the
written round with at most one tree.

The rounds of a file's chains are those of OnBytes/Maker/Trees.lean (`roundT`, `uLT`): a round's
data (`RDT`) has a list of trees. The readings of a written round in OnBytes/Slice/ (`wRound`,
`valsOf`, `chalTo`, `chalTo_fib`, `SendsDraws`, `ansOf`) are stated for a round's data with at most
one tree (`PQ.RD`, Run/PlanQTypes.lean). The two rounds differ in the prover's oracles alone.
Definitions and two equalities by unfolding.

Main names:
  `toRD d`: the entry, the kind, the items and the openings of d, with the first tree of d if
    there is one.
  `wT d`: the written round of d, as a round of the library.
  `chal_eq`, `plain_eq`: its verifier messages and the plain part of its prover messages are
    those of `wRound (toRD d)`. So `chalTo (toRD d) g` and `valsOf (toRD d) c` are typed on the
    messages of `wT d`.
  `msgRD d m`: the plain part of m, as a prover message of `wRound (toRD d)`, with that round's
    fixed oracle.

Limits: `toRD d` keeps one tree of several: whatever reads the tree of `toRD d` does not see the
others. `msgRD` drops the oracles.

-/
import OnBytes.Maker.Trees
import OnBytes.Slice.Draws

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Run OnBytes.Maker OnBytes.Slice

/-- A round's data with a list of trees, as a round's data with at most one. -/
@[reducible] def toRD (d : RDT) : PQ.RD := ⟨d.entry, d.kind, d.items, d.trees.head?, d.opens⟩

/-- The written round of d, as a round of the library. -/
abbrev wT (d : RDT) : Round := (roundT (ckP .two) d).up

theorem chal_eq (d : RDT) : (wT d).Chal = (wRound (toRD d)).Chal := rfl

theorem plain_eq (d : RDT) : (wT d).Plain = (wRound (toRD d)).Plain := rfl

/-- The plain part of a prover message. -/
def msgRD (d : RDT) (m : (wT d).Msg) : (wRound (toRD d)).Msg := ((wRound (toRD d)).dOrc, m.2)

end OnBytes.Flat
