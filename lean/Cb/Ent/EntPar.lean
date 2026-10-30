-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Ent/EntPar.lean: the number `roomX`, the exceptional seeds of a sample, and witnesses for the
counts of an entry's chain, as records of natural numbers.

An entry's chain compares two stored tables: the link's five rounds, a bridge, then a proximity test
in stages.

The witnesses are for the counts of the theorem on codes that is taken as given (`CntW`,
Cb/Ent/EntCnt.lean). q is the number of elements of the field `Cb.Gl.E`.



The samples are taken
to have a point of c coordinates and a factor other than 0: `clash c` exceptional seeds among
`seeds c`.

Main names:



  `StW`, `Wit`: witnesses for the counts: two for each stage (main rows, mask rows), one for the
    tables.




  `roomX`: the number 2^128 + 2^119.
















Limits: not that any link, closing or tower has these numbers: that is `LinkN.Is`
(Cb/Ent/EntKappaN.lean), a hypothesis where it is used. Not that these are a program's or a file's
sizes.
That the counts bound anything is the theorem on codes,
taken as given, which is neither used nor stated here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ent.EntCnt
import Cb.Ent.EntKappaN
import Cb.Ld.LdBldCode
import Cb.Gen.JohnsonList

set_option autoImplicit false

namespace Cb.Ent
open Cb.Gl.Ref

/-- The number X = 2^128 · (1 + 2^-9). The bound 1 / X is a
little below 2^-128 (what for: the head of Cb/Ent/EntKappaX.lean). -/
def roomX : ℕ := 2 ^ 128 + 2 ^ 119

/-- The exceptional seeds of a sample whose seed is a point of c coordinates and a factor other than
0. -/
def clash (c : ℕ) : ℕ := max (c * q ^ (c - 1) * (q - 1)) (q ^ c)
/-- The number of such seeds. -/
def seeds (c : ℕ) : ℕ := q ^ c * (q - 1)

/-- One stage's witnesses: for the count of its main rows' code and for that of its mask rows' code,
repeated to the main rows' length. -/
structure StW where
  main : CntW
  mask : CntW

/-- All witnesses of a chain. -/
structure Wit where
  /-- the tables' code, at the one radius of both folds' tests -/
  tab : CntW
  /-- the stages that fold -/
  st : List StW
  /-- the last stage -/
  fin : StW

end Cb.Ent
