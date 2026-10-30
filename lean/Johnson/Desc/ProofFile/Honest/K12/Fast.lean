-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Fast.lean: three functions of Fmt/ on rows, with each row read as
an array. Definitions only. Imports Halve.lean alone, and no Mathlib.

Each definition is a copy of an original in Fmt/:
- `tabFast` of `tabOf` (Fmt/M1Own.lean): rows of n entries as one table.
- `foldRowsA` of `foldRows` (Fmt/M1Cs.lean): rows folded entry by entry.
- `csFast` of `csOwnG` (Fmt/M1Cs.lean): the two tables of the oracle message that an honest prover
  sends at a code switch. It is `csOwnG` copied line by line, with `foldRowsA` in the six places of
  `foldRows`.
`Seams.fast` (FastW.lean) takes `tabFast`, and `csFast` at `Fld.one`.

By what. The originals read entry j of a row with `List.getD`, which walks j steps down the list, so
a row of n entries costs about n ^ 2 / 2 steps. Here each row is converted to an array once, and an
array is indexed in one step. The same entries go, in the same order, through the same calls of
`foldV` and `fitL`.

Each copy equals its original as a function, for all arguments and without hypothesis:
`tabFast_eq`, `foldRowsA_eq`, `csFast_eq` (FastLaw.lean).

Limits. The costs are counted by reading the code, not measured. Nothing on completeness, soundness
or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Halve

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Stage foldV fitL)

/-- Rows of n entries as one table: entry c of row b is at index b + (number of rows) * c. A row
that is too short counts as filled up with 0. -/
def tabFast (rows : List (List E)) (n : Nat) : Array E :=
  let A : Array (Array E) := (rows.map List.toArray).toArray
  Array.ofFn (n := rows.length * n) fun i =>
    (A.getD (i.val % rows.length) #[]).getD (i.val / rows.length) Fld.zeroE

/-- Rows of n entries folded entry by entry at g. -/
def foldRowsA (f : Fld) (g : List E) (rows : List (List E)) (n : Nat) : List E :=
  let A : List (Array E) := rows.map List.toArray
  (List.range n).map fun j => foldV f g (A.map fun r => r.getD j Fld.zeroE).toArray

/-- The main table and the mask table of the oracle message that a code switch sends. The arguments
are those of `csOwnG`. -/
def csFast (f : Fld) (old new : Stage) (g : List E) (M Rh W Sg P Pi : List (List E))
    (free : List E) (pad : E) : Array E × Array E :=
  let g' := g.take old.h
  let rest := foldRowsA f g' W old.Z.l ++ foldRowsA f g' P old.Z.l ++ foldRowsA f g Rh old.C.r ++
    foldRowsA f g' Sg old.Z.r ++ foldRowsA f g' Pi old.Z.r
  ((foldRowsA f g M old.C.l).toArray,
    (rest ++ fitL Fld.zeroE (2 ^ new.h * new.Z.l - rest.length - 1) free ++ [pad]).toArray)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.tabFast
#print axioms ProofFile.Honest.K12.Light.foldRowsA
#print axioms ProofFile.Honest.K12.Light.csFast
