-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CsW.lean: `csW` computes the two tables of the oracle message that
an honest prover sends at a code switch, at `Fld.two`, as `csFast` (Fast.lean) does, with the
operations on elements computed on 64-bit words alone. Definitions only. Imports Fast.lean and
HalveW.lean, and no Mathlib.

Each definition repeats a text that stands, at `Fld.two`:
- `foldVW` repeats `foldV` (Fmt/M1Types.lean), with `foldLowW` (HalveW.lean) in the place of
  `foldLow`.
- `foldRowsW` repeats `foldRowsA` (Fast.lean), with `foldVW` in the place of `foldV`.
- `csW` repeats `csFast` (Fast.lean) line by line, with `foldRowsW` in the six places of
  `foldRowsA`.
CsWLaw.lean proves each equal to its original at `Fld.two`, as functions, for all arguments and
without hypothesis.

Limits. A second text, for speed. `Seams.fast` (FastW.lean) calls `csW`. Theorems on a run are
stated at the originals and are carried over by the equations. It computes with random values too
(the rows' tails, the free entries, the pad) and keeps its originals' defaults, without a warning:
`foldRowsW` reads a missing entry of a row or a tail as 0, and `csW` fills the list of free entries
with 0 or cuts it. No test file calls `csW` by name; the tests that run `runBy` at `Seams.fast`
(RunManyToy.lean, JobSharedToy.lean) evaluate it. At `Fld.two` only. Nothing is measured here.
Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Fast
import Johnson.Desc.ProofFile.Honest.K12.HalveW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Stage fitL ent)

/-- `foldV` on 64-bit words alone: a vector of 2 ^ |g| entries folded to one element. -/
def foldVW (g : List E) (v : Array E) : E := ent (foldLowW g v) 0

/-- `foldRowsA` on 64-bit words alone: rows of n entries folded entry by entry at g. -/
def foldRowsW (g : List E) (rows : List (List E)) (n : Nat) : List E :=
  let A : List (Array E) := rows.map List.toArray
  (List.range n).map fun j => foldVW g (A.map fun r => r.getD j Fld.zeroE).toArray

/-- **`csFast` on 64-bit words alone**: the main table and the mask table of the oracle message that
a code switch sends. The arguments are those of `csOwnG`, without the field. -/
def csW (old new : Stage) (g : List E) (M Rh W Sg P Pi : List (List E)) (free : List E) (pad : E) :
    Array E × Array E :=
  let g' := g.take old.h
  let rest := foldRowsW g' W old.Z.l ++ foldRowsW g' P old.Z.l ++ foldRowsW g Rh old.C.r ++
    foldRowsW g' Sg old.Z.r ++ foldRowsW g' Pi old.Z.r
  ((foldRowsW g M old.C.l).toArray,
    (rest ++ fitL Fld.zeroE (2 ^ new.h * new.Z.l - rest.length - 1) free ++ [pad]).toArray)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.foldVW
#print axioms ProofFile.Honest.K12.Light.foldRowsW
#print axioms ProofFile.Honest.K12.Light.csW
