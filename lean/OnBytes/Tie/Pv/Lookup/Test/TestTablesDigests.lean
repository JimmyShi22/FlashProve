-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Test/TestTablesDigests.lean.
A test file: the four digests of public tables that stand as lines in the full-size example's
parameter file (tsilu, tsig, trope, texp: eight 32-bit words each) are the digests of the arrays of
OnBytes/Tie/Pv/Lookup/Test/TestTablesOfModel.lean; of the four in the small example's file, three
are (not trope: its rotary table is another). TestTablesOfModel.lean holds these arrays, entry by
entry, against the numbers that the theorems' integer model stores: SILU, the rotary table and the
exponentials whole; of table FS (65,536 entries) the lower half alone: its upper half is the gate's
clamp, which is none of the model's five table functions. The digest tsig covers all of table FS.

Runs, no theorem. A line `#guard` is evaluated by Lean's interpreter when this file compiles, and
the compilation fails if the value is not true. The kernel has no part in it.

What is run. `publicOf` (OnBytes/Model/VerifyPublic.lean), with no layout file, on the bytes made of
`policyF`, `scalesF` and of `policyS`, `scalesS` (OnBytes/Tie/Pv/Plan/PlanKits.lean). For each of
the four tables (`PublicTable`, OnBytes/Model/Config.lean): whether the digest that the parameter
file gives (`PolScan.tableExpected`) is there and is `tableDigest` of the words of `gate.1`,
`gate.2`, `rope` and `expTable 12 8`. The words are laid as `tableHeld` lays them.

What comes out. At the full-size example: four times yes. At the small example: yes for SILU, table
FS and the exponentials; no for the rotary table, which is another there. Two controls: that no; and
at the full-size example, with the first word of each array raised by one, four times no. The file
compiles in about two minutes on a loaded machine.

Why it is more than `publicOf`'s yes. The program compares each digest with its own table on its way
and refuses where they part (`tableHeld`), but where a file has no such lines it compares nothing.
Here the lines must be there.

Limits. Equal digests are all that is held, under the hash of OnBytes/Hash/SecondHashFunction.lean as a fixed
function: two tables with one digest are not ruled out by a run. The lookups are not hereby shown.
The two examples are the repository's folders prover/examples/target_full_f2 and
prover/examples/target_small_f2 (sha256: policy.txt 3c7ff5cb…, KL.bin f8829d72…; these are not the
files of the stored example examples/accepted-proof/), as PlanKits.lean has them written out: no
Lean code compares them with a file on a disk. Nothing on the tables that the C++ programs compute
in floating point. This file is not part of the compiled program.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Test.TestTablesOfModel
import OnBytes.Model.VerifyPublic
import OnBytes.Tie.Pv.Plan.PlanKits

set_option autoImplicit false

namespace Fo.TablesOfModel

open OnBytes.Tie.Pv.Plan (textOf wordsFile policyF scalesF policyS scalesS)
open OnBytes.Model (PublicTable tableDigest)

/-- The digest of a table that is given as an array of words, laid as tableHeld lays them. -/
def digestOf (a : Array Nat) : ByteArray :=
  tableDigest (a.foldl (fun b x => b ++ OnBytes.word32 x) ByteArray.empty)

/-- The array with its first word raised by one. -/
def bent (a : Array Nat) : Array Nat := a.modify 0 (· + 1)

/-- The four tables with the arrays of TestTablesOfModel.lean, each through f. -/
def fourArrays (f : Array Nat → Array Nat) : List (PublicTable × Array Nat) :=
  [(.silu, f gate.1), (.sigmoid, f gate.2), (.rope, f rope),
   (.exp, f ((OnBytes.Attention.expTable 12 8).getD #[]))]

/-- For each of the four: is the file's digest there, and is it the array's. Nothing where the
program's public part refuses. -/
def digestsAt (pol KL : ByteArray) (f : Array Nat → Array Nat) : Option (List Bool) :=
  match OnBytes.Model.Verify.publicOf pol KL none with
  | .error _ => none
  | .ok X => some ((fourArrays f).map fun x => X.P.tableExpected x.1 == some (digestOf x.2))

/-! ## The full-size example -/

#guard digestsAt (textOf policyF) (wordsFile scalesF) id == some [true, true, true, true]
/- the control: each array's first word raised by one -/
#guard digestsAt (textOf policyF) (wordsFile scalesF) bent == some [false, false, false, false]

/-! ## The small example -/

#guard digestsAt (textOf policyS) (wordsFile scalesS) id == some [true, true, false, true]

end Fo.TablesOfModel
