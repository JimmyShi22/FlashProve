-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Test/TestTablesAtFiles.lean.
A test file: that the arguments at which OnBytes/Tie/Pv/Lookup/Test/TestTablesOfModel.lean makes the
Lean verifier program's four tables are those that the program itself has at the full-size
example's public files, as this library has them written out, and that the arrays which the
program's own public part then holds are the arrays guarded there; and at the small example's files
the same for three of the four tables: its rotary table is another.

Runs, no theorem. A line `#guard` is evaluated by Lean's interpreter when this file compiles, and
the compilation fails if the value is not true. The kernel has no part in it.

What is run. `publicOf` (OnBytes/Model/VerifyPublic.lean), with no layout file, on the bytes made of
`policyF`, `scalesF` and of `policyS`, `scalesS` (OnBytes/Tie/Pv/Plan/PlanKits.lean). Of what it
returns: the layers' shape's eg, smax (neither parameter file has a line eg or smax: 8 and 4095 are
what the program's reader takes where the lines are absent: `EG`, `SMAX`,
OnBytes/Model/Config.lean), routed experts, gate's clamp; cs, theta0, dh, lt; the pairs (S, rx) of
the attention plans, each once; whether its table SILU, its table FS and its rotary table are
`gate.1`, `gate.2`, `rope` of TestTablesOfModel.lean, as whole arrays; whether every attention
plan's table of exponentials is `expTable 12 8`.

What comes out. At the full-size example: the arguments of TestTablesOfModel.lean, and four times
yes. At the small example: the same eg, smax, routed experts, gate's clamp, S and rx, and yes for
SILU, FS and the exponentials; another theta0 and lt, and no for the rotary table: that no is also
the control of the comparison of arrays: a thin one: the two tables differ in length (8,192 words
against 131,072), and no control here shows a no between arrays of one length. The list of pairs (S,
rx) is [(12, 8)], not empty, at both examples: so "every attention plan" is not said of no plan.

Limits. Equal arguments and equal arrays are all that is held: the lookups are not hereby shown. The
two examples are the repository's folders prover/examples/target_full_f2 and
prover/examples/target_small_f2 (sha256: policy.txt 3c7ff5cb…, KL.bin f8829d72…; these are not the
files of the stored example examples/accepted-proof/), as PlanKits.lean has them written out; a
stored proof's own configuration may be another file. The repository has a second small folder,
prover/examples/target_small_f2_roomy: that the numbers held here are the same there is not tested
here. Johnson/G/KitFull.lean has the full-size example's two files written out a second time:
nothing here compares the two copies. The bytes are made of lists in this library: no Lean code
compares them with a file on a disk (the head of PlanKits.lean). With no layout file `publicOf`
returns what it returns with one, wherever it returns with one (the head of
Johnson/Road/FormsKeysRunK.lean says why): that it returns with the examples' own layout files is
not run here. Nothing for other parameter files. This file is not part of the compiled program.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Test.TestTablesOfModel
import OnBytes.Model.VerifyPublic
import OnBytes.Tie.Pv.Plan.PlanKits

set_option autoImplicit false

namespace Fo.TablesOfModel

open OnBytes.Tie.Pv.Plan (textOf wordsFile policyF scalesF policyS scalesS)

/-- What the head lists, at a parameter file and a scale file; nothing where the program's public
part refuses. -/
def atFiles (pol KL : ByteArray) : Option ((Nat × Nat × Bool × Bool) × (Nat × Nat × Nat × Nat) ×
    List (Nat × Nat) × Bool × Bool × Bool × Bool) :=
  match OnBytes.Model.Verify.publicOf pol KL none with
  | .error _ => none
  | .ok X =>
    let h := X.layers.y.h
    some ((h.eg, h.smax, h.p3, h.gcl), (h.cs, h.theta0, h.dh, h.lt),
      (X.A.toList.map fun a => (a.S.cf.S, a.S.cf.rx)).eraseDups,
      X.layers.y.silu == gate.1, X.layers.y.fs == gate.2, X.layers.rope == rope,
      X.A.all fun a => some a.S.Tt == OnBytes.Attention.expTable 12 8)

/-! ## The full-size example -/

#guard atFiles (textOf policyF) (wordsFile scalesF) ==
  some ((8, 4095, true, true), (12, 500000, 128, 10), [(12, 8)], true, true, true, true)

/-! ## The small example -/

#guard atFiles (textOf policyS) (wordsFile scalesS) ==
  some ((8, 4095, true, true), (12, 10000, 128, 6), [(12, 8)], true, true, false, true)

end Fo.TablesOfModel
