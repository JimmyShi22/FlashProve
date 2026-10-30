-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Test/TestTablesOfModel.lean.
A test file: the four public tables that the Lean verifier program (the port under OnBytes/Model;
its executable is verify-on-bytes) computes in whole numbers, each held entry by entry against the
numbers that the theorems' integer model stores, at the one size at which the model stores them.

Runs, no theorem. A line `#guard` is evaluated by Lean's interpreter when this file compiles, and
the compilation fails if the value is not true. The kernel has no part in it.

What is compared with what. The model: `tbRef` (Inst/Model/TablesRef.lean): the five table functions
SILU, SIGM, Exp, C, S, read from packed data (Inst/Model/TablesData.lean: generated data; the
program that generated the numbers is not part of this library). The program: `gateTables` and
`ropeTable` (OnBytes/Model/LayerTables.lean), `expTable` (OnBytes/Model/AttentionExp.lean), at the
numbers that the program has at the full-size example's parameter file: eg 8, smax 4095 (the file
has no line eg or smax: these are what the program's reader takes where the lines are absent: `EG`,
`SMAX`, OnBytes/Model/Config.lean), routed experts, the gate's clamp; cs 12, theta0 500000, dh 128,
lt 10; S 12, rx 8.
 1. SILU: all 65,536 entries: the program's word is the model's value plus 4096. At 32,768 of them
    the model's argument is clamped to one of its two ends: there the guard shows that the program
    clamps as the model does.
 2. SIGM: the 32,768 entries of the model's domain (from 2^14 up to 3 * 2^14): entry t of the
    program's table FS is the model's value at t + 2^14. The upper half of table FS is the gate's
    clamp, which is none of the five functions: not compared here; whether the model has that clamp
    elsewhere is not said here.
 3. The rotary table: 65,536 cosines and 65,536 sines: the program's word is the model's C or S in
    layer 0, plus 4096. The model's C and S hang on the layer only through the question whether it
    has the rotary step. Which layers have that step (the model: none where L % 4 = 3; the program:
    by the scale file) is compared by neither of the two test files: `rotaryK`
    (Johnson/Road/FormsKeysRunK.lean) is run by the guard of Johnson/Road/FormsKeysRunKFull.lean.
    What the program does in a layer without the step is no table: not compared here.
 4. Exp: all 2,307 entries.
231,683 entries in all. One guard a table. Each states the table's length and the number of entries
that differ, 0, and, in the same value, a control: the same count at the model's function moved by
one place (for the rotary table: the cosines held against S, the sines against C) is not 0: so a
count that is 0 for nothing would be seen.

Where the same is had otherwise. Exp: a theorem, by evaluation in the kernel: `expTable_ref`
(Johnson/Road/Lane5AttExp.lean). The other three, through the program's own
`publicOf` on bytes made of lists that were written from the full-size example's two files: the
guard of
Johnson/Road/FormsKeysRunKFull.lean (`ropeK`, Johnson/Road/FormsKeysRunK.lean; `tablesR8`,
Johnson/Road/FormsKeysRun8.lean: all rows of the eight lookup tables of the layers' calls, among
them those that hold SILU and SIGM). Further guards with controls: Johnson/Road/Ends/GuardRope.lean
, Johnson/Road/Ends/GuardTabs.lean [not in this library]. Here no reader of a
file stands between.

The small example: the repository's folder prover/examples/target_small_f2 (sha256: policy.txt
3c7ff5cb…, KL.bin f8829d72…; these are not the files of the stored example
examples/accepted-proof/), as OnBytes/Tie/Pv/Plan/PlanKits.lean has it written out. At its parameter
file the program has the same eg, smax, routed experts, gate's clamp, S and rx
(OnBytes/Tie/Pv/Lookup/Test/TestTablesAtFiles.lean runs the program's `publicOf` on it): so the
program calls `gateTables` and `expTable` there at the very arguments of guards 1, 2 and 4: the
program's SILU, FS and exponentials at the small example are the arrays compared here. `tbRef` is
the model's tables at its one size, `ppref`: which model a statement at the small size names is not
said here. The small example's rotary table is another (theta0 10000, 64 tokens), and the model
stores none for it: guard 3 has no like at the small size.

Limits. Equal tables are all that is held: the lookups are not hereby shown, and nothing is said on
what a lookup in these tables proves. That the numbers above are those that the program has at the
two examples' public files is not tested here: TestTablesAtFiles.lean runs the program's own
`publicOf` on these files as the library has them written out, and holds its arguments and its
arrays against those here. Nothing for other numbers. What the test adds is that two artefacts of
separate make agree at every entry compared. The model's functions are compared at their declared
ranges alone: outside them (Exp from 2,307 on; SIGM below 2^14) the program has no entry. Four
tables alone: the model's sixth table function `EX` (Inst/Model/Tables.lean) and the program's other
lookup tables are outside these guards. Nothing on the tables that the C++ programs compute in
floating point (OnBytes/Model/TestLayerTables.lean holds digests). No theorem says that the numbers
are the rounded values of the real functions. This file is not part of the compiled program.

Not claimed: anything on soundness, completeness or hiding.

-/
import Inst.Model.TablesRef
import OnBytes.Model.LayerTables
import OnBytes.Model.AttentionExp

set_option autoImplicit false

namespace Fo.TablesOfModel

open Inst.Model (tbRef)

/-- The number of t below n at which same t is false. -/
def differ (n : Nat) (same : Nat → Bool) : Nat := ((List.range n).filter fun t => !same t).length

/-- The program's tables SILU and FS at the full-size example's numbers. -/
def gate : Array Nat × Array Nat := OnBytes.Model.Layer.gateTables 8 4095 true true

/-- The program's rotary table at the full-size example's numbers: 1,024 tokens, 64 pairs. -/
def rope : Array Nat := OnBytes.Model.Layer.ropeTable 12 500000 128 10

/-! ## 1. SILU

The length; the number of entries that differ; the control: with the model's function moved by one
place some entry differs. -/

#guard (let g := gate.1
  (g.size, differ 65536 fun t => (g.getD t 0 : Int) == tbRef.SILU (t : Int) + 4096,
    differ 65536 (fun t => (g.getD t 0 : Int) == tbRef.SILU ((t : Int) + 1) + 4096) != 0)) ==
  (65536, 0, true)

/-! ## 2. SIGM

The like, on the lower half of table FS. -/

#guard (let g := gate.2
  (g.size, differ 32768 fun t => (g.getD t 0 : Int) == tbRef.SIGM ((t : Int) + 2 ^ 14),
    differ 32768 (fun t => (g.getD t 0 : Int) == tbRef.SIGM ((t : Int) + 2 ^ 14 + 1)) != 0)) ==
  (65536, 0, true)

/-! ## 3. The rotary table

The length; the cosines that differ; the sines that differ; two controls: held against S some cosine
differs, and held against C some sine. -/

#guard (let r := rope
  (r.size, differ 65536 fun x => (r.getD x 0 : Int) == tbRef.C 0 (x / 64) (x % 64) + 4096,
    differ 65536 fun x => (r.getD (65536 + x) 0 : Int) == tbRef.S 0 (x / 64) (x % 64) + 4096,
    differ 65536 (fun x => (r.getD x 0 : Int) == tbRef.S 0 (x / 64) (x % 64) + 4096) != 0,
    differ 65536
      (fun x => (r.getD (65536 + x) 0 : Int) == tbRef.C 0 (x / 64) (x % 64) + 4096) != 0)) ==
  (131072, 0, 0, true, true)

/-! ## 4. Exp

The length; the entries that differ; the control, as in 1. -/

#guard ((OnBytes.Attention.expTable 12 8).map fun a =>
  (a.size, differ 2307 fun t => (a.getD t 0 : Int) == tbRef.Exp (t : Int),
    differ 2307 (fun t => (a.getD t 0 : Int) == tbRef.Exp ((t : Int) + 1)) != 0)) ==
  some (2307, 0, true)

end Fo.TablesOfModel
