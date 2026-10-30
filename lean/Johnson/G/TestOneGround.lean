-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/TestOneGround.lean: the written copies of the shipped examples' public files, held against
one another byte for byte.

Runs alone; no theorem. A line "#guard" is evaluated by Lean's interpreter when this file is
compiled, and the compilation fails if the value is not true.

Why. Tests and evaluations in this library stand at values that are typed copies of an example's
public files (policy.txt, layout.txt, KL.bin), and one example is typed in several files, each in a
spelling of its own. Each of these files says in its head that no Lean code compares its values with
a file. Here the copies are compared with one another, so that a value at which one test stands is
known to have the bytes of the value at which another stands, or known not to.

THE FULL-SIZE EXAMPLE, prover/examples/target_full_f2: THREE WRITINGS, AND THE THREE ARE ONE.
  OnBytes/Tie/Pv/Plan/PlanKits.lean: `policyF` (lines), `scalesF` (32-bit words).
  OnBytes/K/Oracle/SaysLinesFull.lean: `fullPolicy` (bytes): the parameter file alone.
  Johnson/Road/FormsKeysRunK.lean: `linesKF` (lines), `scalesKF` (words).
THE SMALL SIZE HAS TWO EXAMPLES, ONE LINE APART. By the heads of the files that hold them:
  prover/examples/target_small_f2: PlanKits.lean's `policyS`, `scalesS`; FormsKeysRunK.lean's
    `linesKS`, `scalesKS`. The two are one. OnBytes/Model/TestConfig.lean's `klFile` has the scale
    file's bytes too.
  prover/examples/target_small_f2_roomy: OnBytes/K/Oracle/SaysLinesSmall.lean's `smallPolicy`: the
    parameter file alone.
  The two examples' parameter files have 183 lines and 2479 bytes each and part in one line, the
  105th: "MF 44" in the first, "MF 43" in the second. WHAT IS RUN AT ONE IS NOT RUN AT THE OTHER.

Main names: `linesOf`, `partsOf`.
Limits. That any of these values is a file of the repository is not tested: nothing here reads a
folder of examples or reckons a sum. A run is no theorem: it is the interpreter's word at these
values. Equal bytes are not equal calls: FormsKeysRunK.lean's runs go without a layout file. A
further small parameter file stands written in TestConfig.lean (`kit`):
it is neither example's and is not compared here. The layout
files, and the second small example's scale file, are not compared here. Whether a test on public
files says the same at both small examples is not said here. All hold public parameters and scales,
no weights. The program does not read this file.


-/
import OnBytes.Tie.Pv.Plan.PlanKits
import OnBytes.K.Oracle.SaysLinesFull
import OnBytes.K.Oracle.SaysLinesSmall
import Johnson.Road.FormsKeysRunK
import OnBytes.Model.TestConfig

namespace Johnson.G.OneGround
open OnBytes.Tie.Pv.Plan
open OnBytes.Road (textK wordsK linesKF scalesKF linesKS scalesKS)

/-- The lines of a text, cut at line feeds; behind a last line feed stands one empty line more. -/
def linesOf (a : ByteArray) : List String := (String.fromUTF8! a).splitOn "\n"

/-- The places at which two texts part, as far as the shorter has lines: the line's number, counted
from 0, and the two lines. -/
def partsOf (a b : ByteArray) : List (Nat × String × String) :=
  ((linesOf a).zip (linesOf b)).zipIdx.filterMap
    fun p => if p.1.1 == p.1.2 then none else some (p.2, p.1.1, p.1.2)

-- The full-size example: each writing against PlanKits.lean's.
#guard OnBytes.K.Oracle.fullPolicy.data == (textOf policyF).data
#guard (textK linesKF).data == (textOf policyF).data
#guard (wordsK scalesKF).data == (wordsFile scalesF).data

-- The first small example: each writing against PlanKits.lean's.
#guard (textK linesKS).data == (textOf policyS).data
#guard (wordsK scalesKS).data == (wordsFile scalesS).data
#guard OnBytes.Model.TestConfig.klFile.data == (wordsFile scalesS).data

-- The two small examples' parameter files: as many bytes, as many lines, and apart in one line.
#guard ((textOf policyS).size, OnBytes.K.Oracle.smallPolicy.size) == (2479, 2479)
#guard ((linesOf (textOf policyS)).length, (linesOf OnBytes.K.Oracle.smallPolicy).length) ==
  (184, 184)
#guard partsOf (textOf policyS) OnBytes.K.Oracle.smallPolicy == [(104, "MF 44", "MF 43")]

end Johnson.G.OneGround
