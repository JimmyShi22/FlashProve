-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1EngineTypedR.lean: the programs' own proof files of the first toy, at the tiny parameters
with a repeated position, run through the compiled verifier with the real hash: the four run
functions with typed oracle functions and pruned openings. A repeated position: a position drawn
twice is opened once: openings go by the drawn positions' set (Fmt/Rules6.lean).

Tests only. The files are the honest proof (7,400 bytes) and thirteen altered copies, as the
enclosed tools make them. The programs are the C++ implementation that comes with this Lean code;
the first toy is a product test (on rows a, b, c with a_i b_i = c_i for every i; Fmt/M1Types.lean).

1. What the file contains. No definition. The rest of part 1 is that of Run/M1EngineTypedF1.lean's
head; it holds here too.

2. What is checked when the file compiles. For each run function that is named here, file by file,
the outcome is the one of the list (`pin`, Run/M1EngineTyped.lean). So the programs' honest proof
is accepted and every other file is refused.

3. Theorems. None. The tests are evaluations made when the file is compiled: they leave no theorem.

Notation: Lax, Strict in a run function's name: through the lenient reader, through the strict
reader (Run/PlanQS.lean, Run/PlanQSP.lean); S, SP at its end: with challenges as sampled values, as
hash blocks (the same two files).

4. What is not claimed. No statement on soundness follows: that these altered copies are refused
says nothing about others. Which check inside the verifier refused is not seen. The limits on these
runs in part 4 of the head of Run/M1EngineTyped.lean hold here too.

Terms: lean/GLOSSARY.md.
-/
import Run.M1EngineTyped

namespace Run.M1EngineTyped.R
open _root_.Fmt.M1 Run.PQ Run.M1Run Run.M1RunAll Run.M1EngineTyped

#guard ((roads[2]?).map fun R => (R.name, voices R Theirs.specTiny Theirs.sizesTiny filesR == pin R laxR filesR)) = some ("runLaxSP", true)
#guard ((roads[3]?).map fun R => (R.name, voices R Theirs.specTiny Theirs.sizesTiny filesR == pin R laxR filesR)) = some ("runStrictSP", true)
#guard ((roads[4]?).map fun R => (R.name, voices R Theirs.specTiny Theirs.sizesTiny filesR == pin R laxR filesR)) = some ("runLaxS", true)
#guard ((roads[5]?).map fun R => (R.name, voices R Theirs.specTiny Theirs.sizesTiny filesR == pin R laxR filesR)) = some ("runStrictS", true)

end Run.M1EngineTyped.R
