-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1EngineTypedF2.lean: the programs' own proof files of the first toy, at the full parameters
(the toy's full sizes; 30 rounds), run through the compiled verifier with the real hash: the run
function `runStrictSP`.

Tests only. The files are the honest proof (160,520 bytes), thirteen altered copies and nine false
proofs, as the enclosed tools make them. The programs are the C++ implementation that comes with
this Lean code; the first toy is a product test (on rows a, b, c with a_i b_i = c_i for every i;
Fmt/M1Types.lean).

1. What the file contains. No definition. The rest of part 1 is that of Run/M1EngineTypedF1.lean's
head; it holds here too.

2. What is checked when the file compiles. For each run function that is named here, file by file,
the outcome is the one of the list (`pin`, Run/M1EngineTyped.lean). So the programs' honest proof
is accepted and every other file is refused.

3. Theorems. None. The tests are evaluations made when the file is compiled: they leave no theorem.

Notation: Strict in the run function's name: through the strict reader (Run/PlanQSP.lean); SP at its
end: with challenges as hash blocks (Run/PlanQSP.lean).

4. What is not claimed. No statement on soundness follows: that these false proofs are refused says
nothing about others. Which check inside the verifier refused is not seen. The limits on these runs
in part 4 of the head of Run/M1EngineTyped.lean hold here too.

Terms: lean/GLOSSARY.md.
-/
import Run.M1EngineTyped

namespace Run.M1EngineTyped.F2
open _root_.Fmt.M1 Run.PQ Run.M1Run Run.M1RunAll Run.M1EngineTyped

#guard ((roads[3]?).map fun R => (R.name, voices R Theirs.specFull Theirs.sizesFull filesF == pin R laxF filesF)) = some ("runStrictSP", true)

end Run.M1EngineTyped.F2
