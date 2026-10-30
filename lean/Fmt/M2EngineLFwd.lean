-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2EngineLFwd.lean: tests that the altered copies and the false proofs of one set of files of the
second toy are refused, and by which stage of the verifier (files 10 to 12 of the set's 21: altered
copies alone).

The second toy is a test protocol of the programs. An altered copy is the honest proof with one byte
or eight bytes overwritten at one place, without its last byte, or with one byte more
(`f_altered_01` to `f_altered_13`, Fmt/M2ProgLFFiles.lean).

The set of files: full parameters.

Sources. The paragraph "Sources." of Fmt/M2EngineLFwa.lean's head holds here too. The data are
made-up toy data: no model and no weights.

The verifier on bytes has two stages. The first is the strict reader, `wholeChainF`
(Fmt/Rules8Fast.lean). It is this library's rendering of the format page's verifier up to its
decision: it cuts the file, recomputes the hash chain from which the challenges are drawn, tests the
proofs of work and checks every Merkle opening against its root. The second is the decision, the
algebraic part of the check: `Fmt.M2.dec` (Fmt/M2All.lean).

1. What the file contains. One helper, `who`, which gives the outcome: "reader" if the strict reader
   refuses the file, else "decision" if the decision refuses, else "accepted". And tests.

2. What is checked when the file compiles (#guard). File by file, for the files of this part:
   refused by the strict reader.

3. Theorems. None.

4. What is not claimed.
   No theorem. The tests (#guard) are evaluations that Lean makes when the file compiles. They speak
     of these bytes and of nothing else.
   No statement on soundness follows from these tests.
   The outcome does not tell which check of the strict reader, or which of the decision's two
     checks, failed. (The two are the checks of the last block of the proximity test. The decision
     also refuses where sizes or the shape of its input do not fit, so the outcome "decision" need
     not come from one of the two; see the head of Fmt/M2Dec.lean, under 1.)
   Nothing is claimed here of the compiled verifier (see Run/M2Engine*.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Theirs
import Fmt.M2ProgLFFiles
import Fmt.M2All
import Fmt.M1View
import Fmt.Rules8Fast

namespace Fmt
namespace M2
namespace EngineLFwd
open ProgLF Fmt.M1

/-- The outcome on the file `b`: the stage that refuses it, or "accepted". -/
def who (b : ByteArray) : String :=
  match wholeChainF Theirs.specFull b with
  | none => "reader"
  | some o => if dec toyPar (viewOf Theirs.specFull.firstTree o) then "accepted" else "decision"

#guard who f_altered_10 = "reader"
#guard who f_altered_11 = "reader"
#guard who f_altered_12 = "reader"

end EngineLFwd
end M2
end Fmt
