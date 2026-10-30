-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/ProofCompiledSmallControls.lean: the run of Ask/ProofCompiledSmall.lean, and then the same run
six times more, each time with one change to the parsed proof file or to the user's reply.

No soundness: a test. See Ask/README.md, "What a yes does not mean".

Reads: What Ask/ProofCompiledSmall.lean reads, with the same environment variables. Every change is
  made in memory, after the files are read. Nothing is written to disk.
Command: LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --tstack=4000000 \
    Ask/ProofCompiledSmallControls.lean
  (typed in lean/, after the steps that Ask/README.md lists; the faster way serves here too)
Takes: on the same machine as Ask/ProofCompiledSmall.lean: plain, about two hours; with libvob.so,
  about 17 minutes; 10 GB. One of the six costs one more whole run, another about a quarter of one.
Its print means: First the lines of Ask/ProofCompiledSmall.lean. If the unchanged file gets no yes,
  the run ends there, and the changes are not run. Then, for each of the six: a line "=== CONTROL n"
  (what was changed, and which test is expected to say NO); the lines of that run, from "parsed
  file" on; and a line "CONTROL n" with the answer, the tests that said NO, and AS EXPECTED or NOT
  AS EXPECTED. Where a change cannot be made (the file has no place for it), the line says so, and
  that counts as NOT AS EXPECTED. lean ends with status 0 only if the unchanged file gets a yes and
  all six end as expected; if one does not, the error is "a control did not end as expected".
It does not mean: All that Ask/ProofCompiledSmall.lean does not mean. Six changed files that are
  refused show that these tests can say NO on this file. They are no search for a false proof, and
  they say nothing on soundness. Only one of the six tests the protocol's own checks (those that
  were written by hand after the C++ verifier). This was seen once, at the small size, on made-up
  weights, in a copy of this check [not in this library] in which the protocol's own checks were
  replaced by ones that say yes to everything. There controls 1, 2 and 3 were still refused by the
  tests before the verifier ("parsed file 1", "parsed file 3", "parsed file 5"), control 4 at "proof
  form" and control 5 at "run"; control 6, the false reply, was accepted. This file's own print does
  not show which of the six it is: controls 5 and 6 both say NO at "run" and no more. So five of the
  six would end as they do if those checks said yes to everything, and the sixth shows of them only
  that they refuse a reply with one bit changed.
-/
import Johnson.RunOne.AskProof
import Johnson.RunOne.Controls

namespace Ask.ProofCompiledSmallControls
open Johnson.RunOne.Controls
open OnBytes.Maker.Carrier (File)

/-- One bit of the shared chain's run value. -/
def turnRunTwo (k : File) : Option File := (bit0 k.run2).map fun r => { k with run2 := r }

/-- The third chain's run value is one zero byte longer. -/
def turnRunLonger (k : File) : Option File := some { k with run3 := k.run3.push 0 }

/-- The changes on the prover's side: each changes one value of the parsed proof file, in memory. -/
def rows : List (String × Option String × (File → Option File)) :=
  [("one bit of the table's root in the parsed file is changed", some "parsed file 1", turnTable),
    ("one bit of the shared chain's run value is changed", some "parsed file 3", turnRunTwo),
    ("the third chain's run value is one zero byte longer", some "parsed file 5", turnRunLonger),
    ("the salt of the slot's leaf is one zero byte longer", some "proof form", turnLonger),
    ("one opening more, at a leaf that the verifier does not read", some "run", turnMore)]

/-- The change on the user's side: a well-formed false claim. -/
def replies : List (String × Option String × (ByteArray → Option ByteArray)) :=
  [("one bit of the user's reply is changed: a false claim", some "run", replyOther)]

end Ask.ProofCompiledSmallControls

set_option stderrAsMessages false

#eval Johnson.RunOne.Ask.Proof.run Ask.ProofCompiledSmallControls.rows
  Ask.ProofCompiledSmallControls.replies
