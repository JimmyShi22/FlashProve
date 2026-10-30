-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/KeyCompiledSmallControls.lean: the run of Ask/KeyCompiledSmall.lean, and then the same run six
times more, each time with one value of the parsed key file changed.

No soundness: a test. See Ask/README.md, "What a yes does not mean".

Reads: What Ask/KeyCompiledSmall.lean reads, with the same environment variables. Every change is
  made in memory, after the parsed key file is decoded. Nothing is written to disk.
Command: LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --tstack=4000000 \
    Ask/KeyCompiledSmallControls.lean
  (typed in lean/, after the steps that Ask/README.md lists; the faster way serves here too)
Takes: on the same machine as Ask/KeyCompiledSmall.lean: plain, about 31 minutes; with libvob.so,
  about 15 minutes; 6 GB. Each changed file that passes the tests before the verifier costs one
  more whole run.
Its print means: First the lines of Ask/KeyCompiledSmall.lean. If the unchanged file gets no yes,
  the run ends there, and the changes are not run. Then, for each of the six: a line "=== CONTROL n"
  (what was changed, and which test is expected to say NO); the lines of that run, from "parsed
  file" on; and a line "CONTROL n" with the answer, the tests that said NO, and AS EXPECTED or NOT
  AS EXPECTED. It is as expected if the answer is NO and the expected test is among those that said
  NO, or if the run stopped before an answer under the expected name. lean ends with status 0 only
  if the unchanged file gets a yes and all six end as expected; if one does not, the error is "a
  control did not end as expected".
It does not mean: All that Ask/KeyCompiledSmall.lean does not mean. Six changed files that are
  refused show that these tests can say NO on this file. They are no search for a false proof, and
  they say nothing on soundness.
  None of the six is refused by "accept 9" alone, the protocol's own checks on what the three chains
  have read. Controls 1 to 3 are refused by the tests before the verifier ("claim 3", "claim 2",
  "claim 5"); controls 4 and 5 by tests that the compiler makes for every protocol ("after 4",
  "after 3"; at control 5 "accept 9" says NO too); control 6 by the test on the three rounds without
  a challenge ("accept 8"). The line "after 5" repeats the nine "accept" tests together: its NO at
  control 5 is that of "accept 9", at control 6 that of "accept 8". Seen in one run at the small
  size, on made-up weights: a copy of this run, changed so that "accept 9" always says yes, gave the
  same seven answers: yes, then NO six times. That copy is not in this library.
-/
import Johnson.RunOne.AskKeyLaws

namespace Ask.KeyCompiledSmallControls
open OnBytes.Maker

/-- 1 added to the first word. -/
def bump : List UInt64 → List UInt64
  | [] => []
  | w :: l => (w + 1) :: l

/-- The lowest bit of the first byte flipped. -/
def flip0 (b : ByteArray) : ByteArray := if 0 < b.size then b.set! 0 (b.get! 0 ^^^ 1) else b

/-- The six changes: what is changed; the name, up to the colon, of the test that is expected to
say NO; the change. -/
def rows : List (String × Option String × (Carrier.File → Carrier.File)) :=
  [("one bit of the table's root is flipped", some "claim 3",
      fun k => { k with root := flip0 k.root }),
    ("one zero byte is added behind the binding root", some "claim 2",
      fun k => { k with bindRoot := k.bindRoot.push 0 }),
    ("one bit of the shared chain's run value is flipped", some "claim 5",
      fun k => { k with run2 := flip0 k.run2 }),
    ("one bit of the salt of the slot's leaf is flipped", some "after 4",
      fun k => { k with slotSalt := flip0 k.slotSalt }),
    ("1 is added to the first word of the stored table's first opening", some "after 3",
      fun k => { k with stored := match k.stored with
        | r :: rs => { r with column := bump r.column } :: rs
        | [] => [] }),
    ("the number of the stored copy is changed to 1", some "accept 8",
      fun k => { k with copy := 1 })]

end Ask.KeyCompiledSmallControls

set_option stderrAsMessages false

#eval Johnson.RunOne.Ask.Key.run Ask.KeyCompiledSmallControls.rows
