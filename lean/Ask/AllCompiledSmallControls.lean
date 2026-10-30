-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/AllCompiledSmallControls.lean: the run of Ask/AllCompiledSmall.lean, and then the same run five
times more, each time with one value changed so that the test which holds one of the ties between
the files (join 1 to 3; the proof file's table against the original entry file's) must say NO.

No soundness: a test. See Ask/README.md, "What a yes does not mean".

Reads: What Ask/AllCompiledSmall.lean reads, with the same environment variables. Every change is
  made in memory, after the files are read. Nothing is written to disk.
Command: LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --tstack=4000000 \
    Ask/AllCompiledSmallControls.lean
  (typed in lean/, after the steps that Ask/README.md lists; the faster way serves here too)
Takes: on the same machine as Ask/AllCompiledSmall.lean: with libvob.so, 24 to 40 minutes in four
  runs, and 10 GB. Plain: not measured.
Its print means: First the lines of Ask/AllCompiledSmall.lean. If the unchanged files get no yes,
  the run ends there, and the changes are not run. Then, for each of the five: a line "=== CONTROL
  n" (what was changed: the first digit of the user's commitment ID; one bit of the first table's
  root in the parsed entry file; of the table's root in the parsed key file, in the parsed proof
  file, in the original entry file; and which test is expected to say NO); the lines of that run,
  from "verifier run" on; and a line "CONTROL n" with the tests that said NO, and AS EXPECTED (the
  expected test, and no other), NOT AS EXPECTED, or "ALARM: A YES WHERE A NO WAS EXPECTED" (at
  control 5 also where the root is not found in the original entry file, and nothing was changed).
  lean ends with status 0 only if the unchanged files get a yes and all five end as expected; if one
  does not, the error is "a control did not end as expected".
It does not mean: All that Ask/AllCompiledSmall.lean does not mean. Five changed sets of files that
  are refused. At controls 2, 3 and 4 the line that says NO is the tie itself. At controls 1 and 5
  it is a whole check ("key", "proof"), whose own tests are not printed here: at control 1 only the
  test on the commitment ID reads what was changed; at control 5 the changed table is also the one
  of which the proof file's check makes its record and its first digest, so the verifier inside
  "proof" would say NO without the comparison of the two tables (by reading; no run has tried it):
  control 5 shows that "proof" depends on the original entry file, not that the comparison says NO
  (Ask/ProofCompiledSmall.lean prints that comparison as "parsed file 1"). They are no search for a
  false proof, and they say nothing on soundness. At every one of the five another test would say NO
  as well: none shows that a tie is needed.
-/
import Johnson.RunOne.AskAllLaws

namespace Ask.AllCompiledSmallControls
open Johnson.RunOne.Ask.All

/-- The lowest bit of byte i flipped. -/
def flipAt (i : Nat) (b : ByteArray) : ByteArray :=
  if i < b.size then b.set! i (b.get! i ^^^ 1) else b

/-- The first sign of a text changed: '0' for another sign, '1' for '0'. -/
def turnFirst (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: l => String.ofList ((if c == '0' then '1' else '0') :: l)

/-- The place of the first 32 bytes that are n among the first 4096 places of h. -/
def findIn (n h : ByteArray) : Option Nat :=
  (List.range 4096).find? fun j => h.extract j (j + n.size) == n

/-- One bit flipped in the original leaf file, in its table's root: found there as the 32 bytes that
the parsed proof file has for its table's root. Where they are not found nothing is changed; the
run then says yes, and the control's line reads "ALARM: A YES WHERE A NO WAS EXPECTED". -/
def flipRootIn (proof ent : ByteArray) : ByteArray :=
  match findIn (proof.extract 8 40) ent with
  | some j => flipAt j ent
  | none => ent

/-- The five changes. Behind a parsed file's eight signs of kind a table's root begins at byte 8: in
the parsed key file and the parsed leaf file the first table's, in the parsed proof file the further
table's. -/
def rows : List (String × Option String × (User × Given → User × Given)) :=
  [("the first digit of the user's commitment ID is changed", some "key",
      fun x => ({ x.1 with id := turnFirst x.1.id }, x.2)),
    ("one bit of the first table's root is flipped in the parsed leaf file alone", some "join 2",
      fun x => (x.1, { x.2 with leaf := flipAt 8 x.2.leaf })),
    ("one bit of the table's root is flipped in the parsed key file alone", some "join 2",
      fun x => (x.1, { x.2 with key := flipAt 8 x.2.key })),
    ("one bit of the table's root is flipped in the parsed proof file alone", some "join 3",
      fun x => (x.1, { x.2 with proof := flipAt 8 x.2.proof })),
    ("one bit of the table's root is flipped in the original leaf file alone", some "proof",
      fun x => (x.1, { x.2 with ent := flipRootIn x.2.proof x.2.ent }))]

end Ask.AllCompiledSmallControls

set_option stderrAsMessages false

#eval Johnson.RunOne.Ask.All.runAll Ask.AllCompiledSmallControls.rows
