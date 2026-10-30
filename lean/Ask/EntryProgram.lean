-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/EntryProgram.lean: an asking file: a test; no soundness. It is no part of the library: no
file imports it, and `lake build` does not take it. It runs the program for the entry file's part,
`OnBytes.ShellOf.EntryProg.entryCheck` (OnBytes/ShellOf/EntryCheck.lean), on a stored example.
Ask/EntryRecord.lean asks the same closed check with its controls. This file asks more: the whole
call from the user's claim to an exit code, with a theorem on what that exit code says.

Reads: under examples/accepted-proof/ (ENTRY_SIZE=small, the default),
  examples/accepted-proof-clipped-gap/ (ENTRY_SIZE=clipped; the small size's check) or
  examples/full-size/ (ENTRY_SIZE=full): ID.txt (the commitment ID: its first 64 signs) and
  config/policy.txt, config/layout.txt, config/KL.bin (the three public files): these four are the
  user's claim;
  ivk/key.bin (the key file: of it the first table alone, which stands at its head);
  ivk/leaf/0.bin (the entry file). No proof file, no request, no reply. ENTRY_EXAMPLES names another
  folder in the place of ../examples (a path as seen from lean/).

Command: from lean/, behind a build:
    LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --tstack=8000000 Ask/EntryProgram.lean
  For another example put ENTRY_SIZE=clipped or ENTRY_SIZE=full before it. To see it refuse, put
  ENTRY_PLANT=1 before it (no other value plants): that turns the first digit of the commitment
  ID. The evaluating thread reserves its stack (8 GB of address space), so a cap on address space
  must be wide.

Takes: two to four minutes and 4.9 GiB of memory at a small example, 21 to 26 minutes and 6.3 GiB at
  the full-size one: several runs each, in Lean's interpreter, on a shared machine with 128 cores
  under other load. No program is linked. The no under ENTRY_PLANT=1 took four and a half to seven
  minutes at a small example (several runs): the tests run once more to name the stage.

Its print means: at a yes it prints four lines, the last of which begins "YES: OF THE VALUE THAT
  THE PARSER MADE OF THE KEY FILE AND THE ENTRY FILE", and the command's exit code is 0. What has
  then run:
  1. a test that the first 32 lines of policy.txt are those of this size's default setting, and a
     bound on the three public files' length; the rest of the three files enters through the hash
     alone;
  2. a parser of the key file's first table and the entry file, which is trusted for nothing; of
     its answer the plain value alone is taken. It is the hand-written Lean verifier's own strict
     reader of an entry file (the prints call it "the converter");
  3. the closed check `verifyEntrySmall` | `verifyEntryFull` in its form for a run
     (`runEntrySmall` | `runEntryFull`): tests on the parsed value (stage FIT); the description's
     pins (P); the typing of the value (A); a comparison of both tables' seeds, written by hand
     (S); and an evaluable form, proved equal on all arguments, of the lax verifier of the Link
     protocol that a second form of the library's compiler, under OnBytes/TypedOracleCompiler/, makes (V). It is
     not the term that the library's pages call verify();
  4. the comparison of the commitment ID that the hash function gives of the three public files
     and the value's first table with the user's, in lower-case digits (ID). That this is the
     commitment ID of the format's published pages and of the C++ programs is seen at the stored
     examples and proved nowhere. To Lean's own text of the format the term is tied by its
     definition: it draws the record's seeds and then makes one call of `Fmt.publishedIDW`, the hash
     on `Fmt.publishedBytes` (OnBytes/ChecksWithHashAsArgument/M/Key/Table.lean; Fmt/Rules4.lean).
  Two of the four lines give out words of the further table (its root as judged; the ID's text at
  its root and answers): they are held against nothing in this call.
  By `OnBytes.ShellOf.EntryProg.entryCheck_returns` (OnBytes/ShellOf/EntryCheckLaws.lean), if
  `entryCheck` returns without an exception, then: 1 said yes at the three public files that were
  read; 3 said yes at these three files and at the value that the parser made of the key file's
  and the entry file's bytes (a yes of the value, not of the two files); 4 holds of these three
  files and that value's first table.
  Steps 3 and 4 take the hash function as an argument. This run puts there the format's one oracle
  (`Fmt.oracle`), made of this library's BLAKE2b, which is written in Lean; the theorem speaks of
  that function, as a function on bit strings. The bound on the closed check (step 3) is over a
  function drawn at random in that place; that the format's oracle may stand for such a function is
  assumed (lean/README.md, on the ideal hash and BLAKE2b; lean/LIMITS.md, L8). Step 4 is in no
  bound.
  At a no of the verifier it prints "NO: the verifier:" with the stage. Other refusals print "NOT
  CHECKED:" with the ground (the test of step 1 fails; the converter hands nothing over; a file
  cannot be read or is too long). Where the arguments are not as the usage line says (an ENTRY_SIZE
  other than small, clipped or full; an ID that is not 64 hex digits) it prints the usage line
  alone. In each of these cases `entryCheck` throws, Lean prints an error that says "NOT A YES:
  the program's exit code is", and the command's exit code is 1. Under ENTRY_PLANT=1 the stage must
  be ID. Nothing is printed before the run has ended.
  An end without one of the lines "YES:", "NO: the verifier:", "NOT CHECKED:" or the usage line is
  no verdict: a missing ID.txt, an import that is not built, an end by the stack or by memory. Some
  of these also give the exit code 1. On the stored examples anything but the yes means that the
  repository, the build or this library is at fault, not that a prover cheated.

It does not mean: that the files are good. Nothing on soundness follows from this yes alone. It is
  a test on one honest example, through Lean's interpreter, which no theorem covers; that Lean's
  exit code follows a thrown error is a fact of Lean's command line, seen in runs.
  The bound (`verifyEntrySmall_copyBound` | `verifyEntryFull_copyBound`,
  OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean) is not on "a yes on a false statement". It speaks of
  strings read off the log of whoever made the value; it says nothing unless the first table's part
  holds, which the key file's check would have to give and which is not made here; it holds for
  public files that are fixed before the function is drawn; it does not chain with the other
  two parts. Its limits are in that file's head.
  It checks one file of the three that a whole call checks: no key file's chain, no proof file, no
  request and no reply. A key file with one bit turned behind its first table still got a yes of
  `entryCheck`'s program (seen at both sizes, in runs of a compiled form, not through this file; at
  the small one a program built from the text of `verify-on-bytes` refused that file). This check
  does not stand in that text.
  No command here shows step 3 refusing. A damaged entry file is as a rule refused by the parser
  ("NOT CHECKED"), before step 3 is asked; ENTRY_PLANT=1 turns the user's claim, not the value.
  Among what the trusted side does not test: that the chain's run's value is the hash that the
  format's verifier computes (that it has 32 bytes and is not 32 zero bytes is tested); the words
  and the lengths of the two lists of seeds that the parser hands over (they are read as residues
  and compared with the drawn seeds); that every root inside the chain has 32 bytes; that each
  opening's shape is the description's; rows at places that no round asks for. Fields of the value
  that the check does not read may be altered and the yes stands (seen, in a run of a compiled form:
  a nonce at a round without work).

-/
import OnBytes.ShellOf.EntryCheck

#eval show IO Unit from do
  let size := (← IO.getEnv "ENTRY_SIZE").getD "small"
  let root := (← IO.getEnv "ENTRY_EXAMPLES").getD "../examples"
  let e := root ++ (if size == "full" then "/full-size"
    else if size == "clipped" then "/accepted-proof-clipped-gap" else "/accepted-proof")
  let kit := if size == "clipped" then "small" else size
  let id := ((← IO.FS.readFile (e ++ "/ID.txt")).take 64).toString
  let plant := (← IO.getEnv "ENTRY_PLANT") == some "1"
  let id' := if plant then (if id.startsWith "0" then "1" else "0") ++ (id.drop 1).toString else id
  OnBytes.ShellOf.EntryProg.entryCheck
    [kit, id', e ++ "/config", e ++ "/ivk/key.bin", e ++ "/ivk/leaf/0.bin"]
