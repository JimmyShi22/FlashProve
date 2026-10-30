-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/EntryParsed.lean: an asking file: a test; no soundness. It is no part of the library: no file
of it imports this one, and `lake build` does not take it. It is Ask/EntryProgram.lean's sister:
the same check of an entry file (the format's pages call it a leaf file), from the user's claim to
an exit code, but behind the parser that stands outside Lean: parse with tools/parser/, then one
command. It calls `OnBytes.ShellOf.EntryParsed.entryParsedCheck` (OnBytes/ShellOf/EntryParsed.lean).
The parsed form is tools/parser/PARSED-FORM.md's. It is not the form of `Fmt.EntryParsed`
(Fmt/ParsedTypes.lean).

Reads: from the user's side, and through no parser, under examples/accepted-proof/
  (ENTRY_SIZE=small, the default), examples/accepted-proof-clipped-gap/ (ENTRY_SIZE=clipped; the
  small size's check) or examples/full-size/ (ENTRY_SIZE=full): ID.txt (the commitment ID: its
  first 64 signs) and config/policy.txt, config/layout.txt, config/KL.bin (the three public
  files). From the parser's side, in the directory that ENTRY_PARSED names: key.parsed.bin (its
  magic word and its fields 1 and 2 alone: the first table's root and answers) and
  leaf-0.parsed.bin (whole; the parser writes leaf-<k>.parsed.bin, k the number in the proof's
  head: 0 at the stored examples that we have seen). It reads no .seeds, .seeds0 or .order file, no
  key file, no entry file, no proof file, no request and no reply. ENTRY_EXAMPLES names another
  folder in the place of ../examples (a path as seen from lean/).

Command: first, from the repository's root, the parser, as tools/parser/README.md says (it needs
  bash, GNU coreutils, python3 and g++ 13 or later, and the repository around it: it compiles the
  C++ verifier's source first):
    W=$(mktemp -d) && echo "W=$W"
    tools/parser/parse_files.sh examples/accepted-proof/config examples/accepted-proof/ivk \
      examples/accepted-proof/example.req examples/accepted-proof/example.proof \
      "${W:?first run the line with mktemp}/work"
  Its last line begins "PARSED AND READ BACK:" and names the directory with the parsed files. Then,
  from lean/, behind a build, with that directory's whole path in the place of DIR:
    ENTRY_PARSED=DIR LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --tstack=8000000 Ask/EntryParsed.lean
  For another example: the parser on that example's folder, and ENTRY_SIZE=clipped or
  ENTRY_SIZE=full before the command. To see it refuse, put ENTRY_PLANT=1 before it (no other value
  plants): that turns the first digit of the commitment ID. The evaluating thread reserves its
  stack (8 GB of address space), so a cap on address space must be wide.

Takes: two to three and a half minutes and 4.9 GiB of memory at a small example, 19 to 30 minutes
  and 6.3 GiB at the full-size one: several runs each, in Lean's interpreter, on a shared machine
  with 128 cores under other load; the parser's own time is on its page. No program is linked. The
  no under ENTRY_PLANT=1 took four to eight minutes at a small example (several runs): the tests run
  once more to name the stage.

Its print means: at a yes it prints four lines, the last of which begins "YES: OF THE VALUE THAT
  LEAN's READER MADE OF THE TWO PARSED FILES GIVEN", and the command's exit code is 0. What has then
  run:
  1. a test that the first 32 lines of policy.txt are those of this size's default setting, and a
     bound on the three public files' length; the rest of the three files enters through the hash
     alone;
  2. two steps that are trusted for nothing, and are together the prover's last step:
     tools/parser/, outside Lean, and a reader of the two parsed files, written in Lean (the prints
     call it "the converter"). The reader decodes their fields; it hashes no row, column or path of
     them (the two roots enter the names from which it draws the seeds: below). In
     leaf-0.parsed.bin it refuses a byte left over; behind the two fields of key.parsed.bin it
     looks at nothing; it refuses where the leaf file's copy of the first table's root and answers
     is not the key file's, a tree that the description opens nowhere, and a row whose path has not
     as many digests as its tree is deep. It lays the decoded fields out as the value that the
     check takes, with shapes that it takes from the protocol's description itself: the check does
     not hold these against the description. It computes the public files' digest and draws both
     tables' seeds itself (it reads no seeds file), through the same hash function that the check
     takes: here the format's oracle, made of BLAKE2b, at which they are the digest and the seeds
     that the library's converter makes (`cRun_oracle`, `seedsUnder_oracle`,
     OnBytes/ShellOf/EntryParsedLaws.lean); the check draws the seeds anew and compares;
  3. the closed check `verifyEntrySmall` | `verifyEntryFull` in its form for a run, with the
     stages FIT, P, A, S and V, as Ask/EntryProgram.lean's head says them. It is not the term that
     the library's pages call innerCompiledVerifier;
  4. the comparison of the commitment ID that the hash function gives of the three public files
     and the value's first table with the user's, in lower-case digits (ID).
  Two of the four lines give out words of the further table (its root as judged; the ID's text at
  its root and answers). They are held against nothing in this call: the caller may hold the root
  against field 1 of proof.parsed.bin, and the second word against the like word computed of that
  file's fields 1 and 2.
  By `OnBytes.ShellOf.EntryParsed.entryParsedCheck_returns` (OnBytes/ShellOf/EntryParsedLaws.lean),
  if it returns without an exception, then 1 said yes at the three public files that were read, 3
  at these and at the value that the reader made (a yes of the value, not of any file), and 4
  holds of that value's first table. The theorem speaks of the format's one oracle (`Fmt.oracle`),
  made of this library's BLAKE2b, as a function on bit strings; on the bound and on what is assumed
  of that function see Ask/EntryProgram.lean's head. Step 4 is in no bound.
  At a no of the verifier it prints "NO: the verifier:" with the stage. Where the reader refuses it
  prints the reader's own words and "NOT CHECKED: the converter hands nothing over"; other refusals
  print "NOT CHECKED:" with the ground; where the arguments are not as the usage line says it
  prints the usage line alone. In each of these cases `entryParsedCheck` throws, Lean prints an
  error that says "NOT A YES: the program's exit code is", and the command's exit code is 1.
  Where ENTRY_PARSED is not set the file itself throws "NOT A YES: set ENTRY_PARSED …". Under
  ENTRY_PLANT=1 the stage must be ID. Nothing is printed before the run has ended.
  An end without one of these lines is no verdict: a missing ID.txt, an import that is not built,
  an end by the stack or by memory (a hostile parsed file that names a very long list may end the
  run so, and not by a refusal). Some of these also give the exit code 1.

It does not mean: that the key file and the entry file are good, or that the parser is right.
  NOTHING ON SOUNDNESS FOLLOWS FROM THIS YES ALONE: what Ask/EntryProgram.lean's head says of the
  bound holds here. It is a test through Lean's interpreter, which no theorem covers.
  The two original files are not seen, and nothing here says that the parsed files come from them.
  It checks one file of the three that a whole call checks, and the commitment ID against the first
  table: no key file's chain, no proof file, no request and no reply. It does not know which entry
  it judged: the number stands in the parsed file's name alone.
  AMONG WHAT NOTHING IN THIS CALL TESTS: that the chain's run's value is the hash that the format's
  verifier computes (that it has 32 bytes and is not 32 zero bytes is tested; the parsed form has
  not the bytes from which it could be computed); rows at places that no round asks for; and what
  Ask/EntryProgram.lean's head lists. By its text the library's own converter, behind which
  Ask/EntryProgram.lean runs, computes that value itself (no theorem and no run of ours says so): so
  this road accepts more than that one.
  ENTRY_PLANT=1 turns the user's claim, not the value. Step 3 has been seen to refuse on this road,
  at a small example: a parsed leaf file made by the parser of a leaf file whose chain's tail was
  forged (its later rounds drawn anew, the proofs of work redone) got "NO: the verifier: V" (several
  runs); a parsed leaf file with a field element spelled (p, 0, 0), the chain forged over that
  spelling, got "NO: the verifier: FIT" (one run): tools/parser/ refuses such a leaf file, and a
  form of it, without that test, made the parsed file.
  That this file and Ask/EntryProgram.lean say the same on one example shows that the two roads
  from the bytes to the value agree there, as far as the check looks; no theorem says so.

-/
import OnBytes.ShellOf.EntryParsed

#eval show IO Unit from do
  let size := (← IO.getEnv "ENTRY_SIZE").getD "small"
  let root := (← IO.getEnv "ENTRY_EXAMPLES").getD "../examples"
  let some dir ← IO.getEnv "ENTRY_PARSED"
    | throw (IO.userError "NOT A YES: set ENTRY_PARSED to the directory with the parsed files")
  let e := root ++ (if size == "full" then "/full-size"
    else if size == "clipped" then "/accepted-proof-clipped-gap" else "/accepted-proof")
  let kit := if size == "clipped" then "small" else size
  let id := ((← IO.FS.readFile (e ++ "/ID.txt")).take 64).toString
  let plant := (← IO.getEnv "ENTRY_PLANT") == some "1"
  let id' := if plant then (if id.startsWith "0" then "1" else "0") ++ (id.drop 1).toString else id
  OnBytes.ShellOf.EntryParsed.entryParsedCheck
    [kit, id', e ++ "/config", dir ++ "/key.parsed.bin", dir ++ "/leaf-0.parsed.bin"]
