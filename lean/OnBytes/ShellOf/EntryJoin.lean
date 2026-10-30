-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/EntryJoin.lean: two truth values for a file that runs the checks of the key file,
the entry file and the proof file one after the other, behind the parser outside Lean.

States. Definitions only. `yesAtP` (`yesSmallP O`, `yesFullP O`): the entry file's check as a plain
Bool, without input or output: the ID's form, the standard test of the public files, the untrusted
reader `parseP`, then `runAt`. `rdProofHead`: the first two fields of a parsed proof file.
`furtherIs leaf proof`: both readers return, and fields 3 and 4 of the parsed leaf file (root,
answers) are fields 1 and 2 of the parsed proof file.
Under. No hypothesis. The theorems are in EntryJoinLaws.lean.
Does not show.
  1. Soundness: this is a test that serves the runs of lean/Ask/.
  2. That `yesAtP` computes what the program `entryParsedMainO O` computes: no theorem links them.
  3. The program's caps on the files' lengths: `yesAtP` has none.
  4. Anything of the parsed proof file beyond its first two fields.
  5. That whatever judges the key file or the proof file takes its table from these fields: its
     caller must see to that.
  6. That the checks which a caller combines are at one ID, hash function, size, public files and
     byte strings (not paths, which can be read anew): the caller must see to that too.
  7. That O is the function by which a caller's other checks hash: here O's answers are taken as 256
     bits, cut or filled (`oBO`, `cRun`, EntryProg.lean); a check that hashes by `Fmt.HO O` is at
     the same function only where O answers 32 bytes, as `Fmt.oracle` does.
  8. Any test of the number "copy" (the proof form's field 4): it is compared with nothing; the leaf
     table's number is in the leaf file's name only.
  9. Anything of any original file.
 10. What EntryParsed.lean lists as not shown.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ShellOf.EntryParsed

set_option autoImplicit false

namespace OnBytes.ShellOf.EntryParsed

open OnBytes.ShellOf.Claimed
open OnBytes.ShellOf.EntryProg
open OnBytes.Tie (AskedE EntryGround)
open TypedOracleCompiler.Slice (runEntryFull runEntrySmall)
open OnBytes.Slice.Shapes (Cfg)
open _root_.Fmt (rdDigest rdList)

/-- The entry file's part behind the parser outside Lean, as one Bool. -/
def yesAtP (z : Params.StdSize) (G : EntryGround)
    (R : Cfg → AskedE → (ByteArray → ByteArray) → Bool) (O : ByteArray → ByteArray)
    (id0 : String) (cfg : Params.StdCfg) (key leaf : ByteArray) : Bool :=
  match Model.Verify.idAsked id0 with
  | some id =>
    Params.stdEntry z cfg &&
      (match parseP G O ⟨id, cfg⟩ key leaf with
        | .ok a => runAt R G.q.link.table O ⟨id, cfg⟩ a
        | .error _ => false)
  | none => false

def yesSmallP (O : ByteArray → ByteArray) : String → Params.StdCfg → ByteArray → ByteArray → Bool :=
  yesAtP Params.stdSmall Tie.smallRecordGround runEntrySmall O

def yesFullP (O : ByteArray → ByteArray) : String → Params.StdCfg → ByteArray → ByteArray → Bool :=
  yesAtP Params.stdFull Tie.recordGround runEntryFull O

def magicProof : ByteArray := "FPPRFC01".toUTF8

/-- Of the parsed proof file: the magic, the leaf table's root, its answers. -/
def rdProofHead (b : ByteArray) : Option (ByteArray × List E) :=
  if b.extract 0 8 == magicProof then do
    let (root, i) ← rdDigest b 8
    let (answers, _) ← rdList rdE b i
    some (root, answers)
  else none

/-- The parsed leaf file's own table is the table that the parsed proof file names. -/
def furtherIs (leaf proof : ByteArray) : Bool :=
  match rdLeaf leaf, rdProofHead proof with
  | some L, some P => decide (L.root = P.1) && decide (L.answers = P.2)
  | _, _ => false

end OnBytes.ShellOf.EntryParsed

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/ShellOf/EntryJoin.lean: TWO BOOLS FOR A FILE THAT RUNS THE THREE FILES' CHECKS IN A ROW,
behind the parser outside Lean (tools/parser/PARSED-FORM.md, sections 2 and 3): the entry file's
part as a plain Bool, without a shell; and: is the table that a parsed proof file names the table
that this part judged as its further one? Definitions alone; the laws are in
OnBytes/ShellOf/EntryJoinLaws.lean.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

  `yesAtP z G R O id0 cfg key leaf`, `yesSmallP O`, `yesFullP O`: the user's ID is 64 hex digits;
    the standard test of the three public files; the reader `parseP` (untrusted) at O and the two
    parsed files' bytes; then `runAt` at the reader's value. False where any of these says no or
    hands nothing over. Written after the order in which `entryParsedMainO O`
    (OnBytes/ShellOf/EntryParsed.lean) goes (`runOf`, OnBytes/ShellOf/Claim.lean, at `kitSmallP` |
    `kitFullP`, behind `idAsked`); no law ties the two texts; the caps on the files' lengths are the
    program's alone.
  `rdProofHead`: of `proof.parsed.bin` the magic `FPPRFC01` and fields 1 and 2 (the leaf table's
    root and answers) and no more: the rest of that file is not looked at.
  `furtherIs leaf proof`: both readers return, and fields 3 and 4 of the parsed leaf file (root,
    answers) are fields 1 and 2 of the parsed proof file.

The key file's side needs no Bool: `parseP` takes the value's first table out of `key.parsed.bin`'s
fields 1 and 2 itself.

What is not claimed. That whatever judges the key file or the proof file takes its table out of
these fields: that is its caller's to see to; so is that all the terms which it joins stand at one
ID, one hash function, one size, the same three public files and the same byte strings (not paths,
which can be read anew). Of the hash function: here O's answers are taken as 256 bits, cut or filled
(`oBO`, `cRun`, OnBytes/ShellOf/EntryProg.lean); a term that hashes by `Fmt.HO O` stands at the same
function only where O answers 32 bytes, as `Fmt.oracle` does. The number in the proof form's field 4
("copy") is held against nothing: the leaf table's number stands in the leaf file's name alone. A
"true" says nothing of any original file. All that the head of OnBytes/ShellOf/EntryParsed.lean does
not claim.

-/
