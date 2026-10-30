-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/EntryFilesSmall.lean: an asking file: "read the files, then check" of an entry file, in its form
for a run at the format's hash (`runEntryFilesSmall`, OnBytes/K/Oracle/VerdictOnFilesRun.lean), is
asked at the small stored example and at twelve damaged copies of it; and the closed check behind
the reader is asked at two parsed values that no reader made.

Reads: examples/accepted-proof/config/policy.txt, examples/accepted-proof/config/layout.txt,
examples/accepted-proof/config/KL.bin, examples/accepted-proof/ivk/key.bin,
examples/accepted-proof/ivk/leaf/0.bin.

Command: from lean/, behind a build: LEAN_ABORT_ON_PANIC=1 lake env lean Ask/EntryFilesSmall.lean

Takes: AS MEASURED, from disk, the command as it stands above (the variable was set for the whole
job), in Lean's interpreter alone, at the default stack, two other asking files running at the same
time on the same machine: 353 s and a peak of 5.1 GiB: rows 1 and 8 took 125 s each (the reader runs
twice in each), row 15 took 74 s (the reader's run among it), the other twelve at most 6 s each.

Its print means: Lean's evaluator (the interpreter) computed the function at thirteen inputs, and
the closed check at two more, and printed each answer beside the answer that this file expects. Row
1: at the five files as they lie the function says yes: by `verifyEntrySmall_of_runFiles`
(OnBytes/K/Oracle/VerdictOnFilesYes.lean), with no premise beside that yes, the reader then returns
a parsed value a with `verifyEntrySmall cfg a Run.oBits = true`. Rows 2 to 7 and 9 to 13: with one
bit turned in one of the five files, or the entry file one byte shorter or longer, it says no. Row
8: with one bit turned in the key file's last byte it still says yes: THE FUNCTION READS THE KEY
FILE'S HEAD, ROOT AND ANSWERS AND NOTHING BEHIND THEM: the key file is parsed here, not checked.
Beside each answer stands whether the reader returned a value at all. The line before the rows
evaluates the one premise of `runEntryFilesSmall_eq` at the three public files as they lie (rows 2
to 4 ask at other public files, of the same lengths: there it is not evaluated anew): with it, by
that theorem, each printed answer is the value of `verifyEntryFilesSmall`
(OnBytes/K/Oracle/VerdictOnFiles.lean) at these files and at the function on bit strings that is
made from the format's hash (`Run.oBits`). Row 14: the closed check in its form for a run
(`runEntrySmall`) says no at a parsed value that no reader made and that passes the tests on the
parsed value (`zeroOne`, `zeroOne_fit`, OnBytes/K/Oracle/YesNotFree.lean): A NO PAST THE READER, FOR
THE VALUE'S FORM ALONE: that value has no round, and the check refuses it at every function, before
a hash is compared (by the check's text: the head of OnBytes/K/Oracle/YesNotFree.lean). The row
shows that the check does not accept whatever passes the tests on the parsed value, and no more. Row
15: the closed check says no at the reader's own value from row 1 with one answer of the further
table replaced by another canonical value; the tests on the parsed value still say yes: A NO OF THE
CHECK AT A VALUE ONE ANSWER AWAY FROM THE ACCEPTED ONE; which step says no is not printed. The seeds
are drawn from a table's root, the digest and the shape, not from its answers (`nameUnder`,
OnBytes/Tie/EntryAskM.lean): the replaced answer leaves them as they were. If a line is not as
expected the command ends with an error and a status other than 0.

It does not mean: A THEOREM: an evaluation leaves no declaration, and nothing that is checked of
declarations is checked of it; it is trusted that the evaluator computes the terms as Lean's kernel
would, and that the bytes on disk are the named files'. Nor that the check behind the reader refuses
a damaged FILE: WHERE THE PRINT SAYS THAT THE READER RETURNED NO VALUE, THE NO IS THE READER'S
(`no_of_no_value` below), and the closed check was not reached: in the run that was measured that
was so in all eleven rows on files that say no. Rows 14 and 15 are two values: no more is shown of
what the check refuses. Nor anything on the key file beyond its first table, on the commitment ID,
on the proof file, the request or the reply: the function does not look at them. Nor that the three
public files say the sizes at which it checks: it hashes them and parses none of them; the sizes are
those of the library's typed value `smallRecordGround` (OnBytes/Tie/EntryGrounds.lean). Nor anything
under a drawn hash function, where the bounds of OnBytes/K/Oracle/VerdictOnFiles.lean live: one
fixed function is asked. Nor that the text of verify-on-bytes says the same: it does not call
these terms. One example, on made-up weights; fifteen inputs. The small size alone. All that the
heads of OnBytes/K/Oracle/VerdictOnFiles.lean and VerdictOnFilesRun.lean do not claim. Nothing on
soundness or on hiding.

For which format: the one that the library's Fmt/ describes in the tree in which this file lies. The
stored example must have been made by that tree's programs: at files of another format row 1 is
expected to read NOT AS EXPECTED.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.VerdictOnFilesYes
import OnBytes.K.Oracle.YesNotFree

set_option autoImplicit false

namespace Ask.EntryFilesSmall
open OnBytes.K.Oracle
open OnBytes.Slice.Shapes (Cfg Files)
open OnBytes.Tie (smallRecordGround linkAtCfg keyAt askedAt)

/-- The five files that are read: three public files, the key file, the entry file. -/
structure Five where
  /-- the parameter file -/
  pol : ByteArray
  /-- the layout file -/
  lay : ByteArray
  /-- the scale file -/
  KL : ByteArray
  /-- the key file -/
  key : ByteArray
  /-- the entry file -/
  ent : ByteArray

/-- The question: "read the files, then check", in the form for a run, at the format's hash. The
proof file, the request and the reply are empty: the function does not read them. -/
def ask (x : Five) : Bool :=
  runEntryFilesSmall ⟨x.pol, x.lay, x.KL⟩
    ⟨x.key, x.ent, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

/-- Does the reader return a value? The term that `runEntryFilesSmall` takes apart, asked whether it
is a value. -/
def readsAt (cfg : Cfg) (d : Files) : Bool :=
  (askedAt _root_.Fmt.oracle
    (linkAtCfg smallRecordGround.q (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
    (keyAt smallRecordGround.q.link.table
      (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) d.key).2.2 d.ent).isSome

/-- Where the reader returns no value the function says no: such a no is the reader's. Checked by
Lean's kernel whenever this file is run. -/
theorem no_of_no_value (cfg : Cfg) (d : Files) (h : readsAt cfg d = false) :
    runEntryFilesSmall cfg d = false := by
  unfold readsAt at h
  unfold runEntryFilesSmall
  split
  · rfl
  · next a ha =>
    rw [ha] at h
    cases h

/-- `readsAt` at the five files. -/
def reads (x : Five) : Bool :=
  readsAt ⟨x.pol, x.lay, x.KL⟩ ⟨x.key, x.ent, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

/-- The one premise of `runEntryFilesSmall_eq`: what is hashed for the digest of the three public
files has at most 2 ^ 32 - 144 bytes. -/
def within (x : Five) : Bool :=
  decide ((_root_.Fmt.configBytes [x.pol, x.lay, x.KL]).size ≤ 2 ^ 32 - 144)

/-- b with the lowest bit of its byte at place i turned; b itself where it has no such byte. -/
def turned (b : ByteArray) (i : Nat) : ByteArray :=
  if i < b.size then b.set! i (b.get! i ^^^ 1) else b

/-- The sheet: for each row its name, the answer that is expected, and the files that are asked. -/
def sheet (x : Five) : List (String × Bool × Five) :=
  [("the five files as they lie", true, x),
   ("parameter file: one bit turned in its middle byte", false,
     { x with pol := turned x.pol (x.pol.size / 2) }),
   ("layout file: one bit turned in its middle byte", false,
     { x with lay := turned x.lay (x.lay.size / 2) }),
   ("scale file: one bit turned in its middle byte", false,
     { x with KL := turned x.KL (x.KL.size / 2) }),
   ("key file: one bit turned in byte 0 (the head)", false, { x with key := turned x.key 0 }),
   ("key file: one bit turned in byte 8 (the root)", false, { x with key := turned x.key 8 }),
   ("key file: one bit turned in byte 40 (the first answer)", false,
     { x with key := turned x.key 40 }),
   ("key file: one bit turned in its last byte: NOT READ BY THIS FUNCTION", true,
     { x with key := turned x.key (x.key.size - 1) }),
   ("entry file: one bit turned in byte 0 (the head)", false, { x with ent := turned x.ent 0 }),
   ("entry file: one bit turned in its middle byte", false,
     { x with ent := turned x.ent (x.ent.size / 2) }),
   ("entry file: one bit turned in its last byte", false,
     { x with ent := turned x.ent (x.ent.size - 1) }),
   ("entry file: its last byte cut off", false,
     { x with ent := x.ent.extract 0 (x.ent.size - 1) }),
   ("entry file: one byte 0 more at its end", false, { x with ent := x.ent.push 0 })]

/-- A parsed value that no reader made: the library's `zeroOne` (OnBytes/K/Oracle/YesNotFree.lean),
at the small ground's number of answers: it passes the tests on the parsed value by a theorem
(`zeroOne_fit`). -/
def planted : OnBytes.Tie.AskedE :=
  zeroOne (2 ^ smallRecordGround.q.link.table.v * smallRecordGround.q.link.table.answers)

/-- The closed check, in its form for a run, asked at `planted` past the reader. -/
def askPlanted (x : Five) : Bool :=
  TypedOracleCompiler.Slice.runEntrySmall ⟨x.pol, x.lay, x.KL⟩ planted _root_.Fmt.oracle

/-- The reader's own value at the five files, where it returns one. -/
def readValue (x : Five) : Option OnBytes.Tie.AskedE :=
  askedAt _root_.Fmt.oracle
    (linkAtCfg smallRecordGround.q (OnBytes.Params.configurationDigest [x.pol, x.lay, x.KL]))
    (keyAt smallRecordGround.q.link.table
      (OnBytes.Params.configurationDigest [x.pol, x.lay, x.KL]) x.key).2.2 x.ent

/-- `ask` is: the reader's value, then the closed check at it. So `readValue` is the reader inside
the function that rows 1 to 13 ask. Checked by Lean's kernel whenever this file is run. -/
theorem ask_readValue (x : Five) :
    ask x = match readValue x with
      | none => false
      | some a => TypedOracleCompiler.Slice.runEntrySmall ⟨x.pol, x.lay, x.KL⟩ a _root_.Fmt.oracle :=
  rfl

/-- A parsed value with the first answer of its further table replaced: by 0, or by 1 where it was
0. Both are canonical. -/
def forged (a : OnBytes.Tie.AskedE) : OnBytes.Tie.AskedE :=
  { a with further := { a.further with answers :=
      match a.further.answers with
      | [] => []
      | e :: l => (if e == ⟨0, 0, 0⟩ then ⟨1, 0, 0⟩ else ⟨0, 0, 0⟩) :: l } }

end Ask.EntryFilesSmall

open Ask.EntryFilesSmall OnBytes.Tie in
#eval show IO Unit from do
  let dir : System.FilePath := ".." / "examples" / "accepted-proof"
  let x : Five :=
    ⟨← IO.FS.readBinFile (dir / "config" / "policy.txt"),
      ← IO.FS.readBinFile (dir / "config" / "layout.txt"),
      ← IO.FS.readBinFile (dir / "config" / "KL.bin"),
      ← IO.FS.readBinFile (dir / "ivk" / "key.bin"),
      ← IO.FS.readBinFile (dir / "ivk" / "leaf" / "0.bin")⟩
  IO.println s!"read, in bytes: policy.txt {x.pol.size}; layout.txt {x.lay.size}; KL.bin \
    {x.KL.size}; key.bin {x.key.size}; leaf/0.bin {x.ent.size}"
  IO.println s!"the premise of runEntryFilesSmall_eq (what is hashed for the digest of the three \
    public files has at most 2 ^ 32 - 144 bytes): {within x}"
  let mut off := if within x then 0 else 1
  let mut n := 0
  for (name, want, y) in sheet x do
    n := n + 1
    let t0 ← IO.monoMsNow
    let value := reads y
    let got := ask y
    IO.println s!"row {n}: {if got == want then "as expected" else "NOT AS EXPECTED"}: \
      {if got then "YES" else "no"}; the reader returned {if value then "a" else "no"} value: \
      {name}"
    let t1 ← IO.monoMsNow
    IO.println s!"  {(t1 - t0) / 1000} s"
    if got != want then off := off + 1
  let t2 ← IO.monoMsNow
  let fit := TypedOracleCompiler.Slice.askedFit smallRecordGround.q.link.table planted
  let got := askPlanted x
  IO.println s!"row {n + 1}: {if fit && !got then "as expected" else "NOT AS EXPECTED"}: \
    {if got then "YES" else "no"}; past the reader; the tests on the parsed value say \
    {if fit then "yes" else "no"}: the closed check at a planted parsed value"
  let t3 ← IO.monoMsNow
  IO.println s!"  {(t3 - t2) / 1000} s"
  if !(fit && !got) then off := off + 1
  match readValue x with
  | none =>
    IO.println s!"row {n + 2}: NOT AS EXPECTED: the reader returned no value to forge"
    off := off + 1
  | some a =>
    let fit' := TypedOracleCompiler.Slice.askedFit smallRecordGround.q.link.table (forged a)
    let got' := TypedOracleCompiler.Slice.runEntrySmall ⟨x.pol, x.lay, x.KL⟩ (forged a) _root_.Fmt.oracle
    IO.println s!"row {n + 2}: {if fit' && !got' then "as expected" else "NOT AS EXPECTED"}: \
      {if got' then "YES" else "no"}; past the reader; the tests on the parsed value say \
      {if fit' then "yes" else "no"}: the closed check at the reader's own value with one answer \
      of the further table replaced"
    let t4 ← IO.monoMsNow
    IO.println s!"  {(t4 - t3) / 1000} s"
    if !(fit' && !got') then off := off + 1
  if off != 0 then throw (IO.userError s!"{off} LINES ARE NOT AS EXPECTED")
  IO.println s!"ALL {n + 2} ROWS ARE AS EXPECTED"
