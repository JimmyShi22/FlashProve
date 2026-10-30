-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/EntryRecord.lean: runs the check of the entry file on the stored examples' real files: «parse,
then the check of the entry file with the hash function an argument». An asking file
(lean/CHECKING.md, «Asking files»), no part of the library: `lake build` does not take it, and
nothing imports it.

Reads: of each stored example six files, by path from the repository's root: under
examples/accepted-proof/ (the small example) and examples/full-size/ (the full size):
config/policy.txt, config/layout.txt, config/KL.bin, ivk/key.bin, ivk/leaf/0.bin, ID.txt. From lean/
they are found as ../examples/…; another folder: ENTRY_EXAMPLES=‹folder›. No proof file and no
request. It writes nothing.

Command: ulimit -s unlimited; LEAN_ABORT_ON_PANIC=1 ENTRY_SIZE=small \
  lake env lean --tstack=1000000 Ask/EntryRecord.lean
(from lean/, behind a build. ENTRY_SIZE=full: the full size; ENTRY_SIZE=both, or unset: both.
ENTRY_PART=honest | controls | fixed runs the lines H | D2 to D6 | C alone, so that the three long
verdicts of the full size can run in three processes side by side; ENTRY_PART=all, or unset: all
lines. Set no tight cap on address space: every thread reserves its whole stack. ENTRY_PLANT=1 lays
a damaged value in the honest one's place, so that one can see the command fail: it must then end
with another code than 0. LEAN_ABORT_ON_PANIC=1 stands in the command so that a panic ends lean at
once; without it a panic inside a control would give the default value false, which counts as a
refusal: then look for a line PANIC in the print. The lines of the sizes are printed together, when
the whole run has ended.)

Takes: the small example: about 5.5 minutes and 5.1 GiB at the peak; the full size: about 37 minutes
in one process (the lines H, D2 and C take 12 minutes each), or about 14 minutes in three processes
side by side, and 6.6 GiB at the peak a process; on one core a process of an AMD EPYC 9R45 (x86-64).
Of that, the test AXIOMS takes about 40 s in every process.

Its print means: first ten messages of `#print axioms`: on what the eight bounds
`verifyEntryFull_copyBound`, `verifyEntrySmall_copyBound` (each also at 2^40, 2^64, 2^80 queries)
and the two equations `runEntryFull_eq`, `runEntrySmall_eq` rest. `AXIOMS`: a test by program that
these ten rest on propext, Classical.choice and Quot.sound alone; else an error. Then, for each size
(a size that ENTRY_SIZE leaves out has one line that says so): `SIZES`: the files' lengths and the
ID as read. `PARSE`: the parser answered. The parser is the library's `keyAt` (the first table, off
the key file) and then its strict converter `convE` (the rest, off the entry file); it is untrusted
and may hash as it likes. `STD`: `Params.stdEntry` at the library's default for that size
(`stdSmall` | `stdFull`, OnBytes/Params/Std.lean): the reader of a parameter file returns that
default's typed lines on policy.txt (what its first 32 lines say), and the bound of line HB holds.
`FIT`: `askedFit` on the parser's value a. `HB`: the three public files are within the bound on
lengths under which the check's two digests are the format's own. `H`: the value that Lean's
evaluator computed for `runEntrySmall` | `runEntryFull` cfg a `Fmt.oracle`
(OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean): cfg: the three public files as they lie in config/;
`Fmt.oracle`: the format's oracle over Lean's own BLAKE2b. By the two equations that is the value of
`verifyEntrySmall` | `verifyEntryFull` cfg a (gOf Fmt.oracle), the check of which the bounds speak.
`D3`, `D4`: the same with one bit of either root turned; `D5`: with one bit of the user's parameter
file turned, the parser's value as before; `D6`: under another hash function (the first bit of every
answer turned); `D2`: on the lenient converter's value of the entry file with one bit turned (if
that converter answers nothing, the check was not tried there, and that counts as a failure). `C`:
`verifyEL` on a at the ID in ID.txt: the form at the fixed hash, with the ID's comparison. `PART`
(under ENTRY_PART alone): which lines were not run. `END`: it names what the lines that ran show,
and is true exactly if STD, FIT and HB are true and, of the lines that ran, H and C are true, D2 was
tried, and none of D2 to D6 is true. Each `took` line is the time of the line above it. The file
throws, so that lean ends with code 1, where an END line is false; where the test AXIOMS fails; and,
with no END line, where a file is missing or cannot be read, a file has more than 2^28 bytes, the
parser refuses, a variable has a word that the file does not know, or ENTRY_PLANT=1 stands with a
part that leaves H out. Else lean ends with 0.

It does not mean: a proof in Lean of any of these values: they are computed by Lean's evaluator over
the library's stored code (not by a native program of this library; Lean's own functions on numbers,
arrays and bytes run natively inside lean), and whoever relies on them trusts Lean's compiler,
evaluator and runtime. Nor soundness of anything: the bounds are over a function drawn at random,
and the run is at one fixed function; no theorem joins the two; and what they bound is not «a yes on
a false statement» (the head of EntryVerdictBound.lean, limits 1 to 3). What the run adds to the
bounds is one thing: the check of which they speak says yes on something. Nor that this check is the
compiler's output: it is written by hand and tied by theorems (the head of EntryVerdictRun.lean).
Nor that cp_verify makes this check; the text of verify-on-bytes imports none of these files. Nor
that the files belong to any commitment ID or request: the check looks at neither (line C alone
compares the ID, and no control tries another ID). Nor that the parameter file is read: the
parameters are typed constants of the library, the files are hashed, and line STD alone compares
what the first 32 lines say with typed lines; so D5 is refused because a digest moves. By the times
that the lines took when this file was run (no theorem says it) D2 alone of the controls reaches the
long part of the check; the other four are refused early. Nor that D2 is refused because of the
turned bit: the lenient converter's value of the unturned entry file is not tried here, and no
theorem says that it is the strict converter's (the head of OnBytes/TypedOracleCompiler/Run/LenientFill.lean). Nor
that any other file is accepted or refused: one honest example a size, on synthetic weights (the
examples' READMEs). Nothing on the key file's or a proof file's checks. And all that the heads of
OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean and EntryVerdictBound.lean do not claim.
-/
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictBound
import OnBytes.TypedOracleCompiler.Slice.EntryRunMain

open OnBytes TypedOracleCompiler.Slice
open OnBytes.Tie (linkAtCfg keyAt)
namespace EntryRecord
def say (s : String) : IO Unit := do IO.eprintln s; (← IO.getStderr).flush
/-- The value is printed, and so computed, before the clock is read again. -/
def timed (tag : String) (f : Unit → Bool) : IO Bool := do
  let t0 ← IO.monoMsNow
  let v := f ()
  say s!"{tag}: {v}"
  let t1 ← IO.monoMsNow
  say s!"    took {t1 - t0} ms"
  return v
def flip (b : ByteArray) (i : Nat) : ByteArray := b.set! i (b.get! i ^^^ 1)
/-- Another hash function on bytes: the format's oracle, the first bit of every answer turned. -/
def other (b : ByteArray) : ByteArray := flip (_root_.Fmt.oracle b) 0
def one (tag : String) (dir : String) (G : OnBytes.Tie.EntryGround) (z : OnBytes.Params.StdSize)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (run : OnBytes.Slice.Shapes.Cfg → OnBytes.Tie.AskedE → (ByteArray → ByteArray) → Bool)
    (plant : Bool) (part : String) : IO Bool := do
  let runH := part == "all" || part == "honest"
  let runD := part == "all" || part == "controls"
  let runC := part == "all" || part == "fixed"
  let pol ← IO.FS.readBinFile (dir ++ "/config/policy.txt")
  let lay ← IO.FS.readBinFile (dir ++ "/config/layout.txt")
  let kl ← IO.FS.readBinFile (dir ++ "/config/KL.bin")
  let key ← IO.FS.readBinFile (dir ++ "/ivk/key.bin")
  let ent ← IO.FS.readBinFile (dir ++ "/ivk/leaf/0.bin")
  let id := (← IO.FS.readFile (dir ++ "/ID.txt")).trimAscii.toString
  say (s!"{tag} | SIZES | policy {pol.size} layout {lay.size} KL {kl.size} key {key.size} " ++
    s!"entry {ent.size} | ID {id}")
  -- the limit on a binary file in verify-on-bytes (OnBytes/Shell/Ask.lean, fileLimit): 2 ^ 28 bytes
  if [pol, lay, kl, key, ent].any (fun b => b.size > 268435456) then
    say s!"{tag} | SIZES | a file has more than 2^28 bytes: refused"; return false
  let cfg : OnBytes.Slice.Shapes.Cfg := ⟨pol, lay, kl⟩
  let c := OnBytes.Params.configurationDigest [pol, lay, kl]
  let hc : c.size = 32 := OnBytes.Params.configurationDigest_size _
  let q := linkAtCfg G.q c
  let first := (keyAt G.q.link.table c key).2.2
  let t0 ← IO.monoMsNow
  match convE q first ent with
  | none => say s!"{tag} | PARSE | the strict converter refuses the honest file"; return false
  | some a =>
    say (s!"{tag} | PARSE | rounds read {a.out.rounds.size}; " ++
      s!"answers {a.first.answers.length} | {a.further.answers.length}")
    say s!"    took {(← IO.monoMsNow) - t0} ms"
    let std : Bool := OnBytes.Params.stdEntry z ⟨pol, lay, kl⟩
    say s!"{tag} | STD | stdEntry at this size's default on the three public files: {std}"
    let fit : Bool := askedFit G.q.link.table a
    say s!"{tag} | FIT | askedFit on the parser's value: {fit}"
    let hb : Bool := decide ((_root_.Fmt.configBytes [pol, lay, kl]).size ≤ 2 ^ 32 - 144)
    say s!"{tag} | HB  | the public files are within the hash's bound on lengths (2^32 - 144): {hb}"
    let aBad : OnBytes.Tie.AskedE :=
      { a with first := { a.first with root := flip a.first.root 0 } }
    let a0 : OnBytes.Tie.AskedE := if plant then aBad else a
    if plant then
      say s!"{tag} | PLANT | a damaged value lies in the honest one's place: this run must fail"
    let h ← if !runH then pure true else
      timed s!"{tag} | H  | the honest value, O := Fmt.oracle" fun _ =>
        run cfg a0 _root_.Fmt.oracle
    let d3 ← if !runD then pure false else
      timed s!"{tag} | D3 | one bit of the first table's root changed" fun _ =>
        run cfg aBad _root_.Fmt.oracle
    let d4 ← if !runD then pure false else
      timed s!"{tag} | D4 | one bit of the copy's root changed" fun _ =>
        run cfg { a with further := { a.further with root := flip a.further.root 0 } }
          _root_.Fmt.oracle
    let d5 ← if !runD then pure false else
      timed s!"{tag} | D5 | one bit of the user's parameter file changed" fun _ =>
        run ⟨flip pol (pol.size / 2), lay, kl⟩ a _root_.Fmt.oracle
    let d6 ← if !runD then pure false else
      timed s!"{tag} | D6 | the honest value under another hash function" fun _ =>
        run cfg a other
    let entBad := flip ent (ent.size / 2)
    let d2 : Option Bool ← if !runD then pure none else match convLax q first entBad with
      | none =>
        say (s!"{tag} | D2 | the lenient converter on the entry file with one bit changed: none: "
          ++ "THE CHECK WAS NOT TRIED HERE: counted as a failure")
        pure none
      | some b => do
        let v ← timed (s!"{tag} | D2 | the lenient converter's value of the entry file with one " ++
          s!"bit of byte {ent.size / 2} changed") (fun _ => run cfg b _root_.Fmt.oracle)
        pure (some v)
    let cc ← if !runC then pure true else
      timed s!"{tag} | C  | verifyEL at the published ID on the honest value" fun _ =>
        verifyEL G hok ⟨id, c, hc⟩ a
    let okD := !runD || (d2 == some false && !d3 && !d4 && !d5 && !d6)
    let ok := std && fit && hb && h && okD && cc
    let said := ["STD, FIT and HB are true"] ++
      (if runH then ["the honest value is accepted"] else []) ++
      (if runD then ["(D2) was tried and no control (D2) to (D6) is accepted"] else []) ++
      (if runC then ["the form at the fixed hash accepts at the ID"] else [])
    let left := (if runH then [] else ["H"]) ++ (if runD then [] else ["D2 to D6"]) ++
      (if runC then [] else ["C"])
    let leftS := ", ".intercalate left
    let saidS := ", ".intercalate said
    unless left.isEmpty do say s!"{tag} | PART | {part}: not run here: {leftS}"
    say s!"{tag} | END | {saidS}: {ok}"
    return ok
end EntryRecord
#print axioms TypedOracleCompiler.Slice.verifyEntryFull_copyBound
#print axioms TypedOracleCompiler.Slice.verifyEntryFull_copyBound_40
#print axioms TypedOracleCompiler.Slice.verifyEntryFull_copyBound_64
#print axioms TypedOracleCompiler.Slice.verifyEntryFull_copyBound_80
#print axioms TypedOracleCompiler.Slice.verifyEntrySmall_copyBound
#print axioms TypedOracleCompiler.Slice.verifyEntrySmall_copyBound_40
#print axioms TypedOracleCompiler.Slice.verifyEntrySmall_copyBound_64
#print axioms TypedOracleCompiler.Slice.verifyEntrySmall_copyBound_80
#print axioms TypedOracleCompiler.Slice.runEntryFull_eq
#print axioms TypedOracleCompiler.Slice.runEntrySmall_eq
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let three := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``TypedOracleCompiler.Slice.verifyEntryFull_copyBound,
      ``TypedOracleCompiler.Slice.verifyEntryFull_copyBound_40,
      ``TypedOracleCompiler.Slice.verifyEntryFull_copyBound_64,
      ``TypedOracleCompiler.Slice.verifyEntryFull_copyBound_80,
      ``TypedOracleCompiler.Slice.verifyEntrySmall_copyBound,
      ``TypedOracleCompiler.Slice.verifyEntrySmall_copyBound_40,
      ``TypedOracleCompiler.Slice.verifyEntrySmall_copyBound_64,
      ``TypedOracleCompiler.Slice.verifyEntrySmall_copyBound_80,
      ``TypedOracleCompiler.Slice.runEntryFull_eq, ``TypedOracleCompiler.Slice.runEntrySmall_eq] do
    let bad := (← liftCoreM (collectAxioms n)).filter fun a => !three.contains a
    unless bad.isEmpty do throwError "EntryRecord: {n} depends on {bad}"
  logInfo "AXIOMS | the ten names above rest on propext, Classical.choice, Quot.sound alone: true"
#eval show IO Unit from do
  let plantW := (← IO.getEnv "ENTRY_PLANT").getD "0"
  unless ["0", "1"].contains plantW do
    throw (IO.userError "EntryRecord: ENTRY_PLANT must be 0 or 1")
  let plant := plantW == "1"
  let part := (← IO.getEnv "ENTRY_PART").getD "all"
  unless ["all", "honest", "controls", "fixed"].contains part do
    throw (IO.userError "EntryRecord: ENTRY_PART must be all, honest, controls or fixed")
  if plant && !(part == "all" || part == "honest") then
    throw (IO.userError "EntryRecord: ENTRY_PLANT=1 wants the line H: ENTRY_PART all or honest")
  let size := (← IO.getEnv "ENTRY_SIZE").getD "both"
  unless ["small", "full", "both"].contains size do
    throw (IO.userError "EntryRecord: ENTRY_SIZE must be small, full or both")
  let ex := (← IO.getEnv "ENTRY_EXAMPLES").getD "../examples"
  let s ← if size == "full" then do
      EntryRecord.say "SMALL | not run here (ENTRY_SIZE=full)"
      pure true
    else
      EntryRecord.one "SMALL" (ex ++ "/accepted-proof") OnBytes.Tie.smallRecordGround
        OnBytes.Params.stdSmall small_record_ok runEntrySmall plant part
  let f ← if size == "small" then do
      EntryRecord.say "FULL | not run here (ENTRY_SIZE=small)"
      pure true
    else
      EntryRecord.one "FULL" (ex ++ "/full-size") OnBytes.Tie.recordGround
        OnBytes.Params.stdFull record_ok runEntryFull plant part
  unless s && f do throw (IO.userError "EntryRecord: NOT AS IT MUST BE: see the lines above")
