-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/VerdictOnFiles.lean: the closed check of an entry file behind the reader that asks:
"read through g, then check" as one function of (public files, files, hash function), with one
function g for the reader and the check, at the two written grounds; and a bound on it over a drawn
function.

Why. OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean bounds an event of the closed checks
`verifyEntryFull` and `verifyEntrySmall` for every maker of a parsed value, and, for makers of
files, at every parser that sees no hash function. The value that these checks are meant to take is
no plain parse of an entry file: the reader hashes (it follows the chain, and it derives both
tables' seeds). Here the value is made of the maker's files after the maker's queries, by a reader
that is answered by the drawn function itself: so the yes is a yes on the bytes of the key file and
the entry file. What is bounded beside that yes is unchanged: it speaks of two strings that are read
off the maker's log, and of no file's bytes. No new probability: the probability is that of
`soundO_full` and `soundO_small` (OnBytes/K/Oracle/ArmOAt.lean), whose event holds this one; new
here is that the event is said of the closed check, as one truth value of (public files, files,
function).

Main names (namespace `OnBytes.K.Oracle`; each also with Small, at the small example):
  `readEntry G cfg g d`: the reader at g: the value at g of the asking half (`askedAt`,
    OnBytes/Tie/EntryAsked.lean) on the key file's table and the entry file, at g's digest of the
    three public files.
  `verifyEntryFilesFull cfg d g`: read at g, then `verifyEntryFull` at g; no where the reader
    returns nothing. `verifyEntryFilesFull_iff`: its yes.
  `EntryLangFull cfg g a σ`: the entry's language (`DecR.LangE`, OnBytes/Slice/DecoderRec.lean) of
    the two strings that are read off the log σ under a's two roots, with the two records in a.
  `EntryFailFilesFull cfg g`: the event, on files and a log: the reader at g makes a value a of the
    files, and a with the log lies in `EntryFailFull cfg g`: a yes on a under g, while that language
    fails. `entryFailFilesFull_iff`: exactly if `verifyEntryFilesFull` says yes and the language
    fails of what the reader returns.
  `verifyEntryFilesFull_yes`: a yes on files, beside any log, lies in the event, or the language
    holds of the value read and that log. By cases alone.
  `verifyEntryFilesFull_copyBound`: for all cfg and every maker of five files with at most t
    queries: the event has probability at most `entryB (2⁻¹)^128 41622 142 fullV t` + t^2 / 2^256
    (small: 26222, 101, `smallV`). `…_copyBound_64`: up to 2^64 queries at most 2^-61.
  `loseO_of_read`: the step, general in the ground.

Who picks what, and when. cfg is bound outside the probability: the statements hold for all cfg, so
public files that anyone picks before the draw are covered, and files picked after asking the
function are not. Then the function is drawn uniformly. Then the maker asks it at most t times and
puts out five files. The maker is fixed before the function is drawn: it takes no advice that
depends on the function (no preprocessing), and its queries are classical. Then the reader and the
check run, answered by the same function. The reader's queries (at most 41,622 | 26,222,
OnBytes/K/Oracle/Counts.lean) and the check's are no part of t: they are counted in the bound. The
two strings are read off the maker's log alone.

The word "reader". It is not a plain, untrusted converter that counts as a prover's last step: it
asks the function, and its questions stand on the verifier's side of the count (in `entryB`, not in
t). For such a converter, with its questions in t: `verifyEntryFull_copyBound`.

How it is proved. At a fixed g the reader at g is a plain function of the files: `entryLose_iff`
(EntryVerdictBound.lean), which holds at every plain function and every g and has no probability in
it, says the event in the terms of the checker "convert, then the judge's run"; under g that checker
returns what the checker that reads through the oracle returns (`HomeData.chk_eq_run`,
`chk_eq_runO`, `tyAt_det`). So at each g the event lies in that checker's bad event, whose reader
is one oracle computation, fixed before the draw; the bound is that event's
(`HomeData.Left.one_worldO`, OnBytes/K/Oracle/Frame.lean; `leftO_full`, `soundO_full`, ArmOAt.lean),
with the statement on codes laid in (`Cb.Bridge.bchks46At`).

Limits.
  1. What is bounded is not "a yes on a false statement". As Limit 1 of EntryVerdictBound.lean says:
     a yes, while the entry's language fails of two strings that are read off THE MAKER's LOG under
     the two roots in the value. Nothing is said where the first string does not decode or its
     record does not single one table out: without the key file's part nothing follows.
  2. Of the key file the reader takes the table's root and answers by a plain parse (`keyAt`,
     OnBytes/Tie/LinkPlain.lean): the key file is not checked. Where it holds no table, a table with
     an empty root and no answers is handed on; a yes is then shut out, at the latest, by the closed
     check's tests on the value (`askedFit`: both roots have 32 bytes). That dropping the three
     tests of the program's reading of a table gives a prover nothing is no theorem (`keyAt`'s own
     words). The three other files are not read.
  3. The reader is a twin of the program's reader, with the hash as an argument
     (OnBytes/K/Oracle/ReaderAt.lean says how the two are tied). The program does not call it. The
     closed check is hand-written after the compiled verifier and tied to it by theorems; it is not
     the entry file's arm of
     Johnson/Top/OnFilesArmsC.lean.
  4. ONE maker makes all files: nothing on a committer who is bound before a prover moves. The
     promise does not chain with the key file's and the proof file's parts. The commitment ID is not
     looked at.
  5. That "read, then check" says yes on any files, under any function, is not shown here: if it
     never did, the events would be empty. (That the language at these two decoders is neither
     everything nor nothing is `guard_full`, `guard_small`, OnBytes/K/Oracle/Decodes.lean; nothing
     ties the strings written there to a log or a file.) The figure is a ceiling of the written
     bound at one budget, and no level of security of any program. It counts, at 6 of the 41 rounds
     (small: at 4 of the 24), 32 of the 128 bits as proof of work (the head of ArmOAt.lean); without
     that credit, by arithmetic outside Lean in the head of OnBytes/TypedOracleCompiler/Slice/EntryFullNum.lean, a
     bound of this form at the full size would read about 2^-29 at that budget. The bound says
     nothing once it reaches 1.
  6. A random function, not the format's hash: no probability is said of any yes at a fixed hash.
     A form for a run at the format's hash: OnBytes/K/Oracle/VerdictOnFilesRun.lean. "No hypothesis
     but the budget" speaks of the statements' binders. The events are not shown measurable here,
     and `Rom.Pr` is a lower integral (Rom/Measure.lean); each lies, at every function, in the event
     whose bound this is. All that the heads of EntryVerdictBound.lean, EntryVerdictRun.lean,
     ArmOAt.lean, ArmO.lean, Frame.lean and ReaderAt.lean do not claim. One file of three. Nothing
     on tokens. Soundness alone.
  7. The bounds of this file stand, through OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean and Cb/Bridge/,
     on lean/ThirdParty/: files adapted from ArkLib and Mathlib (lean/LIMITS.md,
     L15).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.ArmOAt
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictBound

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Oracle
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Slice OnBytes.K.Left
open OnBytes.Tie (EntryGround recordGround smallRecordGround linkAtCfg keyAt AskedE askedAt typedT)
open OnBytes.Slice (GE GF DecR decRec)
open OnBytes.Slice.Shapes (Size Cfg dgOf dgOf_size pubS₀ pubS₁ zFull zSmall rdC)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

/-! ## The reader that asks, and "read, then check", at one function -/

/-- **The reader, at a function g.** Of the five files it reads the key file and the entry file. c
is g's digest of the three public files cfg. The key file's table by a plain parse at c (`keyAt`:
where the file holds no table, a table with an empty root and no answers); then the value, at g, of
the twin of the program's reading of an entry file, and both tables' seeds: every hash is g's
answer. Nothing where the twin refuses. -/
def readEntry (G : EntryGround) (cfg : Cfg) (g : Fam (rom 256)) (d : Slice.Shapes.Files) :
    Option AskedE :=
  askedAt (_root_.Run.oB (g ())) (linkAtCfg G.q (dgOf cfg (own₀ (pubS₀ cfg) g)))
    (keyAt G.q.link.table (dgOf cfg (own₀ (pubS₀ cfg) g)) d.key).2.2 d.ent

/-- **Read, then check, at the full size: a function of (public files, files, hash function).** ONE
g answers the reader and the check. -/
def verifyEntryFilesFull (cfg : Cfg) (d : Slice.Shapes.Files) (g : Fam (rom 256)) : Bool :=
  match readEntry recordGround cfg g d with
  | none => false
  | some a => verifyEntryFull cfg a g

/-- The same at the small example. -/
def verifyEntryFilesSmall (cfg : Cfg) (d : Slice.Shapes.Files) (g : Fam (rom 256)) : Bool :=
  match readEntry smallRecordGround cfg g d with
  | none => false
  | some a => verifyEntrySmall cfg a g

/-- Its yes: the reader returns a value on which the closed check says yes, both at g. -/
theorem verifyEntryFilesFull_iff (cfg : Cfg) (d : Slice.Shapes.Files) (g : Fam (rom 256)) :
    verifyEntryFilesFull cfg d g = true ↔
      ∃ a, readEntry recordGround cfg g d = some a ∧ verifyEntryFull cfg a g = true := by
  unfold verifyEntryFilesFull
  cases readEntry recordGround cfg g d with
  | none => simp
  | some a => simp

/-- Its yes: the reader returns a value on which the closed check says yes, both at g. -/
theorem verifyEntryFilesSmall_iff (cfg : Cfg) (d : Slice.Shapes.Files) (g : Fam (rom 256)) :
    verifyEntryFilesSmall cfg d g = true ↔
      ∃ a, readEntry smallRecordGround cfg g d = some a ∧ verifyEntrySmall cfg a g = true := by
  unfold verifyEntryFilesSmall
  cases readEntry smallRecordGround cfg g d with
  | none => simp
  | some a => simp

/-! ## The events -/

/-- **The entry's language at the full size, of a parsed value a and a log σ, under g**:
`DecR.LangE` (OnBytes/Slice/DecoderRec.lean) of the two strings that are read off σ under a's two
roots, with the two records in a: the first string with its record does not decode, or that record
does not single one table out, or the second string with its own record decodes to a table that
agrees with the first's before the pads, and its record singles one out. g comes in through its
values at the two public strings alone. -/
def EntryLangFull (cfg : Cfg) (g : Fam (rom 256)) (a : AskedE) (σ : Trace (rom 256)) : Prop :=
  DecR.LangE (DecR.wayColl (decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s))
    ((xOfAskedC zFull.lg zFull.s a).2.1, anT zFull.v zFull.s (xOfAskedC zFull.lg zFull.s a).1.1)
    ((xOfAskedC zFull.lg zFull.s a).2.2, anT zFull.v zFull.s (xOfAskedC zFull.lg zFull.s a).1.2)
    (rdC zFull cfg (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [recordGround.bytesAt] cfg) g) σ
      (_root_.Run.bytesToDig a.first.root))
    (rdC zFull cfg (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [recordGround.bytesAt] cfg) g) σ
      (_root_.Run.bytesToDig a.further.root))

/-- The event on a parsed value, in these words. By unfolding. -/
theorem entryFailFull_iff (cfg : Cfg) (g : Fam (rom 256)) (a : AskedE) (σ : Trace (rom 256)) :
    (a, σ) ∈ EntryFailFull cfg g ↔
      verifyEntryFull cfg a g = true ∧ ¬ EntryLangFull cfg g a σ :=
  Iff.rfl

/-- **The entry's language at the small example, of a parsed value a and a log σ, under g**:
`DecR.LangE` (OnBytes/Slice/DecoderRec.lean) of the two strings that are read off σ under a's two
roots, with the two records in a: the first string with its record does not decode, or that record
does not single one table out, or the second string with its own record decodes to a table that
agrees with the first's before the pads, and its record singles one out. g comes in through its
values at the two public strings alone. -/
def EntryLangSmall (cfg : Cfg) (g : Fam (rom 256)) (a : AskedE) (σ : Trace (rom 256)) : Prop :=
  DecR.LangE (DecR.wayColl (decRec zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s))
    ((xOfAskedC zSmall.lg zSmall.s a).2.1,
      anT zSmall.v zSmall.s (xOfAskedC zSmall.lg zSmall.s a).1.1)
    ((xOfAskedC zSmall.lg zSmall.s a).2.2,
      anT zSmall.v zSmall.s (xOfAskedC zSmall.lg zSmall.s a).1.2)
    (rdC zSmall cfg (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [smallRecordGround.bytesAt] cfg) g) σ
      (_root_.Run.bytesToDig a.first.root))
    (rdC zSmall cfg (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [smallRecordGround.bytesAt] cfg) g) σ
      (_root_.Run.bytesToDig a.further.root))

/-- The event on a parsed value, in these words. By unfolding. -/
theorem entryFailSmall_iff (cfg : Cfg) (g : Fam (rom 256)) (a : AskedE) (σ : Trace (rom 256)) :
    (a, σ) ∈ EntryFailSmall cfg g ↔
      verifyEntrySmall cfg a g = true ∧ ¬ EntryLangSmall cfg g a σ :=
  Iff.rfl

/-- **The event at the full size, on a maker's FILES and log, under g**: the reader, at g, makes a
value a of the files, and a with the maker's log lies in `EntryFailFull cfg g`
(OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean): the closed check says yes on a under g, and the entry's
language fails of the two strings that are read off the maker's log under a's two roots, with the
two records in a. -/
def EntryFailFilesFull (cfg : Cfg) (g : Fam (rom 256)) :
    Set (Slice.Shapes.Files × Trace (rom 256)) :=
  {x | ∃ a, readEntry recordGround cfg g x.1 = some a ∧ (a, x.2) ∈ EntryFailFull cfg g}

/-- The same at the small example. -/
def EntryFailFilesSmall (cfg : Cfg) (g : Fam (rom 256)) :
    Set (Slice.Shapes.Files × Trace (rom 256)) :=
  {x | ∃ a, readEntry smallRecordGround cfg g x.1 = some a ∧ (a, x.2) ∈ EntryFailSmall cfg g}

/-- The event, with the truth value in it: files and log lie in it exactly if "read, then check"
says yes on the files under g and the language fails of whatever the reader returns, with that
log. -/
theorem entryFailFilesFull_iff (cfg : Cfg) (g : Fam (rom 256))
    (x : Slice.Shapes.Files × Trace (rom 256)) :
    x ∈ EntryFailFilesFull cfg g ↔
      verifyEntryFilesFull cfg x.1 g = true ∧
        ∀ a, readEntry recordGround cfg g x.1 = some a → ¬ EntryLangFull cfg g a x.2 := by
  constructor
  · rintro ⟨a, ha, hy, hl⟩
    refine ⟨(verifyEntryFilesFull_iff cfg x.1 g).2 ⟨a, ha, hy⟩, fun a' ha' => ?_⟩
    obtain rfl := Option.some.inj (ha.symm.trans ha')
    exact hl
  · rintro ⟨hy, hl⟩
    obtain ⟨a, ha, hy'⟩ := (verifyEntryFilesFull_iff cfg x.1 g).1 hy
    exact ⟨a, ha, hy', hl a ha⟩

/-- The event, with the truth value in it: files and log lie in it exactly if "read, then check"
says yes on the files under g and the language fails of whatever the reader returns, with that
log. -/
theorem entryFailFilesSmall_iff (cfg : Cfg) (g : Fam (rom 256))
    (x : Slice.Shapes.Files × Trace (rom 256)) :
    x ∈ EntryFailFilesSmall cfg g ↔
      verifyEntryFilesSmall cfg x.1 g = true ∧
        ∀ a, readEntry smallRecordGround cfg g x.1 = some a → ¬ EntryLangSmall cfg g a x.2 := by
  constructor
  · rintro ⟨a, ha, hy, hl⟩
    refine ⟨(verifyEntryFilesSmall_iff cfg x.1 g).2 ⟨a, ha, hy⟩, fun a' ha' => ?_⟩
    obtain rfl := Option.some.inj (ha.symm.trans ha')
    exact hl
  · rintro ⟨hy, hl⟩
    obtain ⟨a, ha, hy'⟩ := (verifyEntryFilesSmall_iff cfg x.1 g).1 hy
    exact ⟨a, ha, hy', hl a ha⟩

/-- **A yes on files, beside any log, lies in the event, or the language holds** of the value read
and that log. By cases alone: it says nothing of how often. -/
theorem verifyEntryFilesFull_yes (cfg : Cfg) (d : Slice.Shapes.Files) (g : Fam (rom 256))
    (σ : Trace (rom 256)) (h : verifyEntryFilesFull cfg d g = true) :
    (d, σ) ∈ EntryFailFilesFull cfg g ∨
      ∃ a, readEntry recordGround cfg g d = some a ∧ EntryLangFull cfg g a σ := by
  obtain ⟨a, ha, hy⟩ := (verifyEntryFilesFull_iff cfg d g).1 h
  by_cases hL : EntryLangFull cfg g a σ
  · exact Or.inr ⟨a, ha, hL⟩
  · exact Or.inl ⟨a, ha, hy, hL⟩

/-- **A yes on files, beside any log, lies in the event, or the language holds** of the value read
and that log. By cases alone: it says nothing of how often. -/
theorem verifyEntryFilesSmall_yes (cfg : Cfg) (d : Slice.Shapes.Files) (g : Fam (rom 256))
    (σ : Trace (rom 256)) (h : verifyEntryFilesSmall cfg d g = true) :
    (d, σ) ∈ EntryFailFilesSmall cfg g ∨
      ∃ a, readEntry smallRecordGround cfg g d = some a ∧ EntryLangSmall cfg g a σ := by
  obtain ⟨a, ha, hy⟩ := (verifyEntryFilesSmall_iff cfg d g).1 h
  by_cases hL : EntryLangSmall cfg g a σ
  · exact Or.inr ⟨a, ha, hL⟩
  · exact Or.inl ⟨a, ha, hy, hL⟩

/-! ## From the check's yes on the reader's value to the checker that reads through the oracle -/

section
variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- At a ground whose description is in order at every digest of 32 bytes (hok) and whose pins fit
at every digest (hpins), at every g: where the reader at g makes a of the files, the check says yes
on a under g, and the entry's language fails of the two strings read off the log, files and log lie
in the bad event of the checker that reads through the oracle (`HomeData.LoseO`,
OnBytes/K/Oracle/Frame.lean, at `readerOf`). -/
theorem loseO_of_read (eM : ℕ) (cfg : Cfg) (εs : ℝ≥0∞) (Bk : ℕ)
    (hpins : ∀ c, pinsFit (entryXD G c) G.q.link.table = true) (g : Fam (rom 256))
    (x : Slice.Shapes.Files × Trace (rom 256)) (a : AskedE) (ha : readEntry G cfg g x.1 = some a)
    (hy : verifyEntryG G hok cfg a g = true)
    (hl : ¬ DecR.LangE (DecR.wayColl (decRec (groundSize G eM).T (groundSize G eM).v
            (groundSize G eM).eM (groundSize G eM).lg (groundSize G eM).s))
          ((xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).2.1,
            anT (groundSize G eM).v (groundSize G eM).s
              (xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).1.1)
          ((xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).2.2,
            anT (groundSize G eM).v (groundSize G eM).s
              (xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).1.2)
          (rdC (groundSize G eM) cfg (own₀ (pubS₀ cfg) g)
            (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g) x.2
            (_root_.Run.bytesToDig a.first.root))
          (rdC (groundSize G eM) cfg (own₀ (pubS₀ cfg) g)
            (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g) x.2
            (_root_.Run.bytesToDig a.further.root))) :
    x ∈ HomeData.LoseO (readerOf G hok eM cfg) εs Bk g := by
  obtain ⟨o, r₀, r₁, ho, hr, hl'⟩ := (entryLose_iff G hok eM (readEntry G cfg g) cfg εs Bk
    (rdC (groundSize G eM) cfg) hpins g x).2 ⟨a, ha, hy, hl⟩
  refine ⟨o, r₀, r₁, ?_, hr, hl'⟩
  have ho' : ((((homeOf G hok eM).spec cfg ((homeOf G hok eM).convOf cfg
      (convRd G hok eM (readEntry G cfg g))) εs Bk).toO (pubS₀ cfg)
      (pubS₁ [(homeOf G hok eM).prm] cfg) (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g)).chk x.1).det g = some o := ho
  rw [HomeData.chk_eq_run] at ho'
  obtain ⟨o', h1, h2⟩ := Option.bind_eq_some_iff.1 ho'
  have h1' := (Option.filter_eq_some_iff.1 h1).1
  have hty : ((readerOf G hok eM cfg).ty (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g) x.1).det g = some o' := by
    show (tyAt G hok eM (dgOf cfg (own₀ (pubS₀ cfg) g)) (dgOf_size cfg (own₀ (pubS₀ cfg) g))
      x.1).det g = some o'
    rw [tyAt_det]
    exact h1'
  show (((HomeData.specO (readerOf G hok eM cfg) εs Bk).toO (pubS₀ cfg)
      (pubS₁ [(homeOf G hok eM).prm] cfg) (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g)).chk x.1).det g = some o
  rw [HomeData.chk_eq_runO, hty]
  exact h2

end

/-! ## The bounds -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The event on files lies in the bad event of the checker that reads through the oracle. -/
theorem entryFailFilesFull_sub (cfg : Cfg) (g : Fam (rom 256))
    (x : Slice.Shapes.Files × Trace (rom 256)) (hx : x ∈ EntryFailFilesFull cfg g) :
    x ∈ HomeData.LoseO (readerOf recordGround record_ok Params.recordRadius cfg)
      (((2 : ℝ≥0∞)⁻¹) ^ 128) 142 g := by
  obtain ⟨a, ha, hy, hl⟩ := hx
  exact loseO_of_read recordGround record_ok Params.recordRadius cfg _ 142 record_pins g x a ha
    ((verifyEntryFull_iff cfg a g).1 hy).2 hl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The event on files lies in the bad event of the checker that reads through the oracle. -/
theorem entryFailFilesSmall_sub (cfg : Cfg) (g : Fam (rom 256))
    (x : Slice.Shapes.Files × Trace (rom 256)) (hx : x ∈ EntryFailFilesSmall cfg g) :
    x ∈ HomeData.LoseO (readerOf smallRecordGround small_record_ok Params.smallRecordRadius cfg)
      (((2 : ℝ≥0∞)⁻¹) ^ 128) 101 g := by
  obtain ⟨a, ha, hy, hl⟩ := hx
  exact loseO_of_read smallRecordGround small_record_ok Params.smallRecordRadius cfg _ 101
    small_record_pins g x a ha ((verifyEntrySmall_iff cfg a g).1 hy).2 hl

/-- **THE BOUND ABOUT "READ, THEN CHECK" ON THE FILES, AT THE FULL SIZE.** The three public files
cfg are fixed first; then the function is drawn uniformly; then a maker with at most t queries to it
puts out five files. The reader and the closed check are then answered by that same function. For
all cfg and every such maker the event `EntryFailFilesFull` has probability at most
`entryB (2⁻¹)^128 41622 142 fullV t` + t^2 / 2^256: the reader's at most 41,622 queries are counted
in the bound and are no part of t; the two strings are read off the maker's log alone. No hypothesis
but the maker's budget; the statement on codes is laid in (`Cb.Bridge.bchks46At`). -/
theorem verifyEntryFilesFull_copyBound (cfg : Cfg) (A : OComp (rom 256) Slice.Shapes.Files) (t : ℕ)
    (hq : A.QueryBound t) :
    Rom.Pr A.withTrace (EntryFailFilesFull cfg) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 41622 142 fullV t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [← record_count]
  exact le_trans (Rom.Pr_mono _ fun g x hx => entryFailFilesFull_sub cfg g x hx)
    ((leftO_full (Cb.Bridge.bchks46At GF GE) cfg).one_worldO _ A t hq)

/-- **THE BOUND ABOUT "READ, THEN CHECK" ON THE FILES, AT THE SMALL EXAMPLE.** As at the full size;
the reader asks at most 26,222 strings. -/
theorem verifyEntryFilesSmall_copyBound (cfg : Cfg) (A : OComp (rom 256) Slice.Shapes.Files) (t : ℕ)
    (hq : A.QueryBound t) :
    Rom.Pr A.withTrace (EntryFailFilesSmall cfg) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 26222 101 smallV t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [← small_record_count]
  exact le_trans (Rom.Pr_mono _ fun g x hx => entryFailFilesSmall_sub cfg g x hx)
    ((leftO_small (Cb.Bridge.bchks46At GF GE) cfg).one_worldO _ A t hq)

/-- At the full size, up to 2^64 queries of the maker: at most 2^-61. A ceiling of the written
bound. -/
theorem verifyEntryFilesFull_copyBound_64 (cfg : Cfg) (A : OComp (rom 256) Slice.Shapes.Files)
    (t : ℕ) (hq : A.QueryBound t) (ht : t ≤ 2 ^ 64) :
    Rom.Pr A.withTrace (EntryFailFilesFull cfg) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61 :=
  le_trans (Rom.Pr_mono _ fun g x hx => entryFailFilesFull_sub cfg g x hx)
    (soundO_full (Cb.Bridge.bchks46At GF GE) cfg A t hq ht)

/-- At the small example, up to 2^64 queries of the maker: at most 2^-61. A ceiling of the written
bound. -/
theorem verifyEntryFilesSmall_copyBound_64 (cfg : Cfg) (A : OComp (rom 256) Slice.Shapes.Files)
    (t : ℕ) (hq : A.QueryBound t) (ht : t ≤ 2 ^ 64) :
    Rom.Pr A.withTrace (EntryFailFilesSmall cfg) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61 :=
  le_trans (Rom.Pr_mono _ fun g x hx => entryFailFilesSmall_sub cfg g x hx)
    (soundO_small (Cb.Bridge.bchks46At GF GE) cfg A t hq ht)

end OnBytes.K.Oracle

#print axioms OnBytes.K.Oracle.verifyEntryFilesFull_iff
#print axioms OnBytes.K.Oracle.verifyEntryFilesSmall_iff
#print axioms OnBytes.K.Oracle.entryFailFilesFull_iff
#print axioms OnBytes.K.Oracle.entryFailFilesSmall_iff
#print axioms OnBytes.K.Oracle.verifyEntryFilesFull_yes
#print axioms OnBytes.K.Oracle.verifyEntryFilesSmall_yes
#print axioms OnBytes.K.Oracle.loseO_of_read
#print axioms OnBytes.K.Oracle.verifyEntryFilesFull_copyBound
#print axioms OnBytes.K.Oracle.verifyEntryFilesSmall_copyBound
#print axioms OnBytes.K.Oracle.verifyEntryFilesFull_copyBound_64
#print axioms OnBytes.K.Oracle.verifyEntryFilesSmall_copyBound_64
