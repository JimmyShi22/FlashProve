-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean: a probability bound about the closed check of an entry
file, over a hash function drawn uniformly at random. Both sizes.

What is bounded is not "a yes on a false statement".

What this file states, assumes and does not show, its terms and its limits in full: the comment on
`verifyEntryFull_copyBound`.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictRun
import OnBytes.K.Left.Pins
import Cb.Bridge.CodeListRSProved
import OnBytes.TypedOracleCompiler.Slice.AskedSection
import Rom.OverOneN
import Rom.EagerLazy
import OnBytes.TypedOracleCompiler.Slice.EntrySmallNum

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX View)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (Tab s0Of decRec GE GF DecR Raw)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁ zFull zSmall rdC)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The event of the entry file's bound, at the converter made of a parser rd, in the terms of the
check: some value a is parsed off the files, the check says yes on it under g, and the entry's
language fails of the two strings that are read off the maker's log under a's two roots, with the
two records in a. -/
theorem entryLose_iff (eM : ℕ) (rd : Files → Option AskedE) (cfg : Cfg) (εs : ℝ≥0∞) (Bk : ℕ)
    (rdL : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX)
    (hpins : ∀ c, pinsFit (entryXD G c) G.q.link.table = true) (g : Fam (rom 256))
    (x : Files × Trace (rom 256)) :
    x ∈ EntryLose (groundSize G eM).T (groundSize G eM).v (groundSize G eM).eM
        (anT (groundSize G eM).v (groundSize G eM).s) ((homeOf G hok eM).at cfg ((homeOf G hok
          eM).convOf cfg (convRd G hok eM rd))) εs
        ((homeOf G hok eM).typ cfg ((homeOf G hok eM).convOf cfg (convRd G hok eM rd)) εs) 0 Bk
          (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) rdL g ↔
      ∃ a, rd x.1 = some a ∧ verifyEntryG G hok cfg a g = true ∧
        ¬ DecR.LangE (DecR.wayColl (decRec (groundSize G eM).T (groundSize G eM).v
            (groundSize G eM).eM (groundSize G eM).lg (groundSize G eM).s))
          ((xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).2.1,
            anT (groundSize G eM).v (groundSize G eM).s
              (xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).1.1)
          ((xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).2.2,
            anT (groundSize G eM).v (groundSize G eM).s
              (xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).1.2)
          (rdL (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g) x.2
            (_root_.Run.bytesToDig a.first.root))
          (rdL (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g) x.2
            (_root_.Run.bytesToDig a.further.root)) := by
  have hP : (homeOf G hok eM).PinsAtG G.q.link.table (dgOf cfg (own₀ (pubS₀ cfg) g)) :=
    ⟨rfl, rfl, salt_of_pinsFit _ _ (hpins _), rfl⟩
  have key := fun o => (homeOf G hok eM).chk_iff_whyG cfg ((homeOf G hok eM).convOf cfg (convRd G
    hok eM rd)) εs Bk g x.1 o G.q.link.table hP
    (dgOf_size cfg (own₀ (pubS₀ cfg) g))
  have shape : ∀ a o, rd x.1 = some a →
      ((homeOf G hok eM).convOf cfg (convRd G hok eM rd)) (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg)
        (pubS₁ [(homeOf G hok eM).prm] cfg) g) x.1 = some o →
      ∃ π, o = ([_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root],
        xOfAskedC _ _ a, ofPS _ _ π) := by
    intro a o hra ho
    have h2 : (rd x.1).bind (fun a => valueOf G hok eM a (dgOf cfg (own₀ (pubS₀ cfg) g))
        (dgOf_size cfg (own₀ (pubS₀ cfg) g)) x.1) = some o := ho
    rw [hra] at h2
    have h3 : valueOf G hok eM a (dgOf cfg (own₀ (pubS₀ cfg) g)) (dgOf_size cfg (own₀ (pubS₀ cfg)
      g)) x.1 = some o := h2
    unfold valueOf at h3
    obtain ⟨π, -, e⟩ := Option.map_eq_some_iff.1 h3
    exact ⟨π, e.symm⟩
  constructor
  · rintro ⟨o, r₀, r₁, ho, hr, hl⟩
    have hk := (key o).1 ho
    have h2 : (rd x.1).bind (fun a => valueOf G hok eM a (dgOf cfg (own₀ (pubS₀ cfg) g))
        (dgOf_size cfg (own₀ (pubS₀ cfg) g)) x.1) = some o := hk.1
    obtain ⟨a, hra, -⟩ := Option.bind_eq_some_iff.1 h2
    have hy : verifyEntryOf G hok rd cfg x.1 g = true :=
      (verifyEntryOf_iff G hok eM rd cfg εs Bk g x.1).2 ⟨hpins _, o, ho⟩
    unfold verifyEntryOf at hy
    rw [hra] at hy
    obtain ⟨π, rfl⟩ := shape a o hra hk.1
    obtain ⟨rfl, rfl⟩ : _root_.Run.bytesToDig a.first.root = r₀ ∧
        _root_.Run.bytesToDig a.further.root = r₁ := by
      have h0 := List.cons.inj hr
      exact ⟨h0.1, (List.cons.inj h0.2).1⟩
    exact ⟨a, hra, hy, hl⟩
  · rintro ⟨a, hra, hy, hl⟩
    have hy' : verifyEntryOf G hok rd cfg x.1 g = true := by
      unfold verifyEntryOf
      rw [hra]
      exact hy
    obtain ⟨-, o, ho⟩ := (verifyEntryOf_iff G hok eM rd cfg εs Bk g x.1).1 hy'
    obtain ⟨π, rfl⟩ := shape a o hra ((key o).1 ho).1
    exact ⟨_, _, _, ho, rfl, hl⟩

/-! ## The bounds about the closed checks -/

/-- The event of the bound at the full size, in the terms of the closed check: a parser rd, three
public files cfg; on a maker's files and log, under g: some value a is parsed off the files, the
closed check says yes on it under g, and the entry's language fails of the two strings that are read
off the maker's log under a's two roots, with the two records in a. -/
def EntryBadFull (rd : Files → Option AskedE) (cfg : Cfg) (g : Fam (rom 256)) :
    Set (Files × Trace (rom 256)) :=
  {x | ∃ a, rd x.1 = some a ∧ verifyEntryFull cfg a g = true ∧
    ¬ DecR.LangE (DecR.wayColl (decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s))
      ((xOfAskedC zFull.lg zFull.s a).2.1, anT zFull.v zFull.s (xOfAskedC zFull.lg zFull.s a).1.1)
      ((xOfAskedC zFull.lg zFull.s a).2.2, anT zFull.v zFull.s (xOfAskedC zFull.lg zFull.s a).1.2)
      (rdC zFull cfg (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [OnBytes.Tie.recordGround.bytesAt] cfg) g) x.2
        (_root_.Run.bytesToDig a.first.root))
      (rdC zFull cfg (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [OnBytes.Tie.recordGround.bytesAt] cfg) g) x.2
        (_root_.Run.bytesToDig a.further.root))}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The bound about the closed check at the full size. The three public files cfg and the parser rd
are fixed first; then the function is drawn uniformly; then a maker with at most t queries to it
puts out the files. For all cfg, every rd and every such maker the event `EntryBadFull` has
probability at most `entryB (2⁻¹)^128 0 142 fullV t` + t^2 / 2^256. No hypothesis is left: the one
on codes is laid in (`Cb.Bridge.bchks46At`). Limits 1 to 6 in the comment on
`verifyEntryFull_copyBound`. -/
theorem verifyEntryFull_bound (cfg : Cfg) (rd : Files → Option AskedE)
    (A : OComp (rom 256) Files) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr A.withTrace (EntryBadFull rd cfg) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 142 fullV t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine le_trans (Rom.Pr_mono _ fun g x hx => ?_)
    (full_one_world (d₁ := d1Run zFull.lg zFull.s) (Cb.Bridge.bchks46At GF GE) cfg
      ((homeOf OnBytes.Tie.recordGround record_ok OnBytes.Params.recordRadius).convOf cfg (convRd
        OnBytes.Tie.recordGround record_ok OnBytes.Params.recordRadius rd)) A t hq)
  obtain ⟨a, hra, hy, hl⟩ := hx
  exact (entryLose_iff OnBytes.Tie.recordGround record_ok OnBytes.Params.recordRadius rd cfg _ 142
    (rdC zFull cfg) OnBytes.K.Left.record_pins g x).2
    ⟨a, hra, ((verifyEntryFull_iff cfg a g).1 hy).2, hl⟩

/-- The event of the bound at the small example, in the terms of the closed check: a parser rd,
three public files cfg; on a maker's files and log, under g: some value a is parsed off the files,
the closed check says yes on it under g, and the entry's language fails of the two strings that are
read off the maker's log under a's two roots, with the two records in a. -/
def EntryBadSmall (rd : Files → Option AskedE) (cfg : Cfg) (g : Fam (rom 256)) :
    Set (Files × Trace (rom 256)) :=
  {x | ∃ a, rd x.1 = some a ∧ verifyEntrySmall cfg a g = true ∧
    ¬ DecR.LangE (DecR.wayColl (decRec zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s))
      ((xOfAskedC zSmall.lg zSmall.s a).2.1, anT zSmall.v zSmall.s (xOfAskedC zSmall.lg zSmall.s
        a).1.1)
      ((xOfAskedC zSmall.lg zSmall.s a).2.2, anT zSmall.v zSmall.s (xOfAskedC zSmall.lg zSmall.s
        a).1.2)
      (rdC zSmall cfg (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [OnBytes.Tie.smallRecordGround.bytesAt] cfg) g) x.2
        (_root_.Run.bytesToDig a.first.root))
      (rdC zSmall cfg (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [OnBytes.Tie.smallRecordGround.bytesAt] cfg) g) x.2
        (_root_.Run.bytesToDig a.further.root))}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The bound about the closed check at the small example. The three public files cfg and the parser
rd are fixed first; then the function is drawn uniformly; then a maker with at most t queries to it
puts out the files. For all cfg, every rd and every such maker the event `EntryBadSmall` has
probability at most `entryB (2⁻¹)^128 0 101 smallV t` + t^2 / 2^256. No hypothesis is left: the one
on codes is laid in (`Cb.Bridge.bchks46At`). Limits 1 to 6 in the comment on
`verifyEntryFull_copyBound`. -/
theorem verifyEntrySmall_bound (cfg : Cfg) (rd : Files → Option AskedE)
    (A : OComp (rom 256) Files) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr A.withTrace (EntryBadSmall rd cfg) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 101 smallV t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine le_trans (Rom.Pr_mono _ fun g x hx => ?_)
    (small_one_world (Cb.Bridge.bchks46At GF GE) cfg
      ((homeOf OnBytes.Tie.smallRecordGround small_record_ok
        OnBytes.Params.smallRecordRadius).convOf cfg (convRd OnBytes.Tie.smallRecordGround
        small_record_ok OnBytes.Params.smallRecordRadius rd)) A t hq)
  obtain ⟨a, hra, hy, hl⟩ := hx
  exact (entryLose_iff OnBytes.Tie.smallRecordGround small_record_ok
    OnBytes.Params.smallRecordRadius rd cfg _ 101 (rdC zSmall cfg) OnBytes.K.Left.small_record_pins
    g x).2
    ⟨a, hra, ((verifyEntrySmall_iff cfg a g).1 hy).2, hl⟩

/-! ## For makers of a parsed value -/

/-- An algorithm whose output is mapped asks no more. -/
theorem queryBound_mapOut {S : OSpec} {α β : Type} (φ : α → β) :
    ∀ {c : OComp S α} {t : ℕ}, c.QueryBound t → (c.bind fun a => OComp.pure (φ a)).QueryBound t
  | .pure _, _, _ => trivial
  | .query _ _ _, 0, h => h.elim
  | .query _ _ _, _ + 1, h => fun r => queryBound_mapOut φ (h r)
  | .sample _ _, _, h => fun r => queryBound_mapOut φ (h r)

/-- An algorithm whose output is mapped has the same log. -/
theorem withTrace_mapOut {S : OSpec} {α β : Type} (c : OComp S α) (φ : α → β) :
    (c.bind fun a => OComp.pure (φ a)).withTrace =
      c.withTrace.bind fun out => OComp.pure (φ out.1, out.2) := by
  rw [Rom.withTrace_bind]
  congr 1
  funext out
  show OComp.pure (φ out.1, out.2 ++ []) = _
  rw [List.append_nil]

/-- The event of the bound at the full size, on a parsed value and its maker's log, under g: the
closed check says yes on the value under g, and the entry's language fails of the two strings that
are read off the log under the value's two roots, with the two records in the value. -/
def EntryFailFull (cfg : Cfg) (g : Fam (rom 256)) : Set (AskedE × Trace (rom 256)) :=
  {y | verifyEntryFull cfg y.1 g = true ∧
    ¬ DecR.LangE (DecR.wayColl (decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s))
      ((xOfAskedC zFull.lg zFull.s y.1).2.1, anT zFull.v zFull.s (xOfAskedC zFull.lg zFull.s
        y.1).1.1)
      ((xOfAskedC zFull.lg zFull.s y.1).2.2, anT zFull.v zFull.s (xOfAskedC zFull.lg zFull.s
        y.1).1.2)
      (rdC zFull cfg (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [OnBytes.Tie.recordGround.bytesAt] cfg) g) y.2
        (_root_.Run.bytesToDig y.1.first.root))
      (rdC zFull cfg (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [OnBytes.Tie.recordGround.bytesAt] cfg) g) y.2
        (_root_.Run.bytesToDig y.1.further.root))}

/-- THE BOUND ABOUT THE CLOSED CHECK AT THE FULL SIZE, FOR EVERY MAKER OF A PARSED VALUE. The three
public files cfg are fixed first; then the function is drawn uniformly; then a maker with at most t
queries to it puts out the parsed value itself: a prover with its parser as its last step, their
queries in one budget. For all cfg and every such maker the event `EntryFailFull` has probability at
most `entryB (2⁻¹)^128 0 142 fullV t` + t^2 / 2^256. No hypothesis is left. Not "a yes on a false
statement": the event speaks of two strings read off the maker's own log under the roots that the
maker named; where the first does not decode with its record, or its record does not single one
table out, nothing is said (limits 1 to 3 below).

This file states: fix the three public files cfg; draw the hash function uniformly at random; let an
algorithm with at most t queries to it put out a parsed entry file. The probability that the closed
check (`verifyEntryFull`, `verifyEntrySmall`, OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean) says yes while
the first table decodes with its record, which singles one table out, and the further table is no
faithful copy of it, both as read off the
algorithm's own log of queries, is at most `entryB (2⁻¹)^128 0 142 fullV t` + t^2 / 2^256 at the
full size and `entryB (2⁻¹)^128 0 101 smallV t` + t^2 / 2^256 at the small example
(`verifyEntryFull_copyBound`, `verifyEntrySmall_copyBound`): at most 2^-85, 2^-61, 2^-45 up to 2^40,
2^64, 2^80 queries (`verifyEntryFull_copyBound_40`, `verifyEntryFull_copyBound_64`,
`verifyEntryFull_copyBound_80`, and the like with Small). `verifyEntryFull_bound` and
`verifyEntrySmall_bound` say the like of algorithms that put out files, behind a parser rd.
`entryLose_iff` says the event of the theorems beneath in the terms of the check `verifyEntryG`
(OnBytes/TypedOracleCompiler/Slice/EntryVerdictG.lean).

It assumes: in the ten bounds no hypothesis beside the budget of queries (hq, and ht in the six
figures). `entryLose_iff` is general in the reference parameters G, a record of data with laws
(`EntryGround`, OnBytes/Tie/EntryGround.lean), and asks two hypotheses on them (hok, hpins). The
bounds' variables are cfg, the algorithm, t and, in two of them, rd. All are fixed before the hash
function is drawn; rd sees no hash function; the algorithm may depend on cfg. The statement on codes
that the theorems beneath assume is used as proved in Cb/Bridge/ over lean/ThirdParty/ (files
adapted from ArkLib and Mathlib (lean/LIMITS.md, L15)):
these files, and all that the proofs call, lie beneath.

It does not show: that a yes on a false statement is unlikely. Nothing is said where the first table
does not decode or its record does not single one table out: so without the key file's part nothing
follows; and "decodes" does not say that the algorithm knew a table. The bound says nothing once it
reaches 1. If the check never said yes the events would be empty, and that it says yes on anything
is shown by no theorem; at an rd that refuses everything the event is empty. The events are not
shown measurable here. The figures count 32 of the 128 bits as proof of work at some rounds (without
that credit, by arithmetic outside Lean, about 2^-53, 2^-29, 2^-13), and are no level of security of
any program. Nothing for public files that are picked after asking the hash function; nothing on a
committer who is bound before a prover moves; the promise is not the one of the arm at the three
files' own object: it does not chain with the key file's and the proof file's parts; a random
function, not the format's hash; the roots, answers and seeds are those that the algorithm named;
the commitment ID is not looked at; one file of three; nothing on tokens. The verifier beneath is
the lax one of Link out of the compiler under OnBytes/TypedOracleCompiler/, a form of the library's.
The limits in full, for every statement of this file:
below.

Terms: lean/GLOSSARY.md. In the comments of this file an "arm" is the check of one file taken as a
protocol, a "ground" is a set of reference parameters typed in Lean, a "maker" is the algorithm that
puts out the value or the files, the "pins" are the constants in the strings that are hashed, "the
judge" is the compiled verifier of the entry file's protocol (`Judge`,
OnBytes/TypedOracleCompiler/Slice/OneWorldJ.lean), and a "run" is an evaluation by Lean's evaluator or of compiled
code. Where a comment of this file names the head of a file, read with it the comment to which that
head points.

THE LIMITS.

OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean: a bound over a uniformly random hash function about the
closed check of an entry file, for every maker of a parsed value, at the two written grounds.

Statements with their proofs, and four definitions of events. `full_one_world` and `small_one_world`
(OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean, EntrySmallTop.lean) bound the event `EntryLose`
(OnBytes/TypedOracleCompiler/Slice/EntryOne.lean) of the checker "convert; two roots; the judge's run", for every
maker of five files and every converter that is fixed before the function is drawn. Here that event,
at the converter "parse by rd, then type" (`convRd`, OnBytes/TypedOracleCompiler/Slice/EntryVerdictRd.lean), is said
in the terms of the check `verifyEntryG`; the two bounds are said about the closed checks
`verifyEntryFull` and `verifyEntrySmall` (OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean), with the
hypothesis on codes laid in; and they are carried from makers of files to makers of a parsed value.

Main names (namespace `TypedOracleCompiler.Slice`):
  `entryLose_iff`: at a ground G whose description is in order at every digest of 32 bytes (hok) and
    whose pins fit at every digest (hpins), every eM, εs, Bk, every reading rdL of a log, every rd,
    cfg, g, files and log: these lie in `EntryLose` at `convRd` exactly if some a is parsed off the
    files, `verifyEntryG` says yes on it under g, and the entry's language (`DecR.LangE`,
    OnBytes/Slice/DecoderRec.lean) fails of the two strings that rdL reads off the log under a's two
    roots, with the two records in a.
  `EntryBadFull rd cfg g`, `EntryBadSmall rd cfg g`: that event with the closed check.
    `verifyEntryFull_bound`, `verifyEntrySmall_bound`: its bound, for every rd and every maker of
    files.
  `EntryFailFull cfg g`, `EntryFailSmall cfg g`: the event on a parsed value and a log: the closed
    check says yes on the value under g, and the entry's language fails as above.
  `verifyEntryFull_copyBound`, `verifyEntrySmall_copyBound`: for all cfg and every maker of a parsed
    value with at most t queries: that event has probability at most
    `entryB (2⁻¹)^128 0 142 fullV t` | `entryB (2⁻¹)^128 0 101 smallV t`, + t^2 / 2^256. No parser,
    no writing into files and no hypothesis stands in the statement. By
    `AskedSection.exists_section` (OnBytes/TypedOracleCompiler/Slice/AskedSection.lean) and the bound for makers of
    files. Why "copy": what is bounded is a yes while the first table decodes and the further is no
    faithful copy of it, both as read off the maker's log; Limit 1 has the cases.
  `verifyEntryFull_copyBound_40` | `_64` | `_80`, and the like small: up to 2^40 | 2^64 | 2^80
    queries at most 2^-85 | 2^-61 | 2^-45 (`entryB_full_40` …, OnBytes/TypedOracleCompiler/Slice/EntryFullNum.lean,
    EntrySmallNum.lean).

Who picks what, and when. cfg is bound outside the probability and before the maker: the bound holds
for all three public files that are fixed before the function is drawn, whoever picks them, and the
maker may depend on them. Files that are picked after asking the function are not covered. The check
parses their text nowhere: it asks the function at the string made of them, and uses that answer
alone; the parameters are the ground's. The maker asks the function and then puts out the parsed
value: a prover with its parser as its last step, their queries in one budget t. The maker is fixed
before the function is drawn: it holds no advice that hangs on the function, and its queries are
classical. The check's own asking is neither in the log nor in t: it stands in `entryB`.

Limits.
  1. What is bounded is not "a yes on a false statement". It is: a yes, while the entry's language
     fails of two strings that are read off THE MAKER's LOG under the two roots in the value. In
     words (the head of EntryOne.lean): the first string decodes with its record, which singles one
     table out, and yet the second does not decode with its own record to a table that agrees with
     the first's before the pads, or its record does not single one out. Nothing is said where the
     first string does not decode or its record does not single one table out: so without the key
     file's part nothing follows. Under a root of which the log holds nothing the reading is a table
     of zeros: "decodes" does not say that the maker knew a table. The reading hangs on g too: the
     log is read at the digest that g gives of the three public files (`rdC`,
     OnBytes/TypedOracleCompiler/Slice/ShapesPub.lean), whether the maker asked for it or not.
  2. ONE maker makes the whole value: nothing on a committer who is bound before a prover moves. The
     promise is not the one of the arm at the three files' own object: it does not chain with
     the key file's and the proof file's parts.
  3. The two roots, both tables' answers and the seeds come out of the value: a yes is a yes for the
     roots and answers that the maker named. The commitment ID is not looked at. That cfg's text is
     the one from which the ground was written is read by no part of the check. The description, the
     sizes, the radii and the decision are the ground's.
  4. In the bounds for makers of files rd is any plain function that sees no hash function; at an rd
     that refuses everything the event is empty. `verifyEntryFull_copyBound` and its like have no
     rd.
  5. The figures are ceilings of the written bound at three budgets; they are no level of security
     of any program. They count, at 6 of the 41 rounds at the full size and at four rounds at the
     small one, 32 of the 128 bits as proof of work, at one query a try; without that credit, by
     arithmetic outside Lean in the heads of OnBytes/TypedOracleCompiler/Slice/EntryFullNum.lean and
     EntrySmallNum.lean, the bound would read about 2^-53, 2^-29, 2^-13 at the three budgets. The
     bound says nothing once it reaches 1. That the closed check says yes on anything is shown by no
     theorem, and is a fact of a run, and this head reports none: if it never did, the events would
     be empty. That the language
     is neither true of every pair of strings nor of none, at the very decoders of the two events,
     is shown (`guard_full`, `guard_small`, OnBytes/K/Oracle/Decodes.lean): of strings and records
     written down there, at one seed written down there (the lemmas beneath: at any seed; none is
     asked to be the function's own), not of strings read off a log. "No hypothesis" speaks of the
     statements' binders: the proofs are as good as the kernel's check, in a build, of all that lies
     beneath, `full_sound` and `small_sound` with what they call among it, much of it by the
     kernel's evaluation. The statement on codes is proved through Cb/Bridge/ over lean/ThirdParty/:
     these files lie beneath too. The four events are not shown measurable here, and `Rom.Pr` is a
     lower integral (Rom/Measure.lean).
  6. The seeds' comparison is written by hand, and Link's verifier is the lax one out of the
     compiler under OnBytes/TypedOracleCompiler/, a form of the library's.
     The closed check is tied to these by theorems, not by its text. All that the
     heads of EntryFullTop.lean, EntrySmallTop.lean, EntryOne.lean and EntryVerdictRun.lean do not
     claim. The tests on the parsed value (`askedFit`) are not used by the bound: it holds of
     `verifyEntryG` alone, by the proofs' road (they drop the tests); no theorem here states that. A
     random function, not the format's hash. One file of three. Nothing on tokens.



-/
theorem verifyEntryFull_copyBound (cfg : Cfg) (Mk : OComp (rom 256) AskedE) (t : ℕ)
    (hq : Mk.QueryBound t) :
    Rom.Pr Mk.withTrace (EntryFailFull cfg) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 142 fullV t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨enc, rd, hs⟩ := AskedSection.exists_section
  have h := verifyEntryFull_bound cfg rd (Mk.bind fun a => OComp.pure (enc a)) t
    (queryBound_mapOut enc hq)
  rw [withTrace_mapOut, Rom.Pr_bind_pure] at h
  refine le_trans (Rom.Pr_mono _ fun g y hy => ?_) h
  exact ⟨y.1, hs y.1, hy.1, hy.2⟩

/-- The event of the bound at the small example, on a parsed value and its maker's log, under g: the
closed check says yes on the value under g, and the entry's language fails of the two strings that
are read off the log under the value's two roots, with the two records in the value. -/
def EntryFailSmall (cfg : Cfg) (g : Fam (rom 256)) : Set (AskedE × Trace (rom 256)) :=
  {y | verifyEntrySmall cfg y.1 g = true ∧
    ¬ DecR.LangE (DecR.wayColl (decRec zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s))
      ((xOfAskedC zSmall.lg zSmall.s y.1).2.1, anT zSmall.v zSmall.s (xOfAskedC zSmall.lg zSmall.s
        y.1).1.1)
      ((xOfAskedC zSmall.lg zSmall.s y.1).2.2, anT zSmall.v zSmall.s (xOfAskedC zSmall.lg zSmall.s
        y.1).1.2)
      (rdC zSmall cfg (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [OnBytes.Tie.smallRecordGround.bytesAt] cfg) g) y.2
        (_root_.Run.bytesToDig y.1.first.root))
      (rdC zSmall cfg (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [OnBytes.Tie.smallRecordGround.bytesAt] cfg) g) y.2
        (_root_.Run.bytesToDig y.1.further.root))}

/-- THE BOUND ABOUT THE CLOSED CHECK AT THE SMALL EXAMPLE, FOR EVERY MAKER OF A PARSED VALUE. The
three public files cfg are fixed first; then the function is drawn uniformly; then a maker with at
most t queries to it puts out the parsed value itself: a prover with its parser as its last step,
their queries in one budget. For all cfg and every such maker the event `EntryFailSmall` has
probability at most `entryB (2⁻¹)^128 0 101 smallV t` + t^2 / 2^256. No hypothesis is left. Not "a
yes on a false statement": the event speaks of two strings read off the maker's own log under the
roots that the maker named; where the first does not decode with its record, or its record does not
single one table out, nothing is said (limits 1 to 3 in the comment on `verifyEntryFull_copyBound`).
-/
theorem verifyEntrySmall_copyBound (cfg : Cfg) (Mk : OComp (rom 256) AskedE) (t : ℕ)
    (hq : Mk.QueryBound t) :
    Rom.Pr Mk.withTrace (EntryFailSmall cfg) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 101 smallV t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨enc, rd, hs⟩ := AskedSection.exists_section
  have h := verifyEntrySmall_bound cfg rd (Mk.bind fun a => OComp.pure (enc a)) t
    (queryBound_mapOut enc hq)
  rw [withTrace_mapOut, Rom.Pr_bind_pure] at h
  refine le_trans (Rom.Pr_mono _ fun g y hy => ?_) h
  exact ⟨y.1, hs y.1, hy.1, hy.2⟩

/-! ## Figures -/

/-- At the full size, up to 2^40 queries: at most 2^-85. A ceiling of the written bound, of the
event of `verifyEntryFull_copyBound`; 32 bits of work are counted (limits 1 and 5 in the comment on
`verifyEntryFull_copyBound`). -/
theorem verifyEntryFull_copyBound_40 (cfg : Cfg) (Mk : OComp (rom 256) AskedE) (t : ℕ)
    (hq : Mk.QueryBound t) (ht : t ≤ 2 ^ 40) :
    Rom.Pr Mk.withTrace (EntryFailFull cfg) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 85 :=
  le_trans (verifyEntryFull_copyBound cfg Mk t hq) (by rw [fullV_eq]; exact entryB_full_40 t ht)

/-- At the full size, up to 2^64 queries: at most 2^-61. A ceiling of the written bound, of the
event of `verifyEntryFull_copyBound`; 32 bits of work are counted (limits 1 and 5 in the comment on
`verifyEntryFull_copyBound`). -/
theorem verifyEntryFull_copyBound_64 (cfg : Cfg) (Mk : OComp (rom 256) AskedE) (t : ℕ)
    (hq : Mk.QueryBound t) (ht : t ≤ 2 ^ 64) :
    Rom.Pr Mk.withTrace (EntryFailFull cfg) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61 :=
  le_trans (verifyEntryFull_copyBound cfg Mk t hq) (by rw [fullV_eq]; exact entryB_full_64 t ht)

/-- At the full size, up to 2^80 queries: at most 2^-45. A ceiling of the written bound, of the
event of `verifyEntryFull_copyBound`; 32 bits of work are counted (limits 1 and 5 in the comment on
`verifyEntryFull_copyBound`). -/
theorem verifyEntryFull_copyBound_80 (cfg : Cfg) (Mk : OComp (rom 256) AskedE) (t : ℕ)
    (hq : Mk.QueryBound t) (ht : t ≤ 2 ^ 80) :
    Rom.Pr Mk.withTrace (EntryFailFull cfg) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 45 :=
  le_trans (verifyEntryFull_copyBound cfg Mk t hq) (by rw [fullV_eq]; exact entryB_full_80 t ht)

/-- At the small example, up to 2^40 queries: at most 2^-85. A ceiling of the written bound, of the
event of `verifyEntrySmall_copyBound`; 32 bits of work are counted (limits 1 and 5 in the comment on
`verifyEntryFull_copyBound`). -/
theorem verifyEntrySmall_copyBound_40 (cfg : Cfg) (Mk : OComp (rom 256) AskedE) (t : ℕ)
    (hq : Mk.QueryBound t) (ht : t ≤ 2 ^ 40) :
    Rom.Pr Mk.withTrace (EntryFailSmall cfg) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 85 :=
  le_trans (verifyEntrySmall_copyBound cfg Mk t hq) (by rw [smallV_eq]; exact entryB_small_40 t ht)

/-- At the small example, up to 2^64 queries: at most 2^-61. A ceiling of the written bound, of the
event of `verifyEntrySmall_copyBound`; 32 bits of work are counted (limits 1 and 5 in the comment on
`verifyEntryFull_copyBound`). -/
theorem verifyEntrySmall_copyBound_64 (cfg : Cfg) (Mk : OComp (rom 256) AskedE) (t : ℕ)
    (hq : Mk.QueryBound t) (ht : t ≤ 2 ^ 64) :
    Rom.Pr Mk.withTrace (EntryFailSmall cfg) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61 :=
  le_trans (verifyEntrySmall_copyBound cfg Mk t hq) (by rw [smallV_eq]; exact entryB_small_64 t ht)

/-- At the small example, up to 2^80 queries: at most 2^-45. A ceiling of the written bound, of the
event of `verifyEntrySmall_copyBound`; 32 bits of work are counted (limits 1 and 5 in the comment on
`verifyEntryFull_copyBound`). -/
theorem verifyEntrySmall_copyBound_80 (cfg : Cfg) (Mk : OComp (rom 256) AskedE) (t : ℕ)
    (hq : Mk.QueryBound t) (ht : t ≤ 2 ^ 80) :
    Rom.Pr Mk.withTrace (EntryFailSmall cfg) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 45 :=
  le_trans (verifyEntrySmall_copyBound cfg Mk t hq) (by rw [smallV_eq]; exact entryB_small_80 t ht)

end TypedOracleCompiler.Slice

#print axioms TypedOracleCompiler.Slice.AskedSection.exists_section
#print axioms TypedOracleCompiler.Slice.entryLose_iff
#print axioms TypedOracleCompiler.Slice.verifyEntryFull_bound
#print axioms TypedOracleCompiler.Slice.verifyEntrySmall_bound
#print axioms TypedOracleCompiler.Slice.verifyEntryFull_copyBound
#print axioms TypedOracleCompiler.Slice.verifyEntrySmall_copyBound
#print axioms TypedOracleCompiler.Slice.verifyEntryFull_copyBound_40
#print axioms TypedOracleCompiler.Slice.verifyEntryFull_copyBound_64
#print axioms TypedOracleCompiler.Slice.verifyEntryFull_copyBound_80
#print axioms TypedOracleCompiler.Slice.verifyEntrySmall_copyBound_40
#print axioms TypedOracleCompiler.Slice.verifyEntrySmall_copyBound_64
#print axioms TypedOracleCompiler.Slice.verifyEntrySmall_copyBound_80
