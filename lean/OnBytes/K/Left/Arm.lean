-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/Arm.lean: THE ENTRY FILE: TWO STATEMENTS ON ONE CHECKER, which has one form for each
way of reading the files (each converter). Where the parameter file has the setting's lines, the
Lean verifier program's exit code 0 is that checker's yes at the format's hash, AT THE CONVERTER
THAT GOES THROUGH THE PROGRAM's OWN READER. At every converter the checker is sound over a random
oracle, under a hypothesis on codes; AT THAT CONVERTER THIS SAYS NEXT TO NOTHING: it has its force
at a converter that only parses, which is not written. NO THEOREM CARRIES THE PROBABILITY TO THE
PROGRAM's YES. (For a checker with one form, whose reader asks the oracle:
OnBytes/K/Oracle/ArmOAt.lean.)

WHAT THIS IS NOT, FIRST. It is no road from an exit code to a probability: nothing here says how
likely it is that the program's yes is wrong, and NO BOUND STANDS ON THE PROGRAM's OWN CHECK of an
entry file. It is not `innerCompiledVerifier_sound` and none of its three shares. It speaks of ONE of the three
files that a verification reads, the entry file, which links a stored copy of the committed table to
the table under the commitment ID; alone it says nothing on weights, on a request or on a reply, and
without the key file's part nothing follows from it. The checker is made by A SECOND FORM OF THE
COMPILER (OnBytes/TypedOracleCompiler/Compile), with A HAND-WRITTEN STEP FOR THE SEEDS in front; it is not the
library's compiler's and not `innerCompiledVerifier`.

What it is. `EntryArm`: two statements, and that they speak of one checker, at each of two sizes.
 `zero` WHERE THE PARAMETER FILE HAS THE SETTING's LINES, EXIT CODE 0 OF THE LEAN VERIFIER PROGRAM
     IS A YES OF THE CHECKER ON THE CALL's OWN FILES. If a call of this tree's program
     verify-on-bytes ends with exit code 0, it was a call to verify, with an ID, whose eight reads
     were answered with the bytes F (`CallRead`: the clauses of `main_zero_port`,
     OnBytes/K/Top.lean), and the program's own checks said yes at two tables (`PortYesAt`). If F's
     parameter file has the setting's lines (`SaysLines`: one decidable equation on that file), then
     the checker AT THE STRICT CONVERTER, which goes through the program's own reader, returns a
     typed value o ON F's KEY FILE AND ENTRY FILE, under the oracle made from the format's hash; o's
     two roots and both tables' answers are those of the two tables of the program's own yes (the
     first comes from its check of the key file; the further one it hands on to its check of the
     proof file); the user's ID in its normal form (64 hexadecimal signs, A to F lowered, as the
     program reads it) is the commitment ID that the format makes of o's first root, first seeds
     and first answers; and the checker at every converter that makes o returns o.
 `sound` THE CHECKER IS SOUND, AT EVERY CONVERTER. The three public files, the converter and the
     maker are fixed first. Then, over one uniformly random oracle, for a maker of files with at
     most t queries, t up to 2^64: with probability at most 2^-61 the checker returns a value while
     the entry's language fails of the two strings that are read off the maker's log under that
     value's two roots, with its records (`EntryLose`, OnBytes/TypedOracleCompiler/Slice/EntryOne.lean): the first
     string decodes with its record, its record singles one table out, and the second does not
     decode to a table that agrees with the first's before the pads, or its record does not single
     one out. A maker may ask in any order: one that asks a table's seeds late is paid for by a
     factor 5 on the count of queries, the checker's own among them, inside the bound.
 `same` IT IS ONE CHECKER. At every converter, files with a log lie in the event of `sound`, taken
     at the format's hash, IF AND ONLY IF the checker of `zero`, at that converter, returns on them
     a value with two roots of which the entry's language fails, read off that log. So where the
     checker returns o at the format's hash, then for every log the files with that log lie in that
     very event, or the language holds of what is read off the log under o's roots
     (`HomeData.lose_or_lang`). It carries no probability. IT IS NO THIRD RESULT: it holds of every
     such checker, at every converter, with no hypothesis, by unfolding alone; what it adds is
     Lean's word that the term in `Returns` is the term in the event.
 `entry_arm_of_left_small`, `entry_arm_of_left_full` these, at the small example's and the full
     size's typed parameters, from `EntryLeft` (a theorem in OnBytes/K/Left/ArmAt.lean) and the
     hypothesis on codes.
 `EntryLeft` the left half as a statement: the program's yes gives the trusted function's yes on
     what the strict converter makes of the call's own files, at the ID's normal form.
 `returns_of_verifyE`, `zero_of_left`, `prepE_ok`, `convPlay_of_convE`, `HomeData.lose_or_lang`,
     `soundAt_congr` the steps.

THE HYPOTHESIS ON CODES. `Cb.BCHKS46At GF GE` (Cb/Gen/CodeListRSAt.lean): a statement on
Reed-Solomon codes up to the Johnson radius, a hypothesis of these theorems, proved in none of these
files (`Cb.Gl.bchks46At`, Cb/Bridge/GlCodesProved.lean, proves it from the files under
lean/ThirdParty/, on which nothing is said here); it speaks of all lengths, degrees, radii and point
sets, and one false instance anywhere would empty `sound`. Only `sound` uses it.
(OnBytes/K/Left/ArmAtInst.lean [not in this library] has a finite list of its instances in its
place.)

THE SETTING. The sizes, radii and rounds are typed values: every group up to the Johnson radius;
proof of work before every draw of positions, and nowhere else (6 of the 41 rounds, 4 of the 24); a
stored table with a record. They are held against a copy of the first 32 lines of one example
parameter file and a copy of another by tests that Lean's evaluator runs
and that are not in this library, outside these
theorems. That they are a release's default is not said in Lean. That a parameter file has these
lines is evaluated in this file of no file; OnBytes/K/Left/TestSaysLines.lean proves it, by the
kernel's evaluation, of copies of the first 32 lines of two example parameter files, and
OnBytes/K/Left/SaysLinesPrefix.lean of every byte string that begins with one of these copies.

WHAT JOINS `zero` AND `sound` IS NO THEOREM, AND IT IS MORE THAN TAKING THE FIXED HASH FOR A DRAWN
ORACLE. No theorem here has both a call and a probability in it. AT THE STRICT CONVERTER ITSELF
`sound` SAYS NEXT TO NOTHING: that converter hashes by the fixed hash, so under a drawn oracle the
checker returns all but never (by reading the converter's text; no theorem says it). The bound has
its force at a converter that only parses, with the maker doing the hashing through the oracle;
none has been written, and the strict converter's own evaluations of the hash would then count
among the maker's queries and stand in its log. `sound` concludes of strings read off a maker's log;
in `zero` there is no maker and no log. `zero` is shown at one oracle, the format's hash, not for
every oracle.

What else is not claimed. NO CALL IS SHOWN TO END WITH EXIT CODE 0, and that the checker returns a
value on any files is no theorem. (Runs by Lean's evaluator are evidence beside this file, not part
of it.) THE ID STANDS IN `zero` ALONE, at the fixed hash: the event of `sound` names no ID, and that
an ID fixes a table is not in these statements. THE FIGURE is a ceiling of this bound, for this
checker: no level of security of any program. It counts 32 of the 128 bits as proof of work in the
rounds named above, at one query a try; without that credit the bound is far weaker
(OnBytes/TypedOracleCompiler/Slice/EntryFullNum.lean). A query is one call of the oracle on a whole string. THE WAYS
OUT: nothing is said where the first string does not decode or its record does not single one table
out; agreement is before the pads alone; under a root of which the log holds nothing the string read
is zeros. That a table made by the format's own encoder decodes
IS NOT SHOWN
for the decoder with a
record of which this language speaks; where it did not, `sound` would say nothing of such tables.
That the programs write their tables with that encoder is compared in no Lean file of this tree. OF
THE PROGRAM's CHECKS OF THE KEY FILE AND OF THE PROOF FILE nothing is shown here but that they ran
at these two tables. EXIT CODE 0 IS GIVEN FOR `YES` AND FOR `WITHIN LIMITS` ALIKE. The Lean program
is meant, not the C++ one; that this tree's program is the one in a release that a person holds is
said by no sum here. The step from an exit code to `zero` rests on Lean's model of input and output
(OnBytes/Shell); Lean's compiler, its run-time and the C compiler are trusted. Nothing on refusals.
Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Top
import OnBytes.TypedOracleCompiler.Slice.EntryVerdict
import OnBytes.TypedOracleCompiler.Slice.EntryTop

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Left
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Slice
open OnBytes.Tie (EntryGround recordGround smallRecordGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (GE GF s0Of DecR decRec)
open OnBytes.Slice.Shapes (Size Cfg dgOf pubS₀ pubS₁ zFull zSmall rdC)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open scoped ENNReal

/-- The three public files of a call. -/
abbrev cfgOf (F : Files) : Cfg := ⟨F.pol, F.lay, F.KL⟩

/-- The digest of the three public files of a call. -/
abbrev digOf (F : Files) : ByteArray := Params.configurationDigest [F.pol, F.lay, F.KL]

/-- The other five files of a call, as the checker's frame has them. -/
def filesOf (F : Files) : OnBytes.Slice.Shapes.Files :=
  { key := F.key, ent := F.ent, prf := F.proof, req := F.request, reply := F.y }

/-- **What the exit code 0 says of the call itself** (`main_zero_port`, OnBytes/K/Top.lean): the
arguments are `verify`, five names and options that hold `-id` and, right behind it, the ID; the
program's operations gave eight reads that were answered with the bytes F; the options hold the ID
and the bits 128. -/
def CallRead (args : List String) (s s' : World) (F : Files) (id : String) : Prop :=
  ∃ (config ivk request y proof : String) (a : Asked) (t : List Event) (pre post : List String),
    args = "verify" :: config :: ivk :: request :: y :: proof ::
      (pre ++ "-id" :: id :: post) ∧
    kindOf args = .whole config ivk request y proof a ∧
    Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
      (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
      (.bytes F.ent) ++ t) s s' ∧
    a.options.id = some id ∧ a.options.bits = 128

/-- **THE LEFT HALF, AS A STATEMENT**: where the Lean verifier program says yes on a call whose
parameter file has the ground's lines: the ID that the user typed has a normal form nid (64
hexadecimal signs, A to F lowered, as the program reads it); THE BYTES' SIDE OF A RUN AT THE STRICT
CONVERTER, which goes through the program's own reader, returns on the call's own files a plain
value a that holds the two tables of the program's yes; and the entry's trusted function says yes
on a, at nid and the digest of the three public files. -/
def EntryLeft (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (zS : Params.StdSize) : Prop :=
  ∀ (F : Files) (id : String) (table further : Params.TableName),
    PortYesAt F id table further → G.SaysLines F.pol →
      ∃ (a : AskedE) (nid : String), Model.Verify.idAsked id = some nid ∧ a.first = table ∧
        a.further = further ∧
        prepE G zS false F.pol F.lay F.KL F.key F.ent =
          .ok ⟨digOf F, Params.configurationDigest_size _, linkAtCfg G.q (digOf F), a⟩ ∧
        verifyE G hok ⟨nid, digOf F, Params.configurationDigest_size _⟩ a = true

/-- **The entry's language of what is read off a log σ, at the format's hash**, under two roots,
with the two records in the typed value o. -/
def _root_.TypedOracleCompiler.Slice.HomeData.LangAt {z : Size} {d₁ : Sd1 z.lg z.s}
    [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁) (cfg : Cfg) (o : H.OutB cfg)
    (σ : Trace (rom 256)) (r₀ r₁ : _root_.Iop.Dig 256) : Prop :=
  DecR.LangE (DecR.wayColl (decRec z.T z.v z.eM z.lg z.s)) (recE₀ z.T z.v z.eM (anT z.v z.s) o)
    (recE₁ z.T z.v z.eM (anT z.v z.s) o)
    (rdC z cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits) σ r₀)
    (rdC z cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits) σ r₁)

/-- **IT IS ONE CHECKER.** Where the checker at a converter returns o on the files d at the format's
hash, with the roots r₀, r₁, then for every log σ: d with σ lies in the bad event at that converter,
taken at the format's hash, or the entry's language holds of what is read off σ under r₀ and r₁. -/
theorem _root_.TypedOracleCompiler.Slice.HomeData.lose_or_lang {z : Size} {d₁ : Sd1 z.lg z.s}
    [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁) (cfg : Cfg) (Bk : ℕ) (conv : H.Conv cfg)
    (d : OnBytes.Slice.Shapes.Files) (o : H.OutB cfg) (r₀ r₁ : _root_.Iop.Dig 256)
    (h : H.Returns cfg Bk conv d o) (hr : o.1 = [r₀, r₁]) (σ : Trace (rom 256)) :
    (d, σ) ∈ H.Lose cfg Bk conv _root_.Run.oBits ∨ H.LangAt cfg o σ r₀ r₁ := by
  by_cases hL : H.LangAt cfg o σ r₀ r₁
  · exact Or.inr hL
  · exact Or.inl ⟨o, r₀, r₁, h, hr, hL⟩

/-- **TWO STATEMENTS ON THE ENTRY FILE's CHECKER AT ONE SIZE, AND THAT THEY SPEAK OF ONE CHECKER.**
k₀: the strict converter. -/
structure EntryArm (G : EntryGround) {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)]
    (H : HomeData z d₁) (k₀ : H.ConvC) (Bk : ℕ) : Prop where
  /-- **WHERE THE PARAMETER FILE HAS THE SETTING's LINES, EXIT CODE 0 OF THE LEAN VERIFIER PROGRAM
  IS A YES OF THE CHECKER ON THE CALL's OWN FILES.**
  If a call ends with exit code 0, then it was a call to verify, with an ID, that read the files F;
  and if F's parameter file has the ground's lines, the checker AT THE STRICT CONVERTER returns a
  typed value o ON F's KEY FILE AND ENTRY FILE, under the oracle made from the format's hash; o's
  TWO ROOTS AND BOTH TABLES' ANSWERS ARE THOSE OF THE TWO TABLES OF THE PROGRAM's OWN YES
  (the first from its check of the key file; the further one it hands on to its check of the proof
  file); the user's ID, in its normal form (64 hexadecimal signs, A to F lowered),
  is the commitment ID that the format makes of o's first root, first seeds and first answers; and
  the checker at every converter that makes o returns o. -/
  zero : ∀ (args : List String) (s s' : World), Shell.Run (_root_.main args) s 0 s' →
    ∃ (F : Files) (id : String) (table further : Params.TableName), CallRead args s s' F id ∧
      PortYesAt F id table further ∧
      (G.SaysLines F.pol →
        ∃ o : H.OutB (cfgOf F),
          H.Returns (cfgOf F) Bk (H.convOf (cfgOf F) k₀) (filesOf F) o ∧
          o.1 = [_root_.Run.bytesToDig table.root, _root_.Run.bytesToDig further.root] ∧
          o.2.1.1 = (table.answers.map E.triple, further.answers.map E.triple) ∧
          Model.Verify.idAsked id =
            some (stmtId G.q.link.table (digOf F) (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1) ∧
          ∀ (conv' : H.Conv (cfgOf F)) (d' : OnBytes.Slice.Shapes.Files),
            conv' (own₀ (pubS₀ (cfgOf F)) _root_.Run.oBits)
              (own₁ (pubS₀ (cfgOf F)) (pubS₁ [H.prm] (cfgOf F)) _root_.Run.oBits) d' = some o →
            H.Returns (cfgOf F) Bk conv' d' o)
  /-- **THE CHECKER IS SOUND, AT EVERY CONVERTER.** Over one uniformly random oracle, for every
  three public files, every converter and every maker of files with at most t queries, t up to 2^64:
  the checker returns a value while the entry's language fails of the two strings that are read off
  the maker's log under that value's roots, with its records, with probability at most 2^-61. This
  is said under the hypotheses that stand in the statement itself, which this comment does not list;
  it is no claim that they hold. -/
  sound : ∀ (cfg : Cfg) (conv : H.Conv cfg) (A : OComp (rom 256) OnBytes.Slice.Shapes.Files)
    (t : ℕ), A.QueryBound t → t ≤ 2 ^ 64 →
      Rom.Pr A.withTrace (H.Lose cfg Bk conv) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61
  /-- **IT IS ONE CHECKER**: the checker of `zero` is the checker in the event of `sound`. At every
  converter, files with a log lie in that event, taken at the format's hash, if and only if the
  checker at that converter returns on them a value with two roots of which the entry's language
  fails, read off that log. No probability stands here, and it is no third result: it holds of every
  such checker, with no hypothesis, by unfolding alone. -/
  same : ∀ (cfg : Cfg) (conv : H.Conv cfg) (d : OnBytes.Slice.Shapes.Files) (σ : Trace (rom 256)),
    (d, σ) ∈ H.Lose cfg Bk conv _root_.Run.oBits ↔
      ∃ (o : H.OutB cfg) (r₀ r₁ : _root_.Iop.Dig 256),
        H.Returns cfg Bk conv d o ∧ o.1 = [r₀, r₁] ∧ ¬ H.LangAt cfg o σ r₀ r₁

section
variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- Where the strict converter makes a, the play's converter makes what is made of a. -/
theorem convPlay_of_convE (eM : ℕ) (c : ByteArray) (hc : c.size = 32)
    (d : OnBytes.Slice.Shapes.Files) (a : AskedE)
    (h : convE (linkAtCfg G.q c) (keyAt G.q.link.table c d.key).2.2 d.ent = some a) :
    convPlay G hok eM false c hc d = valueOf G hok eM a c hc d := by
  unfold convPlay valueOf
  rw [if_neg Bool.false_ne_true, h]
  rfl

/-- What the bytes' side's yes says: the public files pass the test, the digest is theirs, and the
strict converter has made the value. -/
theorem prepE_ok (zS : Params.StdSize) (pol lay kl key ent : ByteArray) (p : PrepE)
    (h : prepE G zS false pol lay kl key ent = .ok p) :
    Params.stdEntry zS ⟨pol, lay, kl⟩ = true ∧ p.c = Params.configurationDigest [pol, lay, kl] ∧
      convE (linkAtCfg G.q p.c) (keyAt G.q.link.table p.c key).2.2 ent = some p.a := by
  unfold prepE at h
  by_cases hs : Params.stdEntry zS ⟨pol, lay, kl⟩ = true
  swap
  · rw [if_neg hs] at h
    cases h
  rw [if_pos hs, if_neg Bool.false_ne_true] at h
  cases hc : convE (linkAtCfg G.q (Params.configurationDigest [pol, lay, kl]))
      (keyAt G.q.link.table (Params.configurationDigest [pol, lay, kl]) key).2.2 ent with
  | none =>
    rw [hc] at h
    cases h
  | some a =>
    rw [hc] at h
    have e := Except.ok.inj h
    subst e
    exact ⟨hs, rfl, hc⟩

/-- **From the trusted function's yes on what the strict converter makes of the files to the
checker's yes on these files**, at a digest c that the oracle's own first table holds. -/
theorem returns_of_verifyE (eM Bk : ℕ) (cfg : Cfg) (id : String)
    (d : OnBytes.Slice.Shapes.Files) (a : AskedE) (c : ByteArray) (h32 : c.size = 32)
    (hc : c = dgOf cfg (own₀ (pubS₀ cfg) _root_.Run.oBits))
    (hpd : own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits
      (s0Of ((homeOf G hok eM).prm c)) = EntryRunTop.pdOf ((homeOf G hok eM).DX c))
    (hcv : convE (linkAtCfg G.q c) (keyAt G.q.link.table c d.key).2.2 d.ent = some a)
    (h : verifyE G hok ⟨id, c, h32⟩ a = true) :
    ∃ o : (homeOf G hok eM).OutB cfg,
      (homeOf G hok eM).Returns cfg Bk ((homeOf G hok eM).convOf cfg (convPlay G hok eM false)) d
        o ∧
      o.1 = [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] ∧
      o.2.1.1 = (a.first.answers.map E.triple, a.further.answers.map E.triple) ∧
      id = stmtId G.q.link.table c (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 ∧
      ∀ (conv' : (homeOf G hok eM).Conv cfg) (d' : OnBytes.Slice.Shapes.Files),
        conv' (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits) d' = some o →
        (homeOf G hok eM).Returns cfg Bk conv' d' o := by
  obtain ⟨hp, o, ho⟩ := verifyE_facts G hok eM ⟨id, c, h32⟩ a h
  have hy := (homeOf G hok eM).yes_of_runX cfg (convPlay G hok eM false) G.q.link.table
    (((2 : ℝ≥0∞)⁻¹) ^ 128) Bk d c h32 hc ⟨rfl, hpd, rfl, salt_of_pinsFit _ _ hp, rfl⟩ h32 o
    ((convPlay_of_convE G hok eM c h32 d a hcv).trans (ho d).1) (ho d).2.1
  obtain ⟨o', ho', hs⟩ := Option.map_eq_some_iff.1 hy
  obtain ⟨hl, ha⟩ := (homeOf G hok eM).any_conv cfg _ (((2 : ℝ≥0∞)⁻¹) ^ 128) Bk _root_.Run.oBits d
    o' ho'
  have h1 : o'.1 = o.1 := congrArg Prod.fst hs
  have h2 : o'.2.1 = o.2.1 := congrArg Prod.snd hs
  obtain ⟨π, -, hπ⟩ := Option.map_eq_some_iff.1 (ho d).1
  have h3 : o.1 = [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] :=
    (congrArg Prod.fst hπ).symm
  have h4 : o.2.1.1 = (a.first.answers.map E.triple, a.further.answers.map E.triple) :=
    (congrArg (fun u => u.2.1.1) hπ).symm
  refine ⟨o', ho', h1.trans h3, (congrArg Prod.fst h2).trans h4, ?_, ha⟩
  rw [h1, h2]
  exact (ho d).2.2

/-- From the left half to the first clause, general in the ground. -/
theorem zero_of_left (zS : Params.StdSize) (eM Bk : ℕ) (hL : EntryLeft G hok zS)
    (args : List String) (s s' : World)
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (F : Files) (id : String) (table further : Params.TableName), CallRead args s s' F id ∧
      PortYesAt F id table further ∧
      (G.SaysLines F.pol →
        ∃ o : (homeOf G hok eM).OutB (cfgOf F),
          (homeOf G hok eM).Returns (cfgOf F) Bk
            ((homeOf G hok eM).convOf (cfgOf F) (convPlay G hok eM false)) (filesOf F) o ∧
          o.1 = [_root_.Run.bytesToDig table.root, _root_.Run.bytesToDig further.root] ∧
          o.2.1.1 = (table.answers.map E.triple, further.answers.map E.triple) ∧
          Model.Verify.idAsked id =
            some (stmtId G.q.link.table (digOf F) (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1) ∧
          ∀ (conv' : (homeOf G hok eM).Conv (cfgOf F)) (d' : OnBytes.Slice.Shapes.Files),
            conv' (own₀ (pubS₀ (cfgOf F)) _root_.Run.oBits)
              (own₁ (pubS₀ (cfgOf F)) (pubS₁ [(homeOf G hok eM).prm] (cfgOf F))
                _root_.Run.oBits) d' = some o →
            (homeOf G hok eM).Returns (cfgOf F) Bk conv' d' o) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, h1, h2, h3, h4, h5, hp⟩ :=
    main_zero_port h
  obtain ⟨table, further, hat⟩ := hp
  refine ⟨F, id, table, further,
    ⟨config, ivk, request, y, proof, a, t, pre, post, h1, h2, h3, h4, h5⟩, hat, fun hs => ?_⟩
  obtain ⟨v, nid, hn, hv1, hv2, hpre, hv⟩ := hL F id table further hat hs
  obtain ⟨hstd, -, hcv⟩ := prepE_ok G zS _ _ _ _ _ _ hpre
  have hb := Params.stdEntry_bytes hstd
  have hpd := (homeOf G hok eM).pd_own₁ (cfgOf F) hb
    (params_le_of_ok _ (hok _ (Params.configurationDigest_size _))) (homeOf_prm G hok eM _)
  obtain ⟨o, h1', h2', h2'', h3', h4'⟩ := returns_of_verifyE G hok eM Bk (cfgOf F) nid (filesOf F) v
    (digOf F) (Params.configurationDigest_size _)
    (OnBytes.Slice.Shapes.dgOf_own₀ (cfgOf F) hb).symm hpd hcv hv
  rw [hv1, hv2] at h2' h2''
  exact ⟨o, h1', h2', h2'', hn.trans (congrArg some h3'), h4'⟩

end

/-- **`EntryArm` at the small example**, from the left half and the hypothesis on
codes. -/
theorem entry_arm_of_left_small (hA : Cb.BCHKS46At GF GE)
    (hL : EntryLeft smallRecordGround small_record_ok Params.stdSmall) :
    EntryArm smallRecordGround homeSmall (convSmall false) 101 where
  zero := zero_of_left smallRecordGround small_record_ok Params.stdSmall
    Params.smallRecordRadius 101 hL
  sound := (entry_top_small hA).sound
  same := fun _ _ _ _ => Iff.rfl

/-- The second statement by itself, at the checker's letters H. -/
def SoundAt {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁)
    (Bk : ℕ) : Prop :=
  ∀ (cfg : Cfg) (conv : H.Conv cfg) (A : OComp (rom 256) OnBytes.Slice.Shapes.Files)
    (t : ℕ), A.QueryBound t → t ≤ 2 ^ 64 →
      Rom.Pr A.withTrace (H.Lose cfg Bk conv) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61

/-- It is carried along an equation of the letters. -/
theorem soundAt_congr {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)]
    (H H' : HomeData z d₁) (e : H = H') (Bk : ℕ) (h : SoundAt H' Bk) : SoundAt H Bk := e ▸ h

/-- **`EntryArm` at the full size**, from the left half and the hypothesis on codes. The
checker's letters are `homeFull` at the run's fixed value (`homeOf_full`,
OnBytes/TypedOracleCompiler/Slice/EntryRunAny.lean: by unfolding). -/
theorem entry_arm_of_left_full (hA : Cb.BCHKS46At GF GE)
    (hL : EntryLeft recordGround record_ok Params.stdFull) :
    EntryArm recordGround (homeOf recordGround record_ok Params.recordRadius)
      (convPlay recordGround record_ok Params.recordRadius false) 142 where
  zero := zero_of_left recordGround record_ok Params.stdFull Params.recordRadius 142 hL
  sound := soundAt_congr _ _ homeOf_full 142 (entry_top_full hA).sound
  same := fun _ _ _ _ => Iff.rfl

end OnBytes.K.Left
