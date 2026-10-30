-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean: (a) for the entry file at the full size, with no letter left
but one that is bound by "for every", under the one hypothesis on codes.

OnBytes/TypedOracleCompiler/Slice/EntryHome.lean has the entry file's checker "convert by any plain function; refuse
unless there are two roots; the judge's run", its bound for every converter, and the list
`HomeData.Left` of what is left of its debts. OnBytes/TypedOracleCompiler/Slice/EntryHomeFull.lean discharges seven
of the ten fields at the full size (`left_full`). This file discharges the other three and fills the
two letters that were left.

Main definitions.
 `tVOf ds a xs` the bound on the judge's typed queries as a function of a description's rounds,
     depth and stored openings; `fullV`: it at the full size's written rounds: a closed term. Its
     value as a numeral, 13545, is shown in OnBytes/TypedOracleCompiler/Slice/EntryFullV.lean, not here.
 `fullDec` the decision of the Lean port's link (`linkVerify … .decides`), at keys written of the
     instance: not shown to be the keys, or the check, that the port makes of a file.
 `homeFull d₁` the part at the full size: the description `entryXD recordGround`, its parameter
     bytes, `fullDec`, the page's own code behind the escape (`EntryRunTop.backOf`).
Main theorems.
 `EntryAt.tV_of`, `full_count` the field "count".
 `full_sound` the field "sound": soundness record by record, from `fr_row13_joh`
     (OnBytes/TypedOracleCompiler/Slice/EntryRow13JohFull.lean) at the four data of `full_four`, UNDER `Cb.BCHKS46At
     GF GE`.
The field "spells" is `full_spells` (OnBytes/TypedOracleCompiler/Slice/EntrySpells.lean).
`full_one_world` over one uniformly random oracle, for every three configuration files, every
converter and every maker with at most t queries: the event `EntryLose` has probability at most
`entryB (2⁻¹)^128 0 142 fullV t` + t^2 / 2^256.

WHAT KIND OF THEOREM THIS IS. A soundness theorem for a checker written in Lean at a description of
the entry's chain that is ours: the second compiler's lax verifier behind a wrap written by hand. It
is for EVERY converter; no sentence should rest on the instance at one converter.

What is not claimed. `Cb.BCHKS46At GF GE` is a hypothesis: a statement on Reed-Solomon codes that is
taken as given: a hypothesis of these theorems, proved in none of these files (`Cb.Gl.bchks46At`,
Cb/Bridge/GlCodesProved.lean, proves it from the files under lean/ThirdParty/, on which nothing is
said here). It speaks of all lengths, degrees, radii and point sets, while the theorem uses it at
ten triples: ONE FALSE INSTANCE ANYWHERE WOULD EMPTY THE THEOREM. WHICH SETTING: "the full size" is
the ground `recordGround`: typed values of one setting of the parameters, with a record and with
proof of work at 6 of its 41 rounds, held against copies of parameter files by tests, by no theorem;
that it is any release's default is not said. OF THE THREE CONFIGURATION FILES the checker reads one
thing, the oracle's value at the string of the call on them: description, sizes, radii and rounds
are the ground's at every cfg, and nothing ties them to what the files say. cfg and the converter
are fixed before the oracle is drawn; one maker makes all five files. THE WAY OUT: nothing is said
where the first string does not decode or its record does not single one table out. A YES IS A YES
OF THE VALUE THAT THE CHECKER RETURNS, NOT OF THE FILES: the two roots and the answers are the
statement, and no file here compares them with a key's or a proof's. That some converter reaches
every typed value is not shown. That the checker returns a value on anything at the full size is not
shown: if it never did, the event would be empty. 32 of the 128 bits in some rounds are proof of
work, counted at one query a try. The bound is no numeral HERE: `fullV` is evaluated in
OnBytes/TypedOracleCompiler/Slice/EntryFullV.lean, and the bound is held below powers of one half in
EntryFullNum.lean; it says nothing once it reaches 1. Not the program, not the format's hash: a
random oracle. Nothing on the key's or the proof's file. Nothing on hiding. The limits of
OnBytes/TypedOracleCompiler/Slice/EntryHome.lean and EntryOne.lean stand.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryHomeFull
import OnBytes.TypedOracleCompiler.Slice.EntryRow13JohFull
import OnBytes.TypedOracleCompiler.Slice.EntryFromLib
import OnBytes.TypedOracleCompiler.Slice.EntrySpells

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open OnBytes Prob Cb TypedOracleCompiler.Run
open OnBytes.Slice (frS frD frRd frC GE GF decRec)
open OnBytes.Slice.Shapes (zFull Files Cfg dgOf Spells pubS₀ pubS₁ rdC)
open OnBytes.Tie (recordGround)
open OnBytes.Params (recordRead)
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View XO)
open TypedOracleCompiler.Run.PQ (bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open scoped ENNReal

/-! ## The typed verifier's count -/

/-- The bound on the judge's typed queries, as a function of a description's rounds, depth and
stored openings: four for the seeds' two chains; one for each round of the link, with the round in
front, and one more; for each opening a leaf and a path of the greatest depth; one for the request's
place. -/
def tVOf (ds : List PQ.RD) (a : ℕ) (xs : List XO) : ℕ :=
  4 + ((ds.length + 1 + 1) +
    ((PQ.nOpen ds + (xs.map (·.count)).sum) * (max (PQ.maxDepth ds) a + 1) + (0 + 1)))

/-- The judge's count at an entry's part is that function of its description. -/
theorem EntryAt.tV_of {An : Type} {lg s : ℕ} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s}
    (T : _root_.Fmt.M1.Code) (v eM : ℕ)
    (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
    (x : EntryAt An lg s d₁) (εs : ℝ≥0∞) :
    (x.base T v eM an εs).J.tV = tVOf x.D.ds x.D.a x.D.xs := by
  rw [EntryAt.tV_eq]
  have e1 : x.Z.wq.nOpen = PQ.nOpen x.D.ds + (x.D.xs.map (·.count)).sum := by
    show (wq0 x.D fun _ => true).nOpen = _
    unfold wq0
    rw [wireTo_nOpen]
    rfl
  have e2 : x.Z.wq.maxDepth = max (PQ.maxDepth x.D.ds) x.D.a := by
    show (wq0 x.D fun _ => true).maxDepth = _
    unfold wq0
    rw [PQ.wireTo_maxDepth]
    rfl
  unfold tVQB tVOf
  rw [e1, e2]
  show 4 + (((PQ.uL x.D.C x.D.ds).length + 1 + 1) + _) = _
  rw [length_uL]

/-- The count at the full size: a closed term. -/
def fullV : ℕ :=
  tVOf ((frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds).map PQ.ofLib)
    frS.P.T.a frD.xs

/-! ## The decision; soundness record by record -/

/-- THE DECISION AT THE FULL SIZE: the decision of the Lean port's link
(`linkVerify … .decides`), at keys written of the instance's answers and seeds: not shown to be the
keys, or the check, that the port makes of a file. It hangs on no digest. -/
def fullDec : ByteArray → XE (List T3) zFull.lg zFull.s → View → Bool :=
  fun _ x => (linkVerify recordRead.link
    (keysOfX zFull.v zFull.lg zFull.s (anT zFull.v zFull.s) x).1
    (keysOfX zFull.v zFull.lg zFull.s (anT zFull.v zFull.s) x).2).decides (OnBytes.Entry.start recordRead)

/-- SOUNDNESS RECORD BY RECORD AT THE FULL SIZE, UNDER THE ONE HYPOTHESIS ON CODES, in the
letters of `HomeData.Left.sound` but for the type of ε, written `link0Shape`
(OnBytes/TypedOracleCompiler/Slice/LinkShape.lean): the same type by unfolding. -/
theorem full_sound (hA : Cb.BCHKS46At GF GE) (c : ByteArray) (_ : c.size = 32) :
    ∃ ε : Err (link0Shape (entryXD recordGround c)),
      (∀ x, (Link0 (entryXD recordGround c) (fullDec c x)).Sound
        (fun _ => lgEX zFull.T zFull.v zFull.eM zFull.lg zFull.s (entryXD recordGround c)
          (anT zFull.v zFull.s) x) ε) ∧ Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  fr_row13_joh hA (anT zFull.v zFull.s) (entryXD recordGround c) (full_four c).1
    (full_four c).2.1 (full_four c).2.2.1 (full_four c).2.2.2

variable (d₁ : Sd1 zFull.lg zFull.s) [DecidableEq (Sd1 zFull.lg zFull.s)]

/-- THE ENTRY's PART AT THE FULL SIZE: NO LETTER IS LEFT but d₁, the fixed value that a first
query holds in the place of seeds: the description at the full-size ground; its parameter bytes;
`fullDec`; the page's own code behind the escape. -/
abbrev homeFull : HomeData zFull d₁ :=
  HomeData.ofGround recordGround zFull d₁ full_base_ok fullDec
    fun c => EntryRunTop.backOf (entryXD recordGround c) d₁

/-- The count, in the letters of `HomeData.Left.count`. -/
theorem full_count (cfg : Cfg) (T₀ T₁ : OnBytes.Slice.Tab) :
    (((homeFull d₁).atR cfg (fun _ => []) T₀ T₁).base zFull.T zFull.v zFull.eM
      (anT zFull.v zFull.s) (((2 : ℝ≥0∞)⁻¹) ^ 128)).J.tV = fullV := by
  rw [EntryAt.tV_of]
  show tVOf (entryXD recordGround (dgOf cfg T₀)).ds (entryXD recordGround (dgOf cfg T₀)).a
    (entryXD recordGround (dgOf cfg T₀)).xs = fullV
  rw [(full_four _).2.1, (full_four _).2.2.1, (full_four _).2.2.2]
  rfl

/-- (a) FOR THE ENTRY FILE AT THE FULL SIZE, UNDER THE ONE HYPOTHESIS ON CODES AND NOTHING ELSE.
Over one uniformly random oracle, for every three configuration files, EVERY converter and every
maker with at most t queries: with probability at most `entryB (2⁻¹)^128 0 142 fullV t` +
t^2 / 2^256 the checker "convert; two roots; the judge's run" returns a value while the entry's
language fails of the two strings that are read off the maker's log under that value's roots, with
its records (`EntryLose`, OnBytes/TypedOracleCompiler/Slice/EntryOne.lean). -/
theorem full_one_world (hA : Cb.BCHKS46At GF GE) (cfg : Cfg)
    (conv : (homeFull d₁).Conv cfg) (A : OComp (rom 256) Files) (t : ℕ)
    (hA' : A.QueryBound t) :
    Rom.Pr A.withTrace (EntryLose zFull.T zFull.v zFull.eM (anT zFull.v zFull.s)
      ((homeFull d₁).at cfg conv) (((2 : ℝ≥0∞)⁻¹) ^ 128)
      ((homeFull d₁).typ cfg conv (((2 : ℝ≥0∞)⁻¹) ^ 128)) 0 142 (pubS₀ cfg)
      (pubS₁ [(homeFull d₁).prm] cfg) (rdC zFull cfg)) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 142 fullV t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  (left_full d₁ fullDec _ cfg fullV (full_sound hA) (full_spells d₁ fullDec cfg)
    (full_count d₁ cfg)).one_world conv A t hA'

end TypedOracleCompiler.Slice
