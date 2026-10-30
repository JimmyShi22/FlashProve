-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntrySmallTop.lean: THE BOUND FOR THE ENTRY FILE AT THE SMALL EXAMPLE, UNDER THE
ONE HYPOTHESIS ON CODES AND NOTHING ELSE, AT THE VERY LETTERS OF A PLAY: the small twin of
OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean, at `homeSmall` (OnBytes/TypedOracleCompiler/Slice/EntryRunPlay.lean).

WHY AT THAT INSTANCE. `playSmall_yes_checker` (EntryRunPlay.lean) carries a play's "YES" to the
checker of the entry's part `homeSmall`, at the play's own converter. The bound here is for that
part, for every converter. So the checker that a play's yes speaks of is one of the checkers of
which this bound speaks: one description, one decision, one page, one code behind the escape.

Main definition: `smallV`: the judge's typed queries at the small sizes, a closed term (`tVOf`,
EntryFullTop.lean).
Main theorems.
 `entryDecR_linkAtCfg`  the decision of an entry's check does not read the configuration's digest.
 `homeSmall_dec`        the decision that a play takes is the program's own decision at the typed
                        small parameters, at the two keys that an instance's answers and seeds make.
 `small_sound`          soundness record by record, in the letters of `HomeData.Left.sound` but for
                        the type of ε, written `link0Shape` (OnBytes/TypedOracleCompiler/Slice/LinkShape.lean): the
                        same type by unfolding; at the decision that a play takes: `sr_row13_joh`
                        (OnBytes/TypedOracleCompiler/Slice/EntryRow13JohSmall.lean), under `Cb.BCHKS46At GF GE`.
 `small_count`          the judge has `smallV` typed queries at all tables.
 `small_left`           NOTHING IS LEFT OF THE BOUND'S DEBTS BUT THAT HYPOTHESIS: `left_small`
                        (OnBytes/TypedOracleCompiler/Slice/EntryHomeSmall.lean) with `small_sound`, `small_spells`
                        (OnBytes/TypedOracleCompiler/Slice/EntrySpells.lean), `small_count`.
 `small_one_world`      THE BOUND: over one uniformly random oracle, for all configuration files,
                        EVERY converter, every maker with at most t queries: the event `EntryLose`
                        (OnBytes/TypedOracleCompiler/Slice/EntryOne.lean) has probability at most `entryB (2⁻¹)^128
                        0 101 smallV t` + t^2 / 2^256.

Not claimed. `Cb.BCHKS46At GF GE` IS A HYPOTHESIS: a statement on codes that is taken as given: a
hypothesis of these theorems, proved in none of these files (`Cb.Gl.bchks46At`,
Cb/Bridge/GlCodesProved.lean, proves it from the files under lean/ThirdParty/, on which nothing is
said here). The bound is no number here: `smallV` and `entryB` are evaluated in
OnBytes/TypedOracleCompiler/Slice/EntrySmallNum.lean. OVER A UNIFORMLY RANDOM ORACLE: at a fixed hash nothing is
proved; a play runs at a fixed hash. THE WAY OUT: nothing is said where the first string does not
decode, or its record does not single one table out: the language has these as ways out. A YES IS A
YES OF THE VALUE that the converter makes, with the statement in it (two roots, both tables'
answers), not of the files. That some converter reaches every typed value is not shown. AT FOUR
ROUNDS 32 OF THE 128 BITS ARE PROOF OF WORK, at the others none (`sr_err_below`,
OnBytes/Slice/SmallRecNum.lean): a written verifier's message holds 32 test bits there, of which one
setting passes; that work is worth its bits is not shown. ONE FILE OF THREE: the entry's language
alone (the copy's table agrees with the first's); nothing on the key's or the proof's file, nor on
their join. The small example, not the full size. That the event is not empty: a yes has been seen
in runs alone. No sentence should rest on the instance at one converter (the head of EntryHome.lean
says why). Nothing on hiding. Nothing on any hash function. What the heads of EntryFullTop.lean,
EntryHome.lean, EntryHomeSmall.lean, EntryRow13JohSmall.lean, EntrySpells.lean, EntryOne.lean and
EntryRunPlay.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryFullTop
import OnBytes.TypedOracleCompiler.Slice.EntryRow13JohSmall
import OnBytes.TypedOracleCompiler.Slice.EntryRunPlay

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open OnBytes Prob Cb TypedOracleCompiler.Run
open OnBytes.Slice (srS srD srRd srC GE GF decRec)
open OnBytes.Slice.Shapes (zSmall Files Cfg dgOf pubS₀ pubS₁ rdC)
open OnBytes.Tie (smallRecordGround linkAtCfg entryDecR)
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

/-- The decision of an entry's check does not read the configuration's digest. -/
theorem entryDecR_linkAtCfg (p : OnBytes.Params.Link) (c : ByteArray) (k0 k1 : OnBytes.TableKey) :
    entryDecR (linkAtCfg p c) k0 k1 = entryDecR p k0 k1 := rfl

/-- The count at the small sizes: a closed term. -/
def smallV : ℕ :=
  tVOf ((srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srRd 5 :: srC.rds).map PQ.ofLib)
    srS.P.T.a srD.xs

set_option maxRecDepth 20000 in
/-- The decision that a play takes at the small example is the program's own decision on a
link's chain at the typed small parameters, at the two keys that an instance's answers and seeds
make. It hangs on no digest. -/
theorem homeSmall_dec (c : ByteArray) (x : XE (List TypedOracleCompiler.Run.FirstAnswers.T3) zSmall.lg
    zSmall.s) :
    homeSmall.dec c x = entryDecR OnBytes.Params.smallRecordRead
      (keysOfX zSmall.v zSmall.lg zSmall.s (anT zSmall.v zSmall.s) x).1
      (keysOfX zSmall.v zSmall.lg zSmall.s (anT zSmall.v zSmall.s) x).2 := rfl

/-- SOUNDNESS RECORD BY RECORD AT THE SMALL SIZES, UNDER THE ONE HYPOTHESIS ON CODES, in the
letters of `HomeData.Left.sound` but for the type of ε, written `link0Shape`
(OnBytes/TypedOracleCompiler/Slice/LinkShape.lean): the same type by unfolding; AT THE DECISION THAT A PLAY TAKES.
-/
theorem small_sound (hA : Cb.BCHKS46At GF GE) (c : ByteArray) (_ : c.size = 32) :
    ∃ ε : Err (link0Shape (entryXD smallRecordGround c)),
      (∀ x, (Link0 (entryXD smallRecordGround c) (homeSmall.dec c x)).Sound
        (fun _ => lgEX zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s (entryXD smallRecordGround c)
          (anT zSmall.v zSmall.s) x) ε) ∧ Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) := by
  obtain ⟨ε, h1, h2⟩ := sr_row13_joh hA (anT zSmall.v zSmall.s) (entryXD smallRecordGround c)
    (small_four c).1 (small_four c).2.1 (small_four c).2.2.1 (small_four c).2.2.2
  refine ⟨ε, fun x => ?_, h2⟩
  rw [homeSmall_dec]
  exact h1 x

/-- The count, in the letters of `HomeData.Left.count`. -/
theorem small_count (cfg : Cfg) (T₀ T₁ : OnBytes.Slice.Tab) :
    ((homeSmall.atR cfg (fun _ => []) T₀ T₁).base zSmall.T zSmall.v zSmall.eM
      (anT zSmall.v zSmall.s) (((2 : ℝ≥0∞)⁻¹) ^ 128)).J.tV = smallV := by
  rw [EntryAt.tV_of]
  show tVOf (entryXD smallRecordGround (dgOf cfg T₀)).ds (entryXD smallRecordGround (dgOf cfg T₀)).a
    (entryXD smallRecordGround (dgOf cfg T₀)).xs = smallV
  rw [(small_four _).2.1, (small_four _).2.2.1, (small_four _).2.2.2]
  rfl

/-- NOTHING IS LEFT OF THE BOUND'S DEBTS AT THE SMALL EXAMPLE BUT THE ONE HYPOTHESIS ON CODES.
-/
theorem small_left (hA : Cb.BCHKS46At GF GE) (cfg : Cfg) :
    homeSmall.Left cfg (((2 : ℝ≥0∞)⁻¹) ^ 128) 101 smallV :=
  left_small (d1Run _ _) _ _ cfg smallV (small_sound hA) (small_spells (d1Run _ _) _ cfg)
    (small_count cfg)

/-- THE BOUND FOR THE ENTRY FILE AT THE SMALL EXAMPLE, UNDER THE ONE HYPOTHESIS ON CODES AND
NOTHING ELSE, AT THE VERY LETTERS OF A PLAY. Over one uniformly random oracle, for every three
configuration files, EVERY converter and every maker with at most t queries: with probability at
most `entryB (2⁻¹)^128 0 101 smallV t` + t^2 / 2^256 the checker "convert; two roots; the judge's
run" returns a value while the entry's language fails of the two strings that are read off the
maker's log under that value's roots, with its records (`EntryLose`,
OnBytes/TypedOracleCompiler/Slice/EntryOne.lean). -/
theorem small_one_world (hA : Cb.BCHKS46At GF GE) (cfg : Cfg) (conv : homeSmall.Conv cfg)
    (A : OComp (rom 256) Files) (t : ℕ) (hA' : A.QueryBound t) :
    Rom.Pr A.withTrace (EntryLose zSmall.T zSmall.v zSmall.eM (anT zSmall.v zSmall.s)
      (homeSmall.at cfg conv) (((2 : ℝ≥0∞)⁻¹) ^ 128)
      (homeSmall.typ cfg conv (((2 : ℝ≥0∞)⁻¹) ^ 128)) 0 101 (pubS₀ cfg)
      (pubS₁ [homeSmall.prm] cfg) (rdC zSmall cfg)) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 101 smallV t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  (small_left hA cfg).one_world conv A t hA'

end TypedOracleCompiler.Slice
