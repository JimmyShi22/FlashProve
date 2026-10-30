-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/DecodesAt.lean: the guard of OnBytes/K/Oracle/Decodes.lean, written out at the two
sizes.

 `groundSize_full`, `groundSize_small` the size z at which `homeOf` stands at the two grounds, and
     so the z of the decoder `decRec z.T z.v z.eM z.lg z.s` in `EntryArmO.sound` and
     `EntryArm.sound`, is `zFull`, `zSmall`.
 `decFull_eq`, `decSmall_eq` that decoder is the decoder with a record at the link's own code, rows
     and radius. The theorems below stand at the right sides of these two equations.
 `full_dist`, `small_dist`   the two codes' distances, and that the radii are below them.
 `full_honest_decodes`, `small_honest_decodes` no hypothesis: every table that the format's encoder
     makes decodes with the record of its own answers, at every seed, and the record singles it out.
 `full_honest_not_lang`, `small_honest_not_lang` one hypothesis: two such tables whose messages
     differ at an entry before the pads are outside the entry's language.

How the last two are to be read. Each table goes with the record of ITS OWN answers, at any two
seeds. "Differ": as read in the field, in some row. "Before the pads": at an index below l - 3 s;
that the format's pads begin there is not asked (the head of OnBytes/Slice/DecoderRec.lean). "That
the format's encoder makes": Lean's table made with `Fmt.M1.symF` (`honestTab`,
OnBytes/Slice/Honest.lean); no Lean file compares it with what the programs write.

What is not claimed. All that the head of Decodes.lean does not claim: strings and records written
down; nothing says that a checker returns a value on any files; nothing ties these strings or
records to what is read off a log under a root, or to the records in a checker's value; the seed is
any seed. Two such tables with the same messages and other tails or seeds are IN the language
(`honest_lang`); for tables that differ in their pads alone no theorem here says it. Nothing on
hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.Decodes
import OnBytes.TypedOracleCompiler.Slice.EntryRunPlay

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Oracle
open Cb Cb.Ood Blocks OnBytes.Slice
open OnBytes.Slice.Shapes (zFull zSmall zFull_lg zSmall_lg)

/-- The size at which `homeOf` stands at the full size's ground and radius, and so the size z of the
decoder `decRec z.T z.v z.eM z.lg z.s` in `EntryArmO.sound` there, is `zFull`. -/
theorem groundSize_full :
    TypedOracleCompiler.Slice.groundSize OnBytes.Tie.recordGround Params.recordRadius = zFull := rfl

/-- The like at the small example. -/
theorem groundSize_small :
    TypedOracleCompiler.Slice.groundSize OnBytes.Tie.smallRecordGround Params.smallRecordRadius = zSmall :=
  rfl

/-- The decoder of which the two statements speak at the full size is the decoder with a record at
the full-size link's code, rows and radius, with 29 coordinates and one answer. -/
theorem decFull_eq : decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s =
    decRec frS.P.T frS.P.v frS.eM 29 1 :=
  congrArg (fun n => decRec zFull.T zFull.v zFull.eM n zFull.s) zFull_lg

/-- The like at the small example: 19 coordinates and one answer. -/
theorem decSmall_eq : decRec zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s =
    decRec srS.P.T srS.P.v srS.eM 19 1 :=
  congrArg (fun n => decRec zSmall.T zSmall.v zSmall.eM n zSmall.s) zSmall_lg

/-- The full size's code has distance 3,848,273,922; the radius 2,852,142,980 is below it. -/
theorem full_dist : HasDist frS.ix.G 3848273922 ∧ frS.eM < 3848273922 :=
  ⟨hasDist_genOf frS.P.T (by decide) (by decide), by decide⟩

/-- The small example's code has distance 7,798,786; the radius 6,137,119 is below it. -/
theorem small_dist : HasDist srS.ix.G 7798786 ∧ srS.eM < 7798786 :=
  ⟨hasDist_genOf srS.P.T (by decide) (by decide), by decide⟩

/-- **At the full size: every table that the format's encoder makes decodes with the record of its
own answers, at every seed, and the record singles it out.** No hypothesis. -/
theorem full_honest_decodes (msg tl : ℕ → List UInt64)
    (ρ : (decRec frS.P.T frS.P.v frS.eM 29 1).Z.D) :
    (decRec frS.P.T frS.P.v frS.eM 29 1).dcdRaw (honestRaw frS msg tl)
        (honestRec frS 29 1 msg ρ) = some (honestMsgs frS msg) ∧
      ¬ (decRec frS.P.T frS.P.v frS.eM 29 1).collRaw (honestRaw frS msg tl) ρ :=
  honest_decodes frS 29 1 full_dist.1 full_dist.2 msg tl ρ

/-- **The same at the small example.** No hypothesis. -/
theorem small_honest_decodes (msg tl : ℕ → List UInt64)
    (ρ : (decRec srS.P.T srS.P.v srS.eM 19 1).Z.D) :
    (decRec srS.P.T srS.P.v srS.eM 19 1).dcdRaw (honestRaw srS msg tl)
        (honestRec srS 19 1 msg ρ) = some (honestMsgs srS msg) ∧
      ¬ (decRec srS.P.T srS.P.v srS.eM 19 1).collRaw (honestRaw srS msg tl) ρ :=
  honest_decodes srS 19 1 small_dist.1 small_dist.2 msg tl ρ

/-- At the full size: two such tables whose messages differ at an entry before the pads are outside
the entry's language. -/
theorem full_honest_not_lang (msg₀ msg₁ tl₀ tl₁ : ℕ → List UInt64)
    (ρ₀ ρ₁ : (decRec frS.P.T frS.P.v frS.eM 29 1).Z.D)
    (hne : ∃ (r : frS.ix.Row) (j : frS.En), j.val < frS.P.T.l - 3 * 1 ∧
      honestMsgs frS msg₁ (r, j) ≠ honestMsgs frS msg₀ (r, j)) :
    ¬ DecR.LangE (DecR.wayColl (decRec frS.P.T frS.P.v frS.eM 29 1)) (honestRec frS 29 1 msg₀ ρ₀)
      (honestRec frS 29 1 msg₁ ρ₁) (honestRaw frS msg₀ tl₀) (honestRaw frS msg₁ tl₁) :=
  honest_not_lang frS 29 1 full_dist.1 full_dist.2 msg₀ msg₁ tl₀ tl₁ ρ₀ ρ₁ hne

/-- The same at the small example. -/
theorem small_honest_not_lang (msg₀ msg₁ tl₀ tl₁ : ℕ → List UInt64)
    (ρ₀ ρ₁ : (decRec srS.P.T srS.P.v srS.eM 19 1).Z.D)
    (hne : ∃ (r : srS.ix.Row) (j : srS.En), j.val < srS.P.T.l - 3 * 1 ∧
      honestMsgs srS msg₁ (r, j) ≠ honestMsgs srS msg₀ (r, j)) :
    ¬ DecR.LangE (DecR.wayColl (decRec srS.P.T srS.P.v srS.eM 19 1)) (honestRec srS 19 1 msg₀ ρ₀)
      (honestRec srS 19 1 msg₁ ρ₁) (honestRaw srS msg₀ tl₀) (honestRaw srS msg₁ tl₁) :=
  honest_not_lang srS 19 1 small_dist.1 small_dist.2 msg₀ msg₁ tl₀ tl₁ ρ₀ ρ₁ hne

end OnBytes.K.Oracle
