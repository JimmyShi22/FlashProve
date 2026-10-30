-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryTop.lean: the entry file's checker at the two sizes: names for what it
returns and for its bad event, and the two statements on it side by side.

What this is not, first. It is not `innerCompiledVerifier_sound` and none of its three shares. It speaks of one
of the three files that a verification reads, the entry file. The checker is made by a second form
of the compiler (OnBytes/TypedOracleCompiler/Compile), proved sound in Lean, with a hand-written step for the seeds
in front; not by the library's compiler.

Main names.
 `HomeData.OutB`      the typed values where the oracle is the one made from the format's hash.
 `HomeData.Returns`   the checker at a converter returns o on the files d, under that oracle.
 `HomeData.Lose` the bad event over a drawn oracle (`EntryLose`, OnBytes/TypedOracleCompiler/Slice/EntryOne.lean).
 `EntryTopAt` two statements at one size. `yes`: if the function of a run (`playE`,
     OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean; either converter; no damage; the page's own family) says
     "YES" on three public files, a key file and an entry file, there is a typed value o with two
     roots, the IDs given out are made of o's roots, seeds and answers, and the checker at every
     converter that makes o returns o. `sound`: over one uniformly random oracle, for every three
     public files, every converter and every maker of files with at most t queries, t up to 2^64,
     the bad event has probability at most 2^-61.
 `entry_top_small`, `entry_top_full` both, under the one hypothesis `Cb.BCHKS46At GF GE`, a
     statement on Reed-Solomon codes that is taken as given: a hypothesis of these theorems, proved
     in none of these files (`Cb.Gl.bchks46At`, Cb/Bridge/GlCodesProved.lean, proves it from the
     files under lean/ThirdParty/, on which nothing is said here).

What is not claimed. The two statements meet in no theorem: `yes` is at one fixed hash, `sound` over
a drawn oracle. The figure is a ceiling of this theorem's bound, for this checker: no level of
security of any program; it counts 32 of the 128 bits as proof of work
(OnBytes/TypedOracleCompiler/Slice/EntryFullNum.lean, EntrySmallNum.lean). Nothing is said where the first string
does not decode or its record does not single one table out. The copy's root and answers are held
against nothing here. All that the heads of EntryFullTop.lean, EntrySmallTop.lean, EntryRunAny.lean
do not claim. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRunAny
import OnBytes.TypedOracleCompiler.Slice.EntrySmallNum

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Tie (EntryGround recordGround smallRecordGround)
open OnBytes.Slice (GE GF)
open OnBytes.Slice.Shapes (Files Size Cfg pubS₀ pubS₁ rdC zFull zSmall)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

namespace HomeData
variable {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁)

/-- The typed values at the format's hash: what a converter hands to the checker where the
oracle is the one made from the format's hash. -/
abbrev OutB (cfg : Cfg) : Type :=
  H.Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
    (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits)

/-- The checker returns o on the files d, at the converter conv, under the oracle made from the
format's hash. Bk: a ceiling on the blocks of an answer to a typed query, a number of the bound's
alone. -/
def Returns (cfg : Cfg) (Bk : ℕ) (conv : H.Conv cfg) (d : Files) (o : H.OutB cfg) : Prop :=
  (((H.spec cfg conv (((2 : ℝ≥0∞)⁻¹) ^ 128) Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg)
    (own₀ (pubS₀ cfg) _root_.Run.oBits)
    (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits)).chk d).det _root_.Run.oBits = some o

/-- The bad event, over a drawn oracle: the checker at the converter conv returns a value on the
maker's files while the entry's language fails of the two strings that are read off the maker's log
under that value's roots, with its records (`EntryLose`, OnBytes/TypedOracleCompiler/Slice/EntryOne.lean). -/
abbrev Lose (cfg : Cfg) (Bk : ℕ) (conv : H.Conv cfg) :=
  EntryLose z.T z.v z.eM (anT z.v z.s) (H.at cfg conv) (((2 : ℝ≥0∞)⁻¹) ^ 128)
    (H.typ cfg conv (((2 : ℝ≥0∞)⁻¹) ^ 128)) 0 Bk (pubS₀ cfg) (pubS₁ [H.prm] cfg) (rdC z cfg)

end HomeData

/-- What is shown of the entry file's verifier at one size. This is said under the hypotheses that
stand in the statement itself, which this comment does not list; it is no claim that they hold. G,
hok, zS: the size's typed parameters; H: the checker's letters at them; Bk: a number of the bound's.
-/
structure EntryTopAt (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (zS : OnBytes.Params.StdSize) {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)]
    (H : HomeData z d₁) (Bk : ℕ) : Prop where
  /-- A yes of a run's function is a yes of the checker, at every converter. If the function of
  a run says "YES" on the three public files, the key file and the entry file (either converter; no
  damage; the page's own family), there is a typed value o with two roots such that the IDs given
  out are made of o's roots, seeds and answers, and the checker at every converter that makes o
  returns o, under the oracle made from the format's hash. -/
  yes : ∀ (lax : Bool) (cfg : Cfg) (d : Files),
    (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 = "YES" →
    ∃ o : H.OutB cfg, o.1.length = 2 ∧
      (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).2 =
        "first " ++ stmtId G.q.link.table
            (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
            (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 ++ " copy " ++
          stmtId G.q.link.table (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
            (o.1.getD 1 default) o.2.1.2.2 o.2.1.1.2 ∧
      ∀ (conv' : H.Conv cfg) (d' : Files),
        conv' (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits) d' = some o →
        H.Returns cfg Bk conv' d' o
  /-- The checker is sound, at every converter. This is said under the hypotheses that stand in the
  statement itself, which this comment does not list; it is no claim that they hold. Over one
  uniformly random oracle, for every
  three public files, every converter and every maker of files with at most t queries, t up to
  2^64: the bad event has probability at most 2^-61. -/
  sound : ∀ (cfg : Cfg) (conv : H.Conv cfg) (A : OComp (rom 256) Files) (t : ℕ),
    A.QueryBound t → t ≤ 2 ^ 64 → Rom.Pr A.withTrace (H.Lose cfg Bk conv) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61

/-- The entry file's verifier at the small example, under the one hypothesis on codes. -/
theorem entry_top_small (hA : Cb.BCHKS46At GF GE) :
    EntryTopAt smallRecordGround small_record_ok OnBytes.Params.stdSmall homeSmall 101 where
  yes := fun lax cfg d h => by
    obtain ⟨o, h2, _, hw, hall⟩ := playSmall_yes_any lax cfg d (((2 : ℝ≥0∞)⁻¹) ^ 128) 101 h
    exact ⟨o, h2, hw, hall⟩
  sound := fun cfg conv A t hq ht => small_one_world_64 hA cfg conv A t hq ht

set_option maxRecDepth 40000 in
/-- The entry file's verifier at the full size, under the one hypothesis on codes. -/
theorem entry_top_full (hA : Cb.BCHKS46At GF GE) :
    EntryTopAt recordGround record_ok OnBytes.Params.stdFull
      (homeFull (d1Run zFull.lg zFull.s)) 142 where
  yes := fun lax cfg d h => by
    obtain ⟨o, h2, _, hw, hall⟩ := play_yes_any recordGround record_ok
      OnBytes.Params.recordRadius OnBytes.Params.stdFull lax cfg d (((2 : ℝ≥0∞)⁻¹) ^ 128) 142 h
    exact ⟨o, h2, hw, hall⟩
  sound := fun cfg conv A t hq ht =>
    full_one_world_64 (d1Run zFull.lg zFull.s) hA cfg conv A t hq ht

end TypedOracleCompiler.Slice
