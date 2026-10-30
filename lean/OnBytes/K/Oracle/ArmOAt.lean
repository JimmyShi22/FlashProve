-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/ArmOAt.lean: THE ENTRY FILE: TWO STATEMENTS ON ONE CHECKER THAT READS THE FILES
THROUGH THE ORACLE, at two sizes, with one hypothesis. NO THEOREM CARRIES THE PROBABILITY FROM THE
DRAWN ORACLE TO THE FIXED HASH.

 `entry_armO_small`, `entry_armO_full`: `EntryArmO` (OnBytes/K/Oracle/ArmO.lean) holds at the small
     example's and at the full size's typed parameters, under `Cb.BCHKS46At GF GE` alone.
 `soundO_small`, `soundO_full`, `leftO_small`, `leftO_full` the steps. The reader asks at most
     26,222 | 41,622 strings (OnBytes/K/Oracle/Counts.lean); the figure is the one without them
     (OnBytes/K/Oracle/Nums.lean).

In plain words. There is one checker: read the key file's table by a plain parse; read the entry
file by a twin of the program's reader, and derive both tables' seeds, with every hash asked of the
oracle but the digest of the three public files, which is handed in as the oracle's own value at
their string; then run the compiled verifier, which asks the same oracle. (1) If a call of this
tree's Lean verifier program ends with exit code 0 and its parameter file has the setting's lines,
that checker, at the oracle made from the format's hash, returns a typed value on the call's own key
file and entry file, with the two tables of the program's own yes and the user's ID. (2) The public
files and the maker are fixed first; then, over one uniformly random oracle, a maker of files with
at most 2^64 queries gets THAT SAME CHECKER to return a value of which the entry's language fails,
of the two strings read off the maker's log, with probability at most 2^-61.

Read the heads of ArmO.lean and of OnBytes/K/Left/Arm.lean before citing this. (1) is at one fixed
hash, (2) over a drawn oracle: what joins them is the step of every argument in the random-oracle
model, and it is no theorem: NO PROBABILITY IS SAID OF THE PROGRAM's YES. Its reading of the entry
file is a twin of the program's, equal to it on every file when the program's hash is put in
(`twin_at_port`, OnBytes/K/Oracle/ReaderAt.lean); the verifier behind it is made by a second form of
the compiler; it is not the program's own check and not `innerCompiledVerifier`. ONE file of
three. Only (2) uses the hypothesis on codes. The figure is a ceiling of this bound, with 32 of 128
bits counted as proof of work. Nothing is said where the first table does not decode or its record
does not single one table out. That under a drawn oracle the checker accepts anything is not shown.
Nothing on hiding.

What must travel with every sentence on these two theorems. (1) A second checker: made by a second
form of the compiler, with a hand-written step for the seeds; not `innerCompiledVerifier`, no
instance of `InnerCompilerInput`, and not the program's own check of an entry file. (2)
Its reader is a twin of the program's: the program does not call the reader; whether it runs that
twin's own text on a model's entry file follows from what OnBytes/Main.lean calls; that the reader
asks what the program hashes is not claimed; that the checker's definitions reach nothing of what
the format's hash is made of is a program's walk, no theorem; the key file's table is parsed, no
more. (3) One fixed hash in the first statement, a drawn oracle in the second, composed nowhere: no
probability is said of the program's yes; the second concludes of strings read off a maker's log,
and in the first there is no maker and no log; the ID stands in the first alone, and it and the
public files' digest there are values of the fixed hash. The three public files are fixed before the
oracle is drawn: a maker who picks them after asking the oracle is not covered; in the first
statement they are the call's own.
(4) Nothing is said where the first table does not decode or its record does not single one table
out; without the key file's part nothing follows from the entry file's. (5) Exit code 0 is given for
`YES` and for `WITHIN LIMITS` alike, and no call is shown to end with it; that a parameter file has
the setting's lines is proved of copies of the first 32 lines of two example parameter files
(OnBytes/K/Left/TestSaysLines.lean) and of every byte string that begins with one of these
(SaysLinesPrefix.lean), of no file on a disk. (6) The statement on codes is a hypothesis of these
two theorems (`Cb.Gl.bchks46At`, Cb/Bridge/GlCodesProved.lean, proves it from the files under
lean/ThirdParty/, on which nothing is said here); the figure
counts 32 of each round's
128 bits as proof of work at 6 of the 41 rounds and at 4 of the 24, and is no level of security of
any program.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.ArmO
import OnBytes.K.Oracle.Nums
import OnBytes.K.Oracle.Counts
import OnBytes.K.Left.ArmAt

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Oracle
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Slice OnBytes.K.Left
open OnBytes.Tie (EntryGround recordGround smallRecordGround typedT)
open OnBytes.Slice (GE GF)
open OnBytes.Slice.Shapes (Size Cfg zFull zSmall)
open scoped ENNReal

/-- What is left of the bound's hypotheses at the small example, at `homeOf`'s letters. -/
theorem leftO_small (hA : Cb.BCHKS46At GF GE) (cfg : Cfg) :
    (homeOf smallRecordGround small_record_ok Params.smallRecordRadius).Left cfg
      (((2 : ℝ≥0∞)⁻¹) ^ 128) 101 smallV :=
  homeOf_small ▸ small_left hA cfg

/-- The same at the full size. -/
theorem leftO_full (hA : Cb.BCHKS46At GF GE) (cfg : Cfg) :
    (homeOf recordGround record_ok Params.recordRadius).Left cfg
      (((2 : ℝ≥0∞)⁻¹) ^ 128) 142 fullV :=
  homeOf_full ▸ left_full (d1Run zFull.lg zFull.s) fullDec _ cfg fullV (full_sound hA)
    (full_spells (d1Run zFull.lg zFull.s) fullDec cfg) (full_count (d1Run zFull.lg zFull.s) cfg)

/-- The bound at the small example, for the reader that asks the oracle. -/
theorem soundO_small (hA : Cb.BCHKS46At GF GE) (cfg : Cfg)
    (A : OComp (rom 256) OnBytes.Slice.Shapes.Files) (t : ℕ) (hq : A.QueryBound t)
    (ht : t ≤ 2 ^ 64) :
    Rom.Pr A.withTrace (HomeData.LoseO
      (readerOf smallRecordGround small_record_ok Params.smallRecordRadius cfg)
      (((2 : ℝ≥0∞)⁻¹) ^ 128) 101) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61 := by
  refine le_trans ((leftO_small hA cfg).one_worldO _ A t hq) ?_
  rw [smallV_eq]
  exact entryB_smallT_64 _ t (by rw [small_record_count]; norm_num) ht

/-- The bound at the full size, for the reader that asks the oracle. -/
theorem soundO_full (hA : Cb.BCHKS46At GF GE) (cfg : Cfg)
    (A : OComp (rom 256) OnBytes.Slice.Shapes.Files) (t : ℕ) (hq : A.QueryBound t)
    (ht : t ≤ 2 ^ 64) :
    Rom.Pr A.withTrace (HomeData.LoseO
      (readerOf recordGround record_ok Params.recordRadius cfg)
      (((2 : ℝ≥0∞)⁻¹) ^ 128) 142) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61 := by
  refine le_trans ((leftO_full hA cfg).one_worldO _ A t hq) ?_
  rw [fullV_eq]
  exact entryB_fullT_64 _ t (by rw [record_count]; norm_num) ht

/-- **`EntryArmO` at the small example.** One hypothesis: the statement on codes. -/
theorem entry_armO_small (hA : Cb.BCHKS46At GF GE) :
    EntryArmO smallRecordGround
      (homeOf smallRecordGround small_record_ok Params.smallRecordRadius)
      (readerOf smallRecordGround small_record_ok Params.smallRecordRadius) 101 where
  zero := zeroO_of_left smallRecordGround small_record_ok small_record_answers Params.stdSmall
    Params.smallRecordRadius 101 (entryLeft_of_at _ _ _ left_small)
  sound := soundO_small hA
  same := fun _ _ _ => Iff.rfl

/-- **`EntryArmO` at the full size.** One hypothesis: the statement on codes. -/
theorem entry_armO_full (hA : Cb.BCHKS46At GF GE) :
    EntryArmO recordGround (homeOf recordGround record_ok Params.recordRadius)
      (readerOf recordGround record_ok Params.recordRadius) 142 where
  zero := zeroO_of_left recordGround record_ok record_answers Params.stdFull
    Params.recordRadius 142 (entryLeft_of_at _ _ _ left_full)
  sound := soundO_full hA
  same := fun _ _ _ => Iff.rfl

end OnBytes.K.Oracle
