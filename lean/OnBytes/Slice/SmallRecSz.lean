-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecSz.lean: the sizes, the stages and the rounds of an entry's chain at the small
files of the setting "record with work", in the forms of this folder.

The setting: stored tables have a record of one answer a row, and all codes are tested up to radii
below the Johnson radius. OnBytes/Params/EntryStagesRecordSmall.lean has the planner's sizes at the
lines typed for the small parameter file; OnBytes/Params/EntryDryRecordSmall.lean has the parameter
bytes spelled from them (`Params.smallRecordRead`) and the 24 rounds that the dry run of the
program's block states under these bytes (`Params.smallRecordRounds`); "the program" is the Lean
text `verify-on-bytes`. The library's own description of an entry's chain (`Fmt.M3.entrySpec`) does
not cover a table with a record. So the description here is `Params.entrySpecOf` at these bytes and
rounds, and one evaluation in Lean's kernel shows that its rounds are a list made by the format's
own makers of rounds (`srFmt`): the library's list `Fmt.M3.roundsOf` but for the number of rows
under the round BAT, which is larger by two, one for each table's record's row.

Main definitions.
 `srPar`   the format's record of sizes, with one answer in a record (s = 1) and 32 bits of work.
 `srSz`    the record of sizes of OnBytes/Slice/LinkAt.lean at `srPar`, with the four radii as
           parameters.
 `srSg1`, `srSg2`, `srSg3`   the three stages of the proximity test. The mask codes of the first
           two are shorter than their main codes.
 `srFmt`   the 24 rounds, by the format's makers of rounds. `srStored`: the stored openings.
 `srD`     the description of the chain by `Params.entrySpecOf`, at an empty statement.
 `srRd i`  round number i of the description, counted from 0. `srRt i`: the same of `srFmt`.
Main theorems.
 `sr_link`, `sr_codes`   the sizes are those of the typed link's shape and the typed codes.
 `sr_cube`, `sr_aPhi`, `sr_cut`   20 and 19 variables; the tables are compared before entry 524285.
 `sr_stages`, `sr_sg`   the stages are the record's; the stage of the link's group is the first.
 `sr_fmt`, `sr_stored`   the dry run's rounds are `srFmt`, its stored openings `srStored`.
 `sr_a`, `sr_xs`, `sr_roots`   the stored tables' depth; the two openings at the round LINK; no
           round sends more than one root.
 `sr_ds`, `sr_rd`, `sr_ds_eq`   so the description's rounds are those made of `srFmt`.
 `sr_ds_at`, `sr_xs_at`   rounds and stored openings are the same at every statement.

Not claimed. That these are the C++ programs' sizes, or any file's: what ties the typed lines to a
file is said in the heads of the two files of OnBytes/Params/ named above. That `Tie.entrySpec`
gives a description. Nothing on the entry RECORD of the plan, which is no round of the chain.
Nothing on the radii, which are free here. Nothing on what the rounds send or draw
(OnBytes/Slice/SmallRecRounds.lean). Nothing on a protocol or on soundness.

-/
import OnBytes.Params.EntryDryRecordSmall
import OnBytes.Params.EntryRoundsToy
import OnBytes.Slice.BatSem
import OnBytes.Tie.StoredMain

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run _root_.Run.PQ
open Params (smallRecordRead smallRecordRounds smallRecordLink smallRecordCodes)

/-- The sizes of an entry's chain at the small files of the setting "record with work": the tables'
code, their 2^8 rows and the one answer of a row's record; 51 and 51 drawn columns; 18 rows for a
folded row; three stages; 32 bits of work where a round has work. -/
def srPar : Fmt.M3.Par where
  fld := .two
  T := ⟨23, 524288, 65535⟩
  v := 8
  s := 1
  nu0 := 51
  nuj := 51
  C := ⟨17, 32768, 97⟩
  Z := ⟨13, 64, 97⟩
  R := 18
  stages := [⟨⟨17, 32768, 97⟩, ⟨13, 64, 97⟩, 6, 0, 97⟩,
    ⟨⟨14, 2048, 66⟩, ⟨12, 128, 66⟩, 4, 2, 66⟩, ⟨⟨14, 2048, 66⟩, ⟨14, 512, 66⟩, 0, 0, 66⟩]
  work := 32
  salt := 40

/-- The tables' shape, the numbers of drawn columns, the rows of a folded row and the order of rows
are those of the typed link's shape; the field and the bytes of a salt are the typed plan's. -/
theorem sr_link : smallRecordLink.table = ⟨⟨srPar.T.a, srPar.T.l, srPar.T.r⟩, srPar.v, srPar.s,
      srPar.salt⟩ ∧
    smallRecordLink.columnsFirst = srPar.nu0 ∧ smallRecordLink.columnsFurther = srPar.nuj ∧
    smallRecordLink.rows = srPar.R ∧ smallRecordLink.rowsHigh = srPar.high ∧
    Params.smallRecordPlan.field = srPar.fld ∧ Params.smallRecordPlan.salt = srPar.salt :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The sizes, with the four radii as parameters. -/
def srSz (eM e0 e1 eU : ℕ) : Sz where
  P := srPar
  eM := eM
  e0 := e0
  e1 := e1
  eU := eU
  hR := by decide
  hl := by decide
  fitM := by decide
  fitT := by decide +kernel

/-- The cube of a folded row's oracle message has 20 variables. -/
theorem sr_cube (eM e0 e1 eU : ℕ) : (srSz eM e0 e1 eU).P.aR + (srSz eM e0 e1 eU).P.aP = 20 := by
  show srPar.aR + srPar.aP = 20
  decide +kernel

/-- The cube of the layout that is compared has 19 variables. -/
theorem sr_aPhi (eM e0 e1 eU : ℕ) : (srSz eM e0 e1 eU).P.aPhi = 19 := by
  show srPar.aPhi = 19
  decide +kernel

/-- The tables are compared before entry 524285: the last three entries of a row's message are the
pad of its one answer. -/
theorem sr_cut (eM e0 e1 eU : ℕ) : (srSz eM e0 e1 eU).P.cut = 524285 := by
  show srPar.cut = 524285
  decide +kernel

/-- The first stage: six row variables, no mask variable, 97 positions. -/
def srSg1 : Sg := ⟨⟨17, 32768, 97⟩, ⟨13, 64, 97⟩, 0, 6, 97⟩

/-- The second stage: four row variables, two of them mask variables, 66 positions. -/
def srSg2 : Sg := ⟨⟨14, 2048, 66⟩, ⟨12, 128, 66⟩, 2, 2, 66⟩

/-- The third stage: no row variable, 66 positions. -/
def srSg3 : Sg := ⟨⟨14, 2048, 66⟩, ⟨14, 512, 66⟩, 0, 0, 66⟩

/-- The three stages are those of the format's record. -/
theorem sr_stages : srPar.stages = [srSg1.st, srSg2.st, srSg3.st] := rfl

/-- The stages' codes are the typed codes: two main codes, of which the second serves two stages,
and three mask codes. The typed link's shape names them by these numbers, with the later stages'
numbers of row variables and of mask variables. -/
theorem sr_codes : smallRecordCodes =
      ⟨#[⟨srSg1.C.a, srSg1.C.l, srSg1.C.r⟩, ⟨srSg2.C.a, srSg2.C.l, srSg2.C.r⟩],
        #[⟨srSg1.Z.a, srSg1.Z.l, srSg1.Z.r⟩, ⟨srSg2.Z.a, srSg2.Z.l, srSg2.Z.r⟩,
          ⟨srSg3.Z.a, srSg3.Z.l, srSg3.Z.r⟩]⟩ ∧
    srSg3.C = srSg2.C ∧ smallRecordLink.code = 0 ∧ smallRecordLink.maskCode = 0 ∧
    smallRecordLink.later =
      [⟨1, 1, srSg2.h + srSg2.g, srSg2.h⟩, ⟨1, 2, srSg3.h + srSg3.g, srSg3.h⟩] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The stage of the link's group is the first stage. -/
theorem sr_sg (eM e0 e1 eU : ℕ) : (srSz eM e0 e1 eU).sg 97 = srSg1 := by
  have haR : srPar.aR = 5 := by decide +kernel
  show (⟨srPar.C, srPar.Z, 0, srPar.aR + 1, 97⟩ : Sg) = srSg1
  rw [haR]
  rfl

/-- **The 24 rounds, by the format's makers of rounds**: the link's five, the batching of
2 s + 1 + 2 + 51 + 51 = 107 rows, and the rounds of the proximity test. -/
def srFmt : List Fmt.Round :=
  [Fmt.M3.rLinkPoint srPar.v, Fmt.M2.rSeedN (srPar.aR + srPar.aP), Fmt.M2.rAnswers 2,
      Fmt.M3.rLink srPar.work (srPar.nu0 + srPar.nuj) srPar.T.a, Fmt.M3.rLinkPhi srPar.aPhi,
      Fmt.M2.rBatN (2 * srPar.s + Fmt.M3.nRows srPar)] ++
    Fmt.M1.laterRounds srPar.work 0 (Fmt.M3.width0 srPar) srSg1.st [srSg2.st, srSg3.st]

/-- **The rounds that the dry run of the program's block states are these.** -/
theorem sr_fmt : smallRecordRounds.map (·.1) = srFmt :=
  Params.rounds_of_parts (by decide +kernel)

/-- The openings of stored tables, round by round, as the library's description has them: at the
round LINK the first table's at the first 51 draws and the copy's at the last 51; elsewhere none. -/
def srStored : List (List Fmt.Stored) :=
  srFmt.map fun r =>
    if r.entry.name == "LINK" then
      [⟨Fmt.M3.shT srPar, srPar.salt, 0, 0, srPar.nu0⟩,
        ⟨Fmt.M3.shT srPar, srPar.salt, 1, srPar.nu0, srPar.nuj⟩]
    else []

/-- **The stored openings that the dry run states are these.** -/
theorem sr_stored : smallRecordRounds.map (·.2) = srStored := by decide +kernel

/-- The description of the chain by `Params.entrySpecOf`, at an empty statement. -/
def srD : XD :=
  Tie.xdOf (Params.entrySpecOf smallRecordRead smallRecordRounds ByteArray.empty)
    fun _ _ => ByteArray.empty

/-- The description's rounds are the same at every statement. -/
theorem sr_ds_at (st : ByteArray) (stm : ByteArray → ByteArray → ByteArray) :
    (Tie.xdOf (Params.entrySpecOf smallRecordRead smallRecordRounds st) stm).ds = srD.ds :=
  _root_.Run.rds_congr _ _ rfl rfl

/-- The description's stored openings are the same at every statement. -/
theorem sr_xs_at (st : ByteArray) (stm : ByteArray → ByteArray → ByteArray) :
    (Tie.xdOf (Params.entrySpecOf smallRecordRead smallRecordRounds st) stm).xs = srD.xs := rfl

/-- The stored tables have 2^23 positions. -/
theorem sr_a : srD.a = srPar.T.a := by
  unfold XD.a
  rw [show srD.stored = srStored from sr_stored]
  rfl

/-- The two openings of stored tables, both at round number 3. -/
theorem sr_xs : srD.xs = [⟨3, false, 0, 51⟩, ⟨3, true, 51, 51⟩] := by
  unfold XD.xs
  rw [show srD.stored = srStored from sr_stored]
  rfl

/-- No round sends more than one root. -/
theorem sr_roots : ∀ r ∈ srD.base.rounds, r.entry.roots ≤ 1 := by
  rw [show srD.base.rounds = srFmt from sr_fmt]
  decide +kernel

/-- The same description with `srFmt` written in the place of the dry run's rounds. -/
def srBase : Fmt.Spec := { srD.base with rounds := srFmt }

/-- The description's rounds are those made of `srFmt`. -/
theorem sr_ds : srD.ds = rds srBase := _root_.Run.rds_congr _ _ sr_fmt rfl

/-- Round number i of the description, counted from 0; an empty round beyond the list's end. -/
def srRd (i : ℕ) : RD := srD.ds.getD i ⟨e0, .nothing, [], none, []⟩

/-- Round number i of those made of `srFmt`. -/
def srRt (i : ℕ) : RD := (rds srBase).getD i ⟨e0, .nothing, [], none, []⟩

/-- They are the same round. -/
theorem sr_rd (i : ℕ) : srRd i = srRt i := by
  unfold srRd srRt
  rw [sr_ds]

/-- The description has at least five rounds: `srRd 0` to `srRd 4`, then the rest. -/
theorem sr_ds_eq : srD.ds = srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srD.ds.drop 5 := by
  unfold srRd
  rw [sr_ds]
  rfl

end OnBytes.Slice
