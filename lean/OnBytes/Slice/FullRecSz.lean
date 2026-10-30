-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecSz.lean: the sizes, the stages and the rounds of an entry's chain at the
full-size files of the setting "record with work", in the forms of this folder.

The like of OnBytes/Slice/SmallRecSz.lean, whose head describes the setting and the way, at the full
size; its text was made from that file's by a program that swaps names and numbers and writes five
stages for three. OnBytes/Params/EntryStagesRecord.lean has the planner's sizes at the lines typed
for the full-size parameter file; OnBytes/Params/EntryDryRecord.lean has the parameter bytes spelled
from them (`Params.recordRead`) and the 41 rounds that the dry run of the block of
`verify-on-bytes` states under these bytes (`Params.recordRounds`). The description here is
`Params.entrySpecOf` at these bytes and rounds, and one evaluation in Lean's kernel shows that its
rounds are a list made by the format's own makers of rounds (`frFmt`): `Fmt.M3.roundsOf`, the list
of rounds before the record's rows are added, but for the round BAT, which has two rows more.

Main definitions.
 `frPar`   the format's record of sizes, with one answer in a record (s = 1) and 32 bits of work.
 `frSz`    the record of sizes of OnBytes/Slice/LinkAt.lean at `frPar`, with the four radii as
           parameters.
 `frSg1` to `frSg5`   the five stages of the proximity test. The mask codes of the first four are
           shorter than their main codes.
 `frFmt`   the 41 rounds, by the format's makers of rounds. `frStored`: the stored openings.
 `frD`     the description of the chain by `Params.entrySpecOf`, at an empty statement.
 `frRd i`  round number i of the description, counted from 0. `frRt i`: the same of `frFmt`.
Main theorems.
 `fr_link`, `fr_codes`   the sizes are those of the typed link's shape and the typed codes.
 `fr_cube`, `fr_aPhi`, `fr_cut`   29 and 29 variables; the tables are compared before entry
           402653181.
 `fr_stages`, `fr_sg`   the stages are the record's; the stage of the link's group is the first.
 `fr_fmt`, `fr_stored`   the dry run's rounds are `frFmt`, its stored openings `frStored`.
 `fr_a`, `fr_xs`, `fr_roots`   the stored tables' depth; the two openings at the round LINK; no
           round sends more than one root.
 `fr_ds`, `fr_rd`, `fr_ds_eq`   so the description's rounds are those made of `frFmt`.
 `fr_ds_at`, `fr_xs_at`   rounds and stored openings are the same at every statement.

Not claimed. That these are the C++ programs' sizes, or any file's: what ties the typed lines to a
file is said in the heads of the two files of OnBytes/Params/ named above. That `Tie.entrySpec`
gives a description. Nothing on the entry RECORD of the plan, which is no round of the chain.
Nothing on the radii, which are free here. Nothing on what the rounds send or draw
(OnBytes/Slice/FullRecRounds.lean). Nothing on a protocol or on soundness.

-/
import OnBytes.Params.EntryDryRecord
import OnBytes.Params.EntryRoundsToy
import OnBytes.Slice.BatSem
import OnBytes.Tie.StoredMain

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run _root_.Run.PQ
open Params (recordRead recordRounds recordLink recordCodes)

/-- The sizes of an entry's chain at the full-size files of the setting "record with work": the
tables' code, their 2^11 rows and the one answer of a row's record; 62 and 62 drawn columns; 107
rows for a folded row; five stages; 32 bits of work where a round has work. -/
def frPar : Fmt.M3.Par where
  fld := .two
  T := ⟨32, 402653184, 44040191⟩
  v := 11
  s := 1
  nu0 := 62
  nuj := 62
  C := ⟨24, 4194304, 97⟩
  Z := ⟨13, 64, 97⟩
  R := 107
  stages := [⟨⟨24, 4194304, 97⟩, ⟨13, 64, 97⟩, 8, 0, 97⟩,
    ⟨⟨21, 131072, 49⟩, ⟨12, 128, 49⟩, 5, 2, 49⟩,
    ⟨⟨17, 8192, 49⟩, ⟨12, 128, 49⟩, 4, 2, 49⟩,
    ⟨⟨13, 512, 50⟩, ⟨12, 128, 50⟩, 4, 2, 50⟩,
    ⟨⟨14, 512, 40⟩, ⟨14, 512, 40⟩, 0, 0, 40⟩]
  work := 32
  salt := 40

/-- The tables' shape, the numbers of drawn columns, the rows of a folded row and the order of rows
are those of the typed link's shape; the field and the bytes of a salt are the typed plan's. -/
theorem fr_link : recordLink.table = ⟨⟨frPar.T.a, frPar.T.l, frPar.T.r⟩, frPar.v, frPar.s,
      frPar.salt⟩ ∧
    recordLink.columnsFirst = frPar.nu0 ∧ recordLink.columnsFurther = frPar.nuj ∧
    recordLink.rows = frPar.R ∧ recordLink.rowsHigh = frPar.high ∧
    Params.recordPlan.field = frPar.fld ∧ Params.recordPlan.salt = frPar.salt :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The sizes, with the four radii as parameters. -/
def frSz (eM e0 e1 eU : ℕ) : Sz where
  P := frPar
  eM := eM
  e0 := e0
  e1 := e1
  eU := eU
  hR := by decide
  hl := by decide
  fitM := by decide +kernel
  fitT := by decide +kernel

/-- The cube of a folded row's oracle message has 29 variables. -/
theorem fr_cube (eM e0 e1 eU : ℕ) : (frSz eM e0 e1 eU).P.aR + (frSz eM e0 e1 eU).P.aP = 29 := by
  show frPar.aR + frPar.aP = 29
  decide +kernel

/-- The cube of the layout that is compared has 29 variables. -/
theorem fr_aPhi (eM e0 e1 eU : ℕ) : (frSz eM e0 e1 eU).P.aPhi = 29 := by
  show frPar.aPhi = 29
  decide +kernel

/-- The tables are compared before entry 402653181: the last three entries of a row's message are
the pad of its one answer. -/
theorem fr_cut (eM e0 e1 eU : ℕ) : (frSz eM e0 e1 eU).P.cut = 402653181 := by
  show frPar.cut = 402653181
  decide +kernel

/-- The first stage: eight row variables, no mask variable, 97 positions. -/
def frSg1 : Sg := ⟨⟨24, 4194304, 97⟩, ⟨13, 64, 97⟩, 0, 8, 97⟩

/-- The second stage: five row variables, two of them mask variables, 49 positions. -/
def frSg2 : Sg := ⟨⟨21, 131072, 49⟩, ⟨12, 128, 49⟩, 2, 3, 49⟩

/-- The third stage: four row variables, two of them mask variables, 49 positions. -/
def frSg3 : Sg := ⟨⟨17, 8192, 49⟩, ⟨12, 128, 49⟩, 2, 2, 49⟩

/-- The fourth stage: four row variables, two of them mask variables, 50 positions. -/
def frSg4 : Sg := ⟨⟨13, 512, 50⟩, ⟨12, 128, 50⟩, 2, 2, 50⟩

/-- The fifth stage: no row variable, 40 positions. -/
def frSg5 : Sg := ⟨⟨14, 512, 40⟩, ⟨14, 512, 40⟩, 0, 0, 40⟩

/-- The five stages are those of the format's record. -/
theorem fr_stages : frPar.stages = [frSg1.st, frSg2.st, frSg3.st, frSg4.st, frSg5.st] := rfl

/-- The stages' codes are the typed codes: five main codes, and four mask codes, of which the second
serves two stages. The typed link's shape names them by these numbers, with the later stages'
numbers of row variables and of mask variables. -/
theorem fr_codes : recordCodes =
      ⟨#[⟨frSg1.C.a, frSg1.C.l, frSg1.C.r⟩,
          ⟨frSg2.C.a, frSg2.C.l, frSg2.C.r⟩,
          ⟨frSg3.C.a, frSg3.C.l, frSg3.C.r⟩,
          ⟨frSg4.C.a, frSg4.C.l, frSg4.C.r⟩,
          ⟨frSg5.C.a, frSg5.C.l, frSg5.C.r⟩],
        #[⟨frSg1.Z.a, frSg1.Z.l, frSg1.Z.r⟩,
          ⟨frSg2.Z.a, frSg2.Z.l, frSg2.Z.r⟩,
          ⟨frSg4.Z.a, frSg4.Z.l, frSg4.Z.r⟩,
          ⟨frSg5.Z.a, frSg5.Z.l, frSg5.Z.r⟩]⟩ ∧
    frSg3.Z = frSg2.Z ∧ recordLink.code = 0 ∧ recordLink.maskCode = 0 ∧
    recordLink.later =
      [⟨1, 1, frSg2.h + frSg2.g, frSg2.h⟩, ⟨2, 1, frSg3.h + frSg3.g, frSg3.h⟩,
        ⟨3, 2, frSg4.h + frSg4.g, frSg4.h⟩, ⟨4, 3, frSg5.h + frSg5.g, frSg5.h⟩] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The stage of the link's group is the first stage. -/
theorem fr_sg (eM e0 e1 eU : ℕ) : (frSz eM e0 e1 eU).sg 97 = frSg1 := by
  have haR : frPar.aR = 7 := by decide +kernel
  show (⟨frPar.C, frPar.Z, 0, frPar.aR + 1, 97⟩ : Sg) = frSg1
  rw [haR]
  rfl

/-- **The 41 rounds, by the format's makers of rounds**: the link's five, the batching of
2 s + 1 + 2 + 62 + 62 = 129 rows, and the rounds of the proximity test. -/
def frFmt : List Fmt.Round :=
  [Fmt.M3.rLinkPoint frPar.v, Fmt.M2.rSeedN (frPar.aR + frPar.aP), Fmt.M2.rAnswers 2,
      Fmt.M3.rLink frPar.work (frPar.nu0 + frPar.nuj) frPar.T.a, Fmt.M3.rLinkPhi frPar.aPhi,
      Fmt.M2.rBatN (2 * frPar.s + Fmt.M3.nRows frPar)] ++
    Fmt.M1.laterRounds frPar.work 0 (Fmt.M3.width0 frPar) frSg1.st
      [frSg2.st, frSg3.st, frSg4.st, frSg5.st]

/-- **The rounds that the dry run of the block of `verify-on-bytes` states are these.** -/
theorem fr_fmt : recordRounds.map (·.1) = frFmt :=
  Params.rounds_of_parts (by decide +kernel)

/-- The openings of stored tables, round by round, as the library's description has them: at the
round LINK the first table's at the first 62 draws and the copy's at the last 62; elsewhere none. -/
def frStored : List (List Fmt.Stored) :=
  frFmt.map fun r =>
    if r.entry.name == "LINK" then
      [⟨Fmt.M3.shT frPar, frPar.salt, 0, 0, frPar.nu0⟩,
        ⟨Fmt.M3.shT frPar, frPar.salt, 1, frPar.nu0, frPar.nuj⟩]
    else []

/-- **The stored openings that the dry run states are these.** -/
theorem fr_stored : recordRounds.map (·.2) = frStored := by decide +kernel

/-- The description of the chain by `Params.entrySpecOf`, at an empty statement. -/
def frD : XD :=
  Tie.xdOf (Params.entrySpecOf recordRead recordRounds ByteArray.empty) fun _ _ => ByteArray.empty

/-- The description's rounds are the same at every statement. -/
theorem fr_ds_at (st : ByteArray) (stm : ByteArray → ByteArray → ByteArray) :
    (Tie.xdOf (Params.entrySpecOf recordRead recordRounds st) stm).ds = frD.ds :=
  _root_.Run.rds_congr _ _ rfl rfl

/-- The description's stored openings are the same at every statement. -/
theorem fr_xs_at (st : ByteArray) (stm : ByteArray → ByteArray → ByteArray) :
    (Tie.xdOf (Params.entrySpecOf recordRead recordRounds st) stm).xs = frD.xs := rfl

/-- The stored tables have 2^32 positions. -/
theorem fr_a : frD.a = frPar.T.a := by
  unfold XD.a
  rw [show frD.stored = frStored from fr_stored]
  rfl

/-- The two openings of stored tables, both at round number 3. -/
theorem fr_xs : frD.xs = [⟨3, false, 0, 62⟩, ⟨3, true, 62, 62⟩] := by
  unfold XD.xs
  rw [show frD.stored = frStored from fr_stored]
  rfl

/-- No round sends more than one root. -/
theorem fr_roots : ∀ r ∈ frD.base.rounds, r.entry.roots ≤ 1 := by
  rw [show frD.base.rounds = frFmt from fr_fmt]
  decide +kernel

/-- The same description with `frFmt` written in the place of the dry run's rounds. -/
def frBase : Fmt.Spec := { frD.base with rounds := frFmt }

/-- The description's rounds are those made of `frFmt`. -/
theorem fr_ds : frD.ds = rds frBase := _root_.Run.rds_congr _ _ fr_fmt rfl

/-- Round number i of the description, counted from 0; an empty round beyond the list's end. -/
def frRd (i : ℕ) : RD := frD.ds.getD i ⟨e0, .nothing, [], none, []⟩

/-- Round number i of those made of `frFmt`. -/
def frRt (i : ℕ) : RD := (rds frBase).getD i ⟨e0, .nothing, [], none, []⟩

/-- They are the same round. -/
theorem fr_rd (i : ℕ) : frRd i = frRt i := by
  unfold frRd frRt
  rw [fr_ds]

/-- The description has at least five rounds: `frRd 0` to `frRd 4`, then the rest. -/
theorem fr_ds_eq : frD.ds = frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frD.ds.drop 5 := by
  unfold frRd
  rw [fr_ds]
  rfl

end OnBytes.Slice
