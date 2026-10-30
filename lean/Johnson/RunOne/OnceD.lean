-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/OnceD.lean: what the calls of a chain query share, at the data of a file's page
(`fillJ`, OnBytes/Maker/Page/Fill.lean), from ONE reading of the query's plain part, ALONG THE DATA;
and a round's need of blocks.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

It imports Johnson/RunOne/OnceCore.lean and Johnson/RunOne/PartD.lean alone: no runner and no log.
In a namespace of its own (`Johnson.RunOne.Lite`).

Main names.
  `partAtD`; `partAtD_eq`: `partAt` with `partOfD` in the place of `partOf`.
  `onceD`; `onceD_eq`: `onceD C D tF tJ t3 rd S q = onceJ (fillJ C D tF tJ t3 rd S) q`.
  `needAt`: a round's number of blocks by the format's own formula, and one more at a round with
    work; by the typed round; read off the data.
Limits. That `needAt` is what the wiring reads is not shown here. Nothing on soundness.

-/
import Johnson.RunOne.OnceCore
import Johnson.RunOne.PartD

set_option autoImplicit false

namespace Johnson.RunOne.Lite

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run
open _root_.Run.PQ (CK)
open OnBytes OnBytes.Maker OnBytes.Maker.Page Johnson.RunOne

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF)
  (tJ : TJ) (t3 : T3)
  (rd : PBt L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))

/-- What a plain part of the interface's protocol is, through the read-back, read along the data. -/
def partAtD (z : PBt L t) : PartJ TF TJ T3 :=
  match rd z with
  | some w => partOfD C D tF tJ t3 w
  | none => .nothing

theorem partAtD_eq (z : PBt L t) : partAtD C D tF tJ t3 rd z = partAt C D tF tJ t3 rd z := by
  unfold partAtD partAt
  cases rd z with
  | none => rfl
  | some w => exact partOfD_eq C D tF tJ t3 w

/-- What the calls of a chain query share, at the data of `fillJ`: one reading, along the data. -/
def onceD (S : SilentJ X TF TJ T3) (q : FbIn 256 L t) : OnceJ :=
  onceFill D S (partAtD C D tF tJ t3 rd) q

/-- **It is `onceJ` at `fillJ`.** -/
theorem onceD_eq (S : SilentJ X TF TJ T3) (q : FbIn 256 L t) :
    onceD C D tF tJ t3 rd S q = onceJ (fillJ C D tF tJ t3 rd S) q := by
  unfold onceD onceFill
  rw [partAtD_eq]
  exact onceFill_eq C D tF tJ t3 rd S q

/-- A round's number of blocks by the format's own formula, and one more where the round has work
(the typed block 0 is then the test's, and the draws' blocks follow it: `chalGrind`,
Iop/GrindWire.lean); by the typed round; 0 where no written round stands. -/
def needAt (D : WholeD) (i : ℕ) : ℕ :=
  ((rdAt D i).map fun d =>
    Fmt.blocksFor (Fmt.wordsAtMost d.entry d.kind) + (if d.entry.work = 0 then 0 else 1)).getD 0

end Johnson.RunOne.Lite

#print axioms Johnson.RunOne.Lite.partAtD_eq
#print axioms Johnson.RunOne.Lite.onceD_eq
