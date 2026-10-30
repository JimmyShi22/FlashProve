-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecBlkSizes.lean: the public numbers of the small files of the setting "record
with work", in the forms in which the statements on the program's blocks ask for them.

This file's text was made by a program.
A statement on a block of the program carries hypotheses on public sizes:
which codes the program holds, how many
rows a stage has, which choices the parameters make. At the typed parameter bytes
(`Params.smallRecordRead`) these are closed facts, most of them proved by evaluation of small
records of numbers. Nothing as long as a code word or a table is built.

Main definitions: `srSt1` to `srSt3`, the stages of the proximity test as the program holds them
(`srRest`: all but the first); `srSent2` to `srSent3`, what the message of each code switch holds.
Main theorems:
 `sr_blkCodes`, `sr_test`, `sr_rest_len`, `sr_stageCodes1` to `3`, `sr_base`, `sr_mask`, `sr_small`,
 `sr_ride`, `sr_start`   the codes, the stages, the choices on masks, from what the block starts.
 `sr_tableCode`, `sr_linkFit_par`, `sr_linkFit`, `sr_linkSizes_par`, `sr_linkSizes`,
 `sr_recordNumbers`   the link's shape, held against the record of sizes `srPar` (`_par`) and, as
     records, against the sizes `srSz` on it; the shape's numbers of a table's record.
 `sr_sendFits2` to `3`, `sr_bits2` to `3`   the new message of each code switch has the shape that
     OnBytes/Slice/BlkSendCs.lean asks for.
 `sr_layTrees1` to `3`, `sr_oneTree2`   how the oracle messages of the link and of each code switch
     are placed in their tree.

What this file does not claim. Nothing on another configuration. Not that `Params.smallRecordRead`
is what the C++ programs hash, or that it follows from public files: the heads of the files of
OnBytes/Params/ that type it say what is tied. Nothing on a key, a record or its rows. Nothing on
soundness.

-/
import OnBytes.Entry.File
import OnBytes.Iop.Link
import OnBytes.Iop.Prox
import OnBytes.Slice.BlkJoints
import OnBytes.Slice.BlkSendCs
import OnBytes.Slice.SmallRecCodes

set_option autoImplicit false

namespace OnBytes.Slice
open OnBytes.Params (smallRecordRead IoppStage)

/-! ## The codes and the stages -/

/-- The program's codes: two main codes and three mask codes. -/
theorem sr_blkCodes : smallRecordRead.codes =
    { base := #[⟨17, 32768, 97⟩, ⟨14, 2048, 66⟩],
      mask := #[⟨13, 64, 97⟩, ⟨12, 128, 66⟩, ⟨14, 512, 66⟩] } := rfl

/-- The first stage as the program holds it: the group of the two folded rows. -/
def srSt1 : IoppStage := { code := 0, maskCode := 0, k := 6, h := 0 }
/-- The second stage as the program holds it. -/
def srSt2 : IoppStage := { code := 1, maskCode := 1, k := 4, h := 2 }
/-- The third stage as the program holds it. -/
def srSt3 : IoppStage := { code := 1, maskCode := 2, k := 0, h := 0 }

/-- The program's stages after the first. -/
def srRest : List IoppStage := [srSt2, srSt3]

/-- The stages of the proximity test. -/
theorem sr_test : smallRecordRead.link.test = srSt1 :: srRest := by
  decide +kernel

/-- There are at least three stages. -/
theorem sr_rest_len : 2 ≤ srRest.length := by decide

/-- The first stage's codes and numbers of row variables. -/
theorem sr_stageCodes1 : StageCodes srSg1 srSt1 smallRecordRead.codes := by
  rw [sr_blkCodes]
  exact ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The second stage's codes and numbers of row variables. -/
theorem sr_stageCodes2 : StageCodes srSg2 srSt2 smallRecordRead.codes := by
  rw [sr_blkCodes]
  exact ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The third stage's codes and numbers of row variables. -/
theorem sr_stageCodes3 : StageCodes srSg3 srSt3 smallRecordRead.codes := by
  rw [sr_blkCodes]
  exact ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The program's base codes, by the numbers that the stages name, are the stages' main codes. -/
theorem sr_base : (smallRecordRead.codes.base[0]?).map codeOf = some srSg1.C ∧
    (smallRecordRead.codes.base[1]?).map codeOf = some srSg2.C ∧
    (smallRecordRead.codes.base[1]?).map codeOf = some srSg3.C := by
  rw [sr_blkCodes]
  exact ⟨rfl, rfl, rfl⟩

/-- The program's mask codes, by the numbers that the stages name, are the stages' mask codes. -/
theorem sr_mask : (smallRecordRead.codes.mask[0]?).map codeOf = some srSg1.Z ∧
    (smallRecordRead.codes.mask[1]?).map codeOf = some srSg2.Z ∧
    (smallRecordRead.codes.mask[2]?).map codeOf = some srSg3.Z := by
  rw [sr_blkCodes]
  exact ⟨rfl, rfl, rfl⟩

/-- No code of a stage is longer than 2^32. -/
theorem sr_small : (srSg1.C.a ≤ 32 ∧ srSg1.Z.a ≤ 32) ∧
    (srSg2.C.a ≤ 32 ∧ srSg2.Z.a ≤ 32) ∧
    (srSg3.C.a ≤ 32 ∧ srSg3.Z.a ≤ 32) := by
  decide

/-- The masks of the later stages go out with the switch that makes the stage, and the first
stage's mask is sent ahead. -/
theorem sr_ride : smallRecordRead.link.choice.masksRide = true ∧
    smallRecordRead.link.masksAhead = true := ⟨rfl, rfl⟩

/-- From what the block of an entry's chain starts: tree number 0, one answer to a sample, the
codes. -/
theorem sr_start : (Entry.start smallRecordRead).firstTree = 0 ∧
    (Entry.start smallRecordRead).samples = 1 ∧
    (Entry.start smallRecordRead).st.codes = smallRecordRead.codes :=
  ⟨rfl, rfl, rfl⟩

/-! ## The link -/

/-- The code of a stored table is that of the record of sizes. -/
theorem sr_tableCode : codeOf smallRecordRead.link.table.code = srPar.T := rfl

/-- What the statement on the rows of the program's link asks of the sizes and shapes, at the record
of sizes. n is the number of answers to a sample. -/
theorem sr_linkFit_par (n : ℕ) :
    smallRecordRead.link.entryBits = srPar.aPhi ∧
      codeOf (smallRecordRead.link.side false n).index.code = srPar.T ∧
      codeOf (smallRecordRead.link.side true n).index.code = srPar.T ∧
      srPar.C.l = 2 ^ srPar.aP ∧ srPar.T.a ≤ 32 ∧ 0 < srPar.T.l := by
  have h1 : smallRecordRead.link.entryBits = srPar.aPhi := by decide +kernel
  have h4 : srPar.C.l = 2 ^ srPar.aP ∧ srPar.T.a ≤ 32 ∧ 0 < srPar.T.l := by decide +kernel
  exact ⟨h1, sr_tableCode, sr_tableCode, h4⟩

/-- The same as a record, at the sizes `srSz`, whatever the radii. -/
theorem sr_linkFit (eM e0 e1 eU : ℕ) :
    LinkFit (srSz eM e0 e1 eU) smallRecordRead.link (smallRecordRead.link.side false 1)
      (smallRecordRead.link.side true 1) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := sr_linkFit_par 1
  exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- Further numbers of the link, at the record of sizes: how a folded row is placed in its oracle
message; the entries that are compared; the draws at the two tables; the rows of a folded row's
message; the length of such a row; the row variables and the length of a stored table; the
coordinates of the point of a folded row's sample. -/
theorem sr_linkSizes_par :
    vectorLay smallRecordRead.codes (smallRecordRead.link.side false 1).u
        smallRecordRead.link.rowsHigh = ⟨srPar.aR, srPar.aP, true⟩ ∧
      smallRecordRead.link.cut = srPar.cut ∧
      smallRecordRead.link.columnsFirst = srPar.nu0 ∧
      smallRecordRead.link.columnsFurther = srPar.nuj ∧
      smallRecordRead.link.rows = srPar.R ∧
      (smallRecordRead.codes.base.getD smallRecordRead.link.code default).ell = srPar.C.l ∧
      smallRecordRead.link.table.v = srPar.v ∧
      smallRecordRead.link.table.code.logN = srPar.T.a ∧
      (Send.cube smallRecordRead.codes (smallRecordRead.link.side false 1).u).bits =
        srPar.aR + srPar.aP := by
  decide +kernel

/-- The same as a record, at the sizes `srSz`, whatever the radii, and at the codes from which the
block starts. -/
theorem sr_linkSizes (eM e0 e1 eU : ℕ) :
    LinkSizes (srSz eM e0 e1 eU) smallRecordRead.link (Entry.start smallRecordRead).st.codes := by
  rw [sr_start.2.2]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := sr_linkSizes_par
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

/-- The shape's numbers of a record: one answer a row, and the coordinates of a seed's point. A
row's message has room for the pad. -/
theorem sr_recordNumbers : smallRecordRead.link.table.answers = 1 ∧
    smallRecordRead.link.table.cubeBits = 19 ∧ 3 * 1 ≤ srPar.T.l := by
  decide +kernel

/-! ## The new messages of the code switches -/

/-- The new message of the first code switch has the shape that is asked for. -/
theorem sr_sendFits2 : SendFits srSg2 smallRecordRead.codes
    (switchTargetStage srSt2.code srSt2.maskCode srSt2.k srSt2.h 1).shape := by
  have hC : (smallRecordRead.codes.base.getD 1 default).ell = srSg2.C.l := by
    rw [sr_blkCodes]
    rfl
  have hZ : (smallRecordRead.codes.mask.getD 1 default).ell = srSg2.Z.l := by
    rw [sr_blkCodes]
    rfl
  exact sendFits_stage sr_fit12 smallRecordRead.codes 1 1 hC hZ

/-- The new message of the second code switch has the shape that is asked for. -/
theorem sr_sendFits3 : SendFits srSg3 smallRecordRead.codes
    (switchTargetStage srSt3.code srSt3.maskCode srSt3.k srSt3.h 1).shape := by
  have hC : (smallRecordRead.codes.base.getD 1 default).ell = srSg3.C.l := by
    rw [sr_blkCodes]
    rfl
  have hZ : (smallRecordRead.codes.mask.getD 2 default).ell = srSg3.Z.l := by
    rw [sr_blkCodes]
    rfl
  exact sendFits_stage sr_fit23 smallRecordRead.codes 1 2 hC hZ

/-- The point of the sample at the first code switch has the second stage's number of
coordinates. -/
theorem sr_bits2 : (Send.cube smallRecordRead.codes
    (switchTargetStage srSt2.code srSt2.maskCode (srSg2.h + srSg2.g) srSg2.h 1).shape).bits =
      srSg2.st.na :=
  sr_sendFits2.bits

/-- The point of the sample at the second code switch has the third stage's number of
coordinates. -/
theorem sr_bits3 : (Send.cube smallRecordRead.codes
    (switchTargetStage srSt3.code srSt3.maskCode (srSg3.h + srSg3.g) srSg3.h 1).shape).bits =
      srSg3.st.na :=
  sr_sendFits3.bits

/-! ## The trees of the link's message and of the code switches' messages -/

/-- What the prover's message of the first code switch holds: the new stage's oracle message, and
with it the fresh mask of the new stage's fold. -/
def srSent2 : Array OracleNotice :=
  #[⟨(switchTargetStage srSt2.code srSt2.maskCode srSt2.k srSt2.h 1).shape,
      (switchTargetStage srSt2.code srSt2.maskCode srSt2.k srSt2.h 1).leafClass⟩] ++
    #[foldMaskNotice (ioppFoldShape srSt2 {})]

/-- What the prover's message of the second code switch holds: the last stage's oracle message, and
with it the masking oracle of the base case. -/
def srSent3 : Array OracleNotice :=
  #[⟨(switchTargetStage srSt3.code srSt3.maskCode srSt3.k srSt3.h 1).shape,
      (switchTargetStage srSt3.code srSt3.maskCode srSt3.k srSt3.h 1).leafClass⟩] ++
    #[baseMaskNotice srSt3.code srSt3.maskCode 1 0]

/-- How the link's three oracle messages are placed: in one tree, in the order of sending. -/
theorem sr_layTrees1 : layTrees smallRecordRead.codes (linkMessage smallRecordRead.link 1) =
    some { tree := #[0, 0, 0], part := #[0, 1, 2],
           shapes := #[⟨17, 13, #[54, 54, 0], #[0, 0, 3]⟩] } := by
  decide +kernel

/-- How the two oracle messages of the first code switch are placed. -/
theorem sr_layTrees2 : layTrees smallRecordRead.codes srSent2 =
    some { tree := #[0, 0], part := #[0, 1],
           shapes := #[⟨14, 12, #[48, 0], #[12, 12]⟩] } := by
  decide +kernel

/-- How the two oracle messages of the second code switch are placed. -/
theorem sr_layTrees3 : layTrees smallRecordRead.codes srSent3 =
    some { tree := #[0, 0], part := #[0, 1],
           shapes := #[⟨14, 14, #[3, 3], #[3, 3]⟩] } := by
  decide +kernel

/-- The first code switch: all oracle messages are in one tree, in their order. The tree has as
many leaves as the second stage's main code has positions, and a column has each message's symbols
in turn. -/
theorem sr_oneTree2 : ∀ lay, layTrees smallRecordRead.codes srSent2 = some lay →
    ∃ sh : TreeShape, lay.shapes = #[sh] ∧ sh.logN = srSg2.C.a ∧
      (∀ i, i < srSent2.size → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
      sh.mainSymbols =
        ((srSent2.toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray ∧
      sh.maskSymbols = ((srSent2.toList.map (·.shape)).map fun s => s.maskRows * 3).toArray := by
  intro lay h
  rw [sr_layTrees2] at h
  obtain rfl := Option.some.inj h
  exact ⟨_, rfl, rfl, by decide, by decide, by decide⟩

end OnBytes.Slice
