-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecBlkSizes.lean: the public numbers of the full-size files of the setting "record
with work", in the forms in which the statements on the program's blocks ask for them.

This file's text was made by a program.
A statement on a block of the program carries hypotheses on public sizes:
which codes the program holds, how many
rows a stage has, which choices the parameters make. At the typed parameter bytes
(`Params.recordRead`) these are closed facts, most of them proved by evaluation of small records of
numbers. Nothing as long as a code word or a table is built.

Main definitions: `frSt1` to `frSt5`, the stages of the proximity test as the program holds them
(`frRest`: all but the first); `frSent2` to `frSent5`, what the message of each code switch holds.
Main theorems:
 `fr_blkCodes`, `fr_test`, `fr_rest_len`, `fr_stageCodes1` to `5`, `fr_base`, `fr_mask`, `fr_small`,
 `fr_ride`, `fr_start`   the codes, the stages, the choices on masks, from what the block starts.
 `fr_tableCode`, `fr_linkFit_par`, `fr_linkFit`, `fr_linkSizes_par`, `fr_linkSizes`,
 `fr_recordNumbers`   the link's shape, held against the record of sizes `frPar` (`_par`) and, as
     records, against the sizes `frSz` on it; the shape's numbers of a table's record.
 `fr_sendFits2` to `5`, `fr_bits2` to `5`   the new message of each code switch has the shape that
     OnBytes/Slice/BlkSendCs.lean asks for.
 `fr_layTrees1` to `5`, `fr_oneTree2` to `4`   how the oracle messages of the link and of each code
     switch are placed in their tree.

What this file does not claim. Nothing on another configuration. Not that `Params.recordRead` is
what the C++ programs hash, or that it follows from public files: the heads of the files of
OnBytes/Params/ that type it say what is tied. Nothing on a key, a record or its rows. Nothing on
soundness.

-/
import OnBytes.Entry.File
import OnBytes.Iop.Link
import OnBytes.Iop.Prox
import OnBytes.Slice.BlkJoints
import OnBytes.Slice.BlkSendCs
import OnBytes.Slice.FullRecCodes

set_option autoImplicit false

namespace OnBytes.Slice
open OnBytes.Params (recordRead IoppStage)

/-! ## The codes and the stages -/

/-- The program's codes: five main codes and four mask codes. -/
theorem fr_blkCodes : recordRead.codes =
    { base := #[⟨24, 4194304, 97⟩, ⟨21, 131072, 49⟩, ⟨17, 8192, 49⟩, ⟨13, 512, 50⟩, ⟨14, 512, 40⟩],
      mask := #[⟨13, 64, 97⟩, ⟨12, 128, 49⟩, ⟨12, 128, 50⟩, ⟨14, 512, 40⟩] } := rfl

/-- The first stage as the program holds it: the group of the two folded rows. -/
def frSt1 : IoppStage := { code := 0, maskCode := 0, k := 8, h := 0 }
/-- The second stage as the program holds it. -/
def frSt2 : IoppStage := { code := 1, maskCode := 1, k := 5, h := 2 }
/-- The third stage as the program holds it. -/
def frSt3 : IoppStage := { code := 2, maskCode := 1, k := 4, h := 2 }
/-- The fourth stage as the program holds it. -/
def frSt4 : IoppStage := { code := 3, maskCode := 2, k := 4, h := 2 }
/-- The fifth stage as the program holds it. -/
def frSt5 : IoppStage := { code := 4, maskCode := 3, k := 0, h := 0 }

/-- The program's stages after the first. -/
def frRest : List IoppStage := [frSt2, frSt3, frSt4, frSt5]

/-- The stages of the proximity test. -/
theorem fr_test : recordRead.link.test = frSt1 :: frRest := by
  decide +kernel

/-- There are at least three stages. -/
theorem fr_rest_len : 2 ≤ frRest.length := by decide

/-- The first stage's codes and numbers of row variables. -/
theorem fr_stageCodes1 : StageCodes frSg1 frSt1 recordRead.codes := by
  rw [fr_blkCodes]
  exact ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The second stage's codes and numbers of row variables. -/
theorem fr_stageCodes2 : StageCodes frSg2 frSt2 recordRead.codes := by
  rw [fr_blkCodes]
  exact ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The third stage's codes and numbers of row variables. -/
theorem fr_stageCodes3 : StageCodes frSg3 frSt3 recordRead.codes := by
  rw [fr_blkCodes]
  exact ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The fourth stage's codes and numbers of row variables. -/
theorem fr_stageCodes4 : StageCodes frSg4 frSt4 recordRead.codes := by
  rw [fr_blkCodes]
  exact ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The fifth stage's codes and numbers of row variables. -/
theorem fr_stageCodes5 : StageCodes frSg5 frSt5 recordRead.codes := by
  rw [fr_blkCodes]
  exact ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The program's base codes, by the numbers that the stages name, are the stages' main codes. -/
theorem fr_base : (recordRead.codes.base[0]?).map codeOf = some frSg1.C ∧
    (recordRead.codes.base[1]?).map codeOf = some frSg2.C ∧
    (recordRead.codes.base[2]?).map codeOf = some frSg3.C ∧
    (recordRead.codes.base[3]?).map codeOf = some frSg4.C ∧
    (recordRead.codes.base[4]?).map codeOf = some frSg5.C := by
  rw [fr_blkCodes]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The program's mask codes, by the numbers that the stages name, are the stages' mask codes. -/
theorem fr_mask : (recordRead.codes.mask[0]?).map codeOf = some frSg1.Z ∧
    (recordRead.codes.mask[1]?).map codeOf = some frSg2.Z ∧
    (recordRead.codes.mask[1]?).map codeOf = some frSg3.Z ∧
    (recordRead.codes.mask[2]?).map codeOf = some frSg4.Z ∧
    (recordRead.codes.mask[3]?).map codeOf = some frSg5.Z := by
  rw [fr_blkCodes]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- No code of a stage is longer than 2^32. -/
theorem fr_small : (frSg1.C.a ≤ 32 ∧ frSg1.Z.a ≤ 32) ∧
    (frSg2.C.a ≤ 32 ∧ frSg2.Z.a ≤ 32) ∧
    (frSg3.C.a ≤ 32 ∧ frSg3.Z.a ≤ 32) ∧
    (frSg4.C.a ≤ 32 ∧ frSg4.Z.a ≤ 32) ∧
    (frSg5.C.a ≤ 32 ∧ frSg5.Z.a ≤ 32) := by
  decide

/-- The masks of the later stages go out with the switch that makes the stage, and the first
stage's mask is sent ahead. -/
theorem fr_ride : recordRead.link.choice.masksRide = true ∧
    recordRead.link.masksAhead = true := ⟨rfl, rfl⟩

/-- From what the block of an entry's chain starts: tree number 0, one answer to a sample, the
codes. -/
theorem fr_start : (Entry.start recordRead).firstTree = 0 ∧
    (Entry.start recordRead).samples = 1 ∧
    (Entry.start recordRead).st.codes = recordRead.codes :=
  ⟨rfl, rfl, rfl⟩

/-! ## The link -/

/-- The code of a stored table is that of the record of sizes. -/
theorem fr_tableCode : codeOf recordRead.link.table.code = frPar.T := rfl

/-- What the statement on the rows of the program's link asks of the sizes and shapes, at the record
of sizes. n is the number of answers to a sample. -/
theorem fr_linkFit_par (n : ℕ) :
    recordRead.link.entryBits = frPar.aPhi ∧
      codeOf (recordRead.link.side false n).index.code = frPar.T ∧
      codeOf (recordRead.link.side true n).index.code = frPar.T ∧
      frPar.C.l = 2 ^ frPar.aP ∧ frPar.T.a ≤ 32 ∧ 0 < frPar.T.l := by
  have h1 : recordRead.link.entryBits = frPar.aPhi := by decide +kernel
  have h4 : frPar.C.l = 2 ^ frPar.aP ∧ frPar.T.a ≤ 32 ∧ 0 < frPar.T.l := by decide +kernel
  exact ⟨h1, fr_tableCode, fr_tableCode, h4⟩

/-- The same as a record, at the sizes `frSz`, whatever the radii. -/
theorem fr_linkFit (eM e0 e1 eU : ℕ) :
    LinkFit (frSz eM e0 e1 eU) recordRead.link (recordRead.link.side false 1)
      (recordRead.link.side true 1) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := fr_linkFit_par 1
  exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- Further numbers of the link, at the record of sizes: how a folded row is placed in its oracle
message; the entries that are compared; the draws at the two tables; the rows of a folded row's
message; the length of such a row; the row variables and the length of a stored table; the
coordinates of the point of a folded row's sample. -/
theorem fr_linkSizes_par :
    vectorLay recordRead.codes (recordRead.link.side false 1).u
        recordRead.link.rowsHigh = ⟨frPar.aR, frPar.aP, true⟩ ∧
      recordRead.link.cut = frPar.cut ∧
      recordRead.link.columnsFirst = frPar.nu0 ∧
      recordRead.link.columnsFurther = frPar.nuj ∧
      recordRead.link.rows = frPar.R ∧
      (recordRead.codes.base.getD recordRead.link.code default).ell = frPar.C.l ∧
      recordRead.link.table.v = frPar.v ∧
      recordRead.link.table.code.logN = frPar.T.a ∧
      (Send.cube recordRead.codes (recordRead.link.side false 1).u).bits =
        frPar.aR + frPar.aP := by
  decide +kernel

/-- The same as a record, at the sizes `frSz`, whatever the radii, and at the codes from which the
block starts. -/
theorem fr_linkSizes (eM e0 e1 eU : ℕ) :
    LinkSizes (frSz eM e0 e1 eU) recordRead.link (Entry.start recordRead).st.codes := by
  rw [fr_start.2.2]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := fr_linkSizes_par
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

/-- The shape's numbers of a record: one answer a row, and the coordinates of a seed's point. A
row's message has room for the pad. -/
theorem fr_recordNumbers : recordRead.link.table.answers = 1 ∧
    recordRead.link.table.cubeBits = 29 ∧ 3 * 1 ≤ frPar.T.l := by
  decide +kernel

/-! ## The new messages of the code switches -/

/-- The new message of the first code switch has the shape that is asked for. -/
theorem fr_sendFits2 : SendFits frSg2 recordRead.codes
    (switchTargetStage frSt2.code frSt2.maskCode frSt2.k frSt2.h 1).shape := by
  have hC : (recordRead.codes.base.getD 1 default).ell = frSg2.C.l := by
    rw [fr_blkCodes]
    rfl
  have hZ : (recordRead.codes.mask.getD 1 default).ell = frSg2.Z.l := by
    rw [fr_blkCodes]
    rfl
  exact sendFits_stage fr_fit12 recordRead.codes 1 1 hC hZ

/-- The new message of the second code switch has the shape that is asked for. -/
theorem fr_sendFits3 : SendFits frSg3 recordRead.codes
    (switchTargetStage frSt3.code frSt3.maskCode frSt3.k frSt3.h 1).shape := by
  have hC : (recordRead.codes.base.getD 2 default).ell = frSg3.C.l := by
    rw [fr_blkCodes]
    rfl
  have hZ : (recordRead.codes.mask.getD 1 default).ell = frSg3.Z.l := by
    rw [fr_blkCodes]
    rfl
  exact sendFits_stage fr_fit23 recordRead.codes 2 1 hC hZ

/-- The new message of the third code switch has the shape that is asked for. -/
theorem fr_sendFits4 : SendFits frSg4 recordRead.codes
    (switchTargetStage frSt4.code frSt4.maskCode frSt4.k frSt4.h 1).shape := by
  have hC : (recordRead.codes.base.getD 3 default).ell = frSg4.C.l := by
    rw [fr_blkCodes]
    rfl
  have hZ : (recordRead.codes.mask.getD 2 default).ell = frSg4.Z.l := by
    rw [fr_blkCodes]
    rfl
  exact sendFits_stage fr_fit34 recordRead.codes 3 2 hC hZ

/-- The new message of the fourth code switch has the shape that is asked for. -/
theorem fr_sendFits5 : SendFits frSg5 recordRead.codes
    (switchTargetStage frSt5.code frSt5.maskCode frSt5.k frSt5.h 1).shape := by
  have hC : (recordRead.codes.base.getD 4 default).ell = frSg5.C.l := by
    rw [fr_blkCodes]
    rfl
  have hZ : (recordRead.codes.mask.getD 3 default).ell = frSg5.Z.l := by
    rw [fr_blkCodes]
    rfl
  exact sendFits_stage fr_fit45 recordRead.codes 4 3 hC hZ

/-- The point of the sample at the first code switch has the second stage's number of
coordinates. -/
theorem fr_bits2 : (Send.cube recordRead.codes
    (switchTargetStage frSt2.code frSt2.maskCode (frSg2.h + frSg2.g) frSg2.h 1).shape).bits =
      frSg2.st.na :=
  fr_sendFits2.bits

/-- The point of the sample at the second code switch has the third stage's number of
coordinates. -/
theorem fr_bits3 : (Send.cube recordRead.codes
    (switchTargetStage frSt3.code frSt3.maskCode (frSg3.h + frSg3.g) frSg3.h 1).shape).bits =
      frSg3.st.na :=
  fr_sendFits3.bits

/-- The point of the sample at the third code switch has the fourth stage's number of
coordinates. -/
theorem fr_bits4 : (Send.cube recordRead.codes
    (switchTargetStage frSt4.code frSt4.maskCode (frSg4.h + frSg4.g) frSg4.h 1).shape).bits =
      frSg4.st.na :=
  fr_sendFits4.bits

/-- The point of the sample at the fourth code switch has the fifth stage's number of
coordinates. -/
theorem fr_bits5 : (Send.cube recordRead.codes
    (switchTargetStage frSt5.code frSt5.maskCode (frSg5.h + frSg5.g) frSg5.h 1).shape).bits =
      frSg5.st.na :=
  fr_sendFits5.bits

/-! ## The trees of the link's message and of the code switches' messages -/

/-- What the prover's message of the first code switch holds: the new stage's oracle message, and
with it the fresh mask of the new stage's fold. -/
def frSent2 : Array OracleNotice :=
  #[⟨(switchTargetStage frSt2.code frSt2.maskCode frSt2.k frSt2.h 1).shape,
      (switchTargetStage frSt2.code frSt2.maskCode frSt2.k frSt2.h 1).leafClass⟩] ++
    #[foldMaskNotice (ioppFoldShape frSt2 {})]

/-- What the prover's message of the second code switch holds: the new stage's oracle message, and
with it the fresh mask of the new stage's fold. -/
def frSent3 : Array OracleNotice :=
  #[⟨(switchTargetStage frSt3.code frSt3.maskCode frSt3.k frSt3.h 1).shape,
      (switchTargetStage frSt3.code frSt3.maskCode frSt3.k frSt3.h 1).leafClass⟩] ++
    #[foldMaskNotice (ioppFoldShape frSt3 {})]

/-- What the prover's message of the third code switch holds: the new stage's oracle message, and
with it the fresh mask of the new stage's fold. -/
def frSent4 : Array OracleNotice :=
  #[⟨(switchTargetStage frSt4.code frSt4.maskCode frSt4.k frSt4.h 1).shape,
      (switchTargetStage frSt4.code frSt4.maskCode frSt4.k frSt4.h 1).leafClass⟩] ++
    #[foldMaskNotice (ioppFoldShape frSt4 {})]

/-- What the prover's message of the fourth code switch holds: the last stage's oracle message, and
with it the masking oracle of the base case. -/
def frSent5 : Array OracleNotice :=
  #[⟨(switchTargetStage frSt5.code frSt5.maskCode frSt5.k frSt5.h 1).shape,
      (switchTargetStage frSt5.code frSt5.maskCode frSt5.k frSt5.h 1).leafClass⟩] ++
    #[baseMaskNotice frSt5.code frSt5.maskCode 1 0]

/-- How the link's three oracle messages are placed: in one tree, in the order of sending. -/
theorem fr_layTrees1 : layTrees recordRead.codes (linkMessage recordRead.link 1) =
    some { tree := #[0, 0, 0], part := #[0, 1, 2],
           shapes := #[⟨24, 13, #[321, 321, 0], #[0, 0, 3]⟩] } := by
  decide +kernel

/-- How the two oracle messages of the first code switch are placed. -/
theorem fr_layTrees2 : layTrees recordRead.codes frSent2 =
    some { tree := #[0, 0], part := #[0, 1],
           shapes := #[⟨21, 12, #[96, 0], #[12, 12]⟩] } := by
  decide +kernel

/-- How the two oracle messages of the second code switch are placed. -/
theorem fr_layTrees3 : layTrees recordRead.codes frSent3 =
    some { tree := #[0, 0], part := #[0, 1],
           shapes := #[⟨17, 12, #[48, 0], #[12, 12]⟩] } := by
  decide +kernel

/-- How the two oracle messages of the third code switch are placed. -/
theorem fr_layTrees4 : layTrees recordRead.codes frSent4 =
    some { tree := #[0, 0], part := #[0, 1],
           shapes := #[⟨13, 12, #[48, 0], #[12, 12]⟩] } := by
  decide +kernel

/-- How the two oracle messages of the fourth code switch are placed. -/
theorem fr_layTrees5 : layTrees recordRead.codes frSent5 =
    some { tree := #[0, 0], part := #[0, 1],
           shapes := #[⟨14, 14, #[3, 3], #[3, 3]⟩] } := by
  decide +kernel

/-- The first code switch: all oracle messages are in one tree, in their order. The tree has as
many leaves as the second stage's main code has positions, and a column has each message's symbols
in turn. -/
theorem fr_oneTree2 : ∀ lay, layTrees recordRead.codes frSent2 = some lay →
    ∃ sh : TreeShape, lay.shapes = #[sh] ∧ sh.logN = frSg2.C.a ∧
      (∀ i, i < frSent2.size → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
      sh.mainSymbols =
        ((frSent2.toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray ∧
      sh.maskSymbols = ((frSent2.toList.map (·.shape)).map fun s => s.maskRows * 3).toArray := by
  intro lay h
  rw [fr_layTrees2] at h
  obtain rfl := Option.some.inj h
  exact ⟨_, rfl, rfl, by decide, by decide, by decide⟩

/-- The second code switch: all oracle messages are in one tree, in their order. The tree has as
many leaves as the third stage's main code has positions, and a column has each message's symbols
in turn. -/
theorem fr_oneTree3 : ∀ lay, layTrees recordRead.codes frSent3 = some lay →
    ∃ sh : TreeShape, lay.shapes = #[sh] ∧ sh.logN = frSg3.C.a ∧
      (∀ i, i < frSent3.size → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
      sh.mainSymbols =
        ((frSent3.toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray ∧
      sh.maskSymbols = ((frSent3.toList.map (·.shape)).map fun s => s.maskRows * 3).toArray := by
  intro lay h
  rw [fr_layTrees3] at h
  obtain rfl := Option.some.inj h
  exact ⟨_, rfl, rfl, by decide, by decide, by decide⟩

/-- The third code switch: all oracle messages are in one tree, in their order. The tree has as
many leaves as the fourth stage's main code has positions, and a column has each message's symbols
in turn. -/
theorem fr_oneTree4 : ∀ lay, layTrees recordRead.codes frSent4 = some lay →
    ∃ sh : TreeShape, lay.shapes = #[sh] ∧ sh.logN = frSg4.C.a ∧
      (∀ i, i < frSent4.size → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
      sh.mainSymbols =
        ((frSent4.toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray ∧
      sh.maskSymbols = ((frSent4.toList.map (·.shape)).map fun s => s.maskRows * 3).toArray := by
  intro lay h
  rw [fr_layTrees4] at h
  obtain rfl := Option.some.inj h
  exact ⟨_, rfl, rfl, by decide, by decide, by decide⟩

end OnBytes.Slice
