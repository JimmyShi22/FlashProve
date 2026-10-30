-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/Lengths.lean: how many bytes the spellings of four parameter items have, as sums
over the values' parts; and so that each item of a proof's first chain has fewer than 2 ^ 64 bytes,
where five numbers are below 2 ^ 64. General: no value is named.

Why. The law that a chain's parameter bytes are read back (`Given.read_spelled`,
OnBytes/Params/ToyDescriptions.lean) asks that each item's value have fewer than 2 ^ 64 bytes. At
the full size the item "layout" has some 400,000 bytes. With its length as a sum, the bound can be
shown without laying these bytes in a row. The library has the like for the other items
(OnBytes/Params/Fit/StagesFew.lean, Johnson/Goal/Conditions/KeyBytesFitAtScope.lean).

`size_spellBlock`, `size_spellArray`, `size_spellLayout`: the item "layout"; `arraySize`,
`layoutSize`: the sums. `size_spellReqMessage`, `size_spellReqLink`, `size_spellNotice`,
`size_spellReq`: the item "request's shape"; `reqSize`: the sum. `size_spellWord`,
`size_spellWords`: a number, a list of numbers. `short_first`: the seven items of a proof's first
chain.

Limits. Lengths alone. The five bounds of `short_first` are premises. Nothing on soundness.

-/
import Johnson.AtFull.Made.ReadsOfConfigure
import OnBytes.Params.Fit.StagesFew
import Johnson.Flat.ParamsSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params

theorem size_spellWord (n : Nat) : (spellWord n).size = 8 := rfl

theorem size_spellWords (l : List Nat) : (spellWords l).size = 8 + 8 * l.length :=
  size_listOf spellWord 8 size_spellWord l

/-! ## "layout" -/

theorem size_spellBlock (b : LaidBlock) : (spellBlock b).size = 72 := by
  unfold spellBlock
  rw [ByteArray.size_append, size_spellRow, size_bool]
  rfl

/-- The bytes of an array's spelling: the word of the name's length and the name; three words; the
word of the number of blocks and 72 bytes for each block. -/
def arraySize (a : ReqArray) : Nat := 40 + (Fmt.ascii a.name).size + 72 * a.blocks.length

theorem size_spellArray (a : ReqArray) : (spellArray a).size = arraySize a := by
  unfold spellArray arraySize
  rw [ByteArray.size_append, ByteArray.size_append, Fmt.size_textS, size_spellRow,
    size_listOf spellBlock 72 size_spellBlock]
  simp only [List.length_cons, List.length_nil]
  omega

/-- The bytes of a layout's spelling. -/
def layoutSize (y : ReqLayout) : Nat := 8 + (y.link.map fun l => 8 + (l.map arraySize).sum).sum

theorem size_spellLayout (y : ReqLayout) : (spellLayout y).size = layoutSize y := by
  simp only [spellLayout, layoutSize, Fmt.size_list, size_spellArray]

/-! ## "request's shape" -/

theorem size_spellReqMessage (m : ReqMessage) : (spellReqMessage m).size = 48 := by
  unfold spellReqMessage
  rw [size_spellRow]
  rfl

theorem size_spellReqLink (l : ReqLink) : (spellReqLink l).size = 16 + 48 * l.messages.length := by
  unfold spellReqLink
  rw [ByteArray.size_append, size_spellWord, size_listOf spellReqMessage 48 size_spellReqMessage]
  omega

theorem size_spellNotice (n : OracleNotice) : (spellNotice n).size = 56 := by
  unfold spellNotice
  rw [ByteArray.size_append, size_spellShape, size_spellWord]

/-- The bytes of the spelling of a chain of links: two words; the links; the notices at the start;
the word of the answers; the stages of the last test but the first; the word of the choice. -/
def reqSize (s : ReqShape) : Nat :=
  16 + (8 + (s.link.map fun l => 16 + 48 * l.messages.length).sum) + (8 + 56 * s.atStart.length) +
    8 + (8 + 32 * (s.last.drop 1).length) + 8

theorem size_spellReq (s : ReqShape) : (spellReq s).size = reqSize s := by
  unfold spellReq reqSize spellChoice
  simp only [ByteArray.size_append]
  rw [size_spellRow, Fmt.size_list spellReqLink, size_listOf spellNotice 56 size_spellNotice,
    size_spellStages, size_spellWord, size_bool]
  simp only [size_spellReqLink, List.length_cons, List.length_nil]

/-! ## The seven items of a proof's first chain -/

theorem short_first {l : Lines} {x : Shapes} {z : Sized}
    (h1 : 16 + 24 * z.proof.codes.base.size + 24 * z.proof.codes.mask.size < 2 ^ 64)
    (h2 : 1024 + 32 * (z.proof.batch.shape.testU.length + z.proof.batch.shape.testOmega.length +
      z.proof.batch.shape.testOwn.length + z.proof.batch.shape.testOwnOmega.length) < 2 ^ 64)
    (h3 : reqSize z.proof.request < 2 ^ 64) (h4 : layoutSize x.layout < 2 ^ 64)
    (h5 : 8 + 8 * x.identifiers.length < 2 ^ 64) : Short (madeFirstItems l x z) := by
  intro y hy
  simp only [madeFirstItems, madeLinItems, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hy
  rcases hy with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl
  · show (spellCodes z.proof.codes).size < 2 ^ 64
    rw [size_spellCodes]
    exact h1
  · show (spellLin z.proof.batch.shape).size < 2 ^ 64
    exact Nat.lt_of_le_of_lt (size_spellLin z.proof.batch.shape) h2
  · show (spellReq z.proof.request).size < 2 ^ 64
    rw [size_spellReq]
    exact h3
  · show (spellLayout x.layout).size < 2 ^ 64
    rw [size_spellLayout]
    exact h4
  · show (spellWords x.identifiers).size < 2 ^ 64
    rw [size_spellWords]
    exact h5
  · show (spellWord x.sub.pendingRows).size < 2 ^ 64
    rw [size_spellWord]
    omega
  · show (spellBinding ⟨clog2 l.slots, z.set.saltBytes⟩).size < 2 ^ 64
    unfold spellBinding
    rw [size_spellRow]
    simp only [List.length_cons, List.length_nil]
    omega

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.size_spellWord
#print axioms Johnson.AtFull.Made.size_spellWords
#print axioms Johnson.AtFull.Made.size_spellBlock
#print axioms Johnson.AtFull.Made.size_spellArray
#print axioms Johnson.AtFull.Made.size_spellLayout
#print axioms Johnson.AtFull.Made.size_spellReqMessage
#print axioms Johnson.AtFull.Made.size_spellReqLink
#print axioms Johnson.AtFull.Made.size_spellNotice
#print axioms Johnson.AtFull.Made.size_spellReq
#print axioms Johnson.AtFull.Made.short_first
