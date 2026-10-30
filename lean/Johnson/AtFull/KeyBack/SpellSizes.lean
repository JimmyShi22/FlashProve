-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/KeyBack/SpellSizes.lean: THE SIZES OF WHAT OnBytes/Params/Spell.lean SPELLS, AS SUMS:
the items that OnBytes/Params/Fit/StagesFew.lean and Johnson/Goal/Conditions/KeyBytesFitAtScope.lean
have not: words · a binding tree · a notice · "the link" · "request's shape" · "layout". General
laws: at every value; no file, no scope. Theorems with their proofs. NO SUB-PROTOCOL IMPORTS THIS
FILE.
Why. The seven strings of parameter bytes are Fmt.paramsBytes of a list of rounds' entries, the
digest and such items; Fmt.size_paramsBytes (Johnson/Flat/ParamsSize.lean) has their size as a sum
over the items' sizes. With these laws a size is a sum of numbers over a written value, which Lean's
kernel counts without ever laying bytes in a row.
CALLED, NOT TYPED: size_listOf · size_spellRow · size_bool · size_spellShape · size_spellStages
(StagesFew.lean) · spellIndex_size (OnBytes/Params/IndexLaws.lean) · Fmt.size_list · Fmt.size_textS
(ParamsSize.lean).
LIMITS. Sizes alone: nothing on the bytes. No soundness is claimed. On hiding nothing.

-/
import OnBytes.Params.Fit.StagesFew
import Johnson.Flat.ParamsSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

theorem size_spellWords (l : List Nat) : (spellWords l).size = 8 + 8 * l.length :=
  size_listOf spellWord 8 (fun _ => rfl) l

theorem size_spellBinding (s : LinBindingShape) : (spellBinding s).size = 16 := by
  simp [spellBinding, size_spellRow]

theorem size_spellNotice (n : OracleNotice) : (spellNotice n).size = 56 := by
  unfold spellNotice spellWord
  rw [ByteArray.size_append, size_spellShape, Fmt.size_u64n]

/-- The item "the link". -/
theorem size_spellLink (S : LinkShape) : (spellLink S).size = 128 + 32 * S.later.length := by
  unfold spellLink spellChoice spellWord
  simp only [ByteArray.size_append, spellIndex_size, size_spellRow, size_spellStages, size_bool,
    Fmt.size_u64n, List.length_cons, List.length_nil]
  omega

theorem size_spellReqMessage (m : ReqMessage) : (spellReqMessage m).size = 48 := by
  simp [spellReqMessage, size_spellRow]

theorem size_spellReqLink (l : ReqLink) : (spellReqLink l).size = 16 + 48 * l.messages.length := by
  unfold spellReqLink spellWord
  rw [ByteArray.size_append, Fmt.size_u64n, size_listOf spellReqMessage 48 size_spellReqMessage]
  omega

/-- The item "request's shape". -/
theorem size_spellReq (s : ReqShape) : (spellReq s).size =
    56 + (s.link.map fun l => 16 + 48 * l.messages.length).sum + 56 * s.atStart.length +
      32 * (s.last.drop 1).length := by
  unfold spellReq spellChoice spellWord
  simp only [ByteArray.size_append, size_spellRow, Fmt.size_list, size_spellReqLink,
    size_listOf spellNotice 56 size_spellNotice, size_spellStages, size_bool, Fmt.size_u64n,
    List.length_cons, List.length_nil]
  omega

theorem size_spellBlock (b : LaidBlock) : (spellBlock b).size = 72 := by
  unfold spellBlock
  rw [ByteArray.size_append, size_spellRow, size_bool]
  rfl

theorem size_spellArray (a : ReqArray) :
    (spellArray a).size = 40 + (Fmt.ascii a.name).size + 72 * a.blocks.length := by
  unfold spellArray
  rw [ByteArray.size_append, ByteArray.size_append, Fmt.size_textS, size_spellRow,
    size_listOf spellBlock 72 size_spellBlock]
  simp only [List.length_cons, List.length_nil]
  omega

/-- The item "layout". -/
theorem size_spellLayout (l : ReqLayout) : (spellLayout l).size =
    8 + (l.link.map fun as =>
      8 + (as.map fun a => 40 + (Fmt.ascii a.name).size + 72 * a.blocks.length).sum).sum := by
  unfold spellLayout
  simp only [Fmt.size_list, size_spellArray]

end OnBytes.Params

#print axioms OnBytes.Params.size_spellWords
#print axioms OnBytes.Params.size_spellBinding
#print axioms OnBytes.Params.size_spellNotice
#print axioms OnBytes.Params.size_spellLink
#print axioms OnBytes.Params.size_spellReqMessage
#print axioms OnBytes.Params.size_spellReqLink
#print axioms OnBytes.Params.size_spellReq
#print axioms OnBytes.Params.size_spellBlock
#print axioms OnBytes.Params.size_spellArray
#print axioms OnBytes.Params.size_spellLayout
