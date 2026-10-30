-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingPage166.lean: the strings of the programs' format as bit strings: a header and the bytes;
and the partial code of a node query.

Definitions that compute, with their laws.
A call of the format's hash has six fields: half, number, tree, index, start, bytes (`OQ`,
Fmt/Rules23.lean); its string (`oStr`, there) is what the single oracle is asked. A partial code
(`PCode`, Run/CodingPart.lean) writes some points of a type as bit strings, injectively, with a
parser. A node query is the typed query, a pair of bit strings, that hashes two children in a hash
tree.

After the format page's rules R2.1, R2.2, R2.4 (the oracle's strings) and R7.7 (a vertex), in the
form that a vertex has in an edition that is not the one that ships: the vertices' number, tree 0,
index 0, a start that is a constant of the instance (a parameter here).

Main names:
  `hdr half number tree index start`: the bits of the format's string of a call without its bytes:
    81 bytes.
  `pNode start`, a `PCode` on pairs of bit strings: a node query (l, r) is written exactly if both
    have 256 bits: header, l, r; read back by cutting.
  `pNode_put`: if l and r have 256 bits, what it writes is the bits of the format's string of the
    call (vertices' number, 0, 0, start; the bytes of l, the bytes of r).

Limits: this file does not say that the single oracle is any hash. It does not say which start.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingBitsLaws
import Run.CodingPart
import Fmt.Rules23

set_option autoImplicit false

namespace Run
open Rom

/-- The bits of a call's string without its bytes. -/
def hdr (half : UInt8) (number tree index : Nat) (start : ByteArray) : List Bool :=
  bytesToBits (⟨#[half]⟩ ++ _root_.Fmt.pblock number start ++ _root_.Fmt.label number tree index)

/-- The bits of a call's string are its header and then the bits of its bytes. -/
theorem oStr_bits (half : UInt8) (number tree index : Nat) (start bytes : ByteArray) :
    bytesToBits (_root_.Fmt.oStr half number tree index start bytes) =
      hdr half number tree index start ++ bytesToBits bytes :=
  bytesToBits_append _ _

theorem hdr_head (half : UInt8) (number tree index : Nat) (start : ByteArray) :
    ∃ r, hdr half number tree index start = bitsOfByte half ++ r := by
  refine ⟨bytesToBits (_root_.Fmt.pblock number start) ++
      bytesToBits (_root_.Fmt.label number tree index),
    ?_⟩
  unfold hdr
  rw [bytesToBits_append, bytesToBits_append, List.append_assoc]
  rfl

/-- Two bytes with the same bits are the same. -/
theorem bitsOfByte_inj {x y : UInt8} (h : bitsOfByte x = bitsOfByte y) : x = y := by
  rw [← byteOf_bits x, h, byteOf_bits]

/-- A byte other than the half (`he`) is no prefix of a string of the format. -/
theorem hdr_not_prefix (e half : UInt8) (he : e ≠ half) (number tree index : Nat)
    (start : ByteArray) (x : List Bool) :
    ¬ bitsOfByte e <+: hdr half number tree index start ++ x := by
  obtain ⟨r, hr⟩ := hdr_head half number tree index start
  rintro ⟨t, ht⟩
  rw [hr, List.append_assoc] at ht
  exact he (bitsOfByte_inj (List.append_inj_left ht (by rw [length_bitsOfByte, length_bitsOfByte])))

/-- The partial code of a node query. -/
def pNode (start : ByteArray) : PCode (List Bool × List Bool) where
  put := fun q =>
    if q.1.length = 256 ∧ q.2.length = 256 then some (hdr 0 166 0 0 start ++ (q.1 ++ q.2)) else none
  parse := fun s => match strip (hdr 0 166 0 0 start) s with
    | some t => if t.length = 512 then some (t.take 256, t.drop 256) else none
    | none => none
  parse_put := fun q s h => by
    by_cases hq : q.1.length = 256 ∧ q.2.length = 256
    · rw [if_pos hq] at h
      rw [← Option.some.inj h, strip_append]
      show (if (q.1 ++ q.2).length = 512 then some ((q.1 ++ q.2).take 256, (q.1 ++ q.2).drop 256)
          else none) = some q
      rw [if_pos (by rw [List.length_append, hq.1, hq.2]),
        List.take_left' hq.1, List.drop_left' hq.1]
    · rw [if_neg hq] at h
      cases h
  put_parse := fun s q h => by
    cases hs : strip (hdr 0 166 0 0 start) s with
    | none => simp only [hs] at h; cases h
    | some t =>
        simp only [hs] at h
        by_cases ht : t.length = 512
        · rw [if_pos ht] at h
          rw [← Option.some.inj h]
          show (if (t.take 256).length = 256 ∧ (t.drop 256).length = 256 then
                some (hdr 0 166 0 0 start ++ (t.take 256 ++ t.drop 256))
              else none) = some s
          rw [if_pos ⟨by rw [List.length_take, ht]; rfl, by rw [List.length_drop, ht]⟩,
            List.take_append_drop, eq_of_strip _ s t hs]
        · rw [if_neg ht] at h
          cases h

/-- If l and r have 256 bits (`hl`, `hr`), what `pNode` writes is the bits of the format's string.
-/
theorem pNode_put (start : ByteArray) (l r : List Bool)
    (hl : l.length = 256) (hr : r.length = 256) :
    (pNode start).put (l, r) =
      some (bytesToBits (_root_.Fmt.oStr 0 166 0 0 start (bitsToBytes l ++ bitsToBytes r))) := by
  show (if l.length = 256 ∧ r.length = 256 then some (hdr 0 166 0 0 start ++ (l ++ r)) else none) =
    _
  rw [if_pos ⟨hl, hr⟩, oStr_bits, bytesToBits_append,
    bytesToBits_bitsToBytes l ((whole_iff l).2 ⟨32, hl⟩),
    bytesToBits_bitsToBytes r ((whole_iff r).2 ⟨32, hr⟩)]

/-- Every string that `pNode` writes begins with the header. -/
theorem pNode_hdr (start : ByteArray) (q : List Bool × List Bool)
    (s : List Bool) (h : (pNode start).put q = some s) :
    ∃ x, s = hdr 0 166 0 0 start ++ x := by
  by_cases hq : q.1.length = 256 ∧ q.2.length = 256
  · have h' : (if q.1.length = 256 ∧ q.2.length = 256 then
            some (hdr 0 166 0 0 start ++ (q.1 ++ q.2))
          else none) = some s := h
    rw [if_pos hq] at h'
    exact ⟨_, (Option.some.inj h').symm⟩
  · have h' : (if q.1.length = 256 ∧ q.2.length = 256 then
            some (hdr 0 166 0 0 start ++ (q.1 ++ q.2))
          else none) = some s := h
    rw [if_neg hq] at h'
    cases h'

end Run
