-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingTag.lean: what keeps the strings of different uses of the hash apart: the number in the
label, read off a bit string at a fixed place.

Definitions that compute, theorems. After the format page's rules R2.1, R2.4 (the label stands
after the half and the 64 bytes of the parameter block), in an edition that is not the one that
ships (the same in a second edition, also not the one that ships). (The half: the
string's first byte, 0 or 1: which 32 bytes of the call's answer; `Fmt.oStr`, Fmt/Rules23.lean.)
Shown here: each string that `pNode start` writes has the tag `t166`, for a start of 32 bytes
(`pNode_tag`); each that `p162 D K` writes has `t162`, under `hl` (`p162_tag`). For `t160` and
`t164` this file has no such theorem, only `tag16_hdr` and `tag16_pre33`; Run/CodingPage.lean asks
these two tags of its data (`PageC.firstTag`, `PageC.leafTag`).

Main names:
  `tag16 s`: the 16 bits of s from bit 520 on.
  `p162_tag` asks that the word with the chain's label has the rounds' number in its low 16 bits; at
    a given label this is an evaluation.
  `t160`, `t162`, `t164`, `t166`, and that they differ (`tags_differ`). (160: the number under which
    the format makes the hash that is a chain's first value. 162: the number of a round's query;
    under it alone a digest has 64 bytes, not 32. 164: the number under which the format hashes a
    leaf of a tree of a run. 166: the number under which the format hashes an inner vertex; the
    batch's binding tree has 178.)
  `apart`: two partial codes whose strings have different tags write no common string (what
    `PCode.sum` asks).

Limits: this file says nothing on a hash.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingPage162
import Fmt.Rules23Laws

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

/-- The 16 bits of s from bit 520 on: in a string with a call's header (a start of 32 bytes), the
two low bytes of the label's first word (`tag16_hdr`). -/
def tag16 (s : List Bool) : List Bool := (s.drop 520).take 16

theorem tag16_at (a w r : List Bool) (ha : a.length = 520) :
    tag16 (a ++ (w ++ r)) = (w ++ r).take 16 := by
  unfold tag16
  rw [List.drop_left' ha]

theorem take16 (w r : List Bool) (hw : 16 ≤ w.length) : (w ++ r).take 16 = w.take 16 :=
  List.take_append_of_le_length hw

theorem length_u64n (x : ℕ) : (bytesToBits (_root_.Fmt.u64n x)).length = 64 := by
  rw [length_bytesToBits]
  rfl

/-- The tag of a string with a call's header, for a start of 32 bytes (`hs`). -/
theorem tag16_hdr (half : UInt8) (number tree index : Nat) (start : ByteArray)
    (hs : start.size = 32) (x : List Bool) :
    tag16 (hdr half number tree index start ++ x) =
      (bytesToBits (_root_.Fmt.u64n (number + 65536 * tree))).take 16 := by
  unfold hdr _root_.Fmt.label
  have e : bytesToBits
          (⟨#[half]⟩ ++ _root_.Fmt.pblock number start ++
            (_root_.Fmt.u64n (number + 65536 * tree) ++ _root_.Fmt.u64n index)) ++ x =
      (bytesToBits ⟨#[half]⟩ ++ bytesToBits (_root_.Fmt.pblock number start)) ++
        (bytesToBits (_root_.Fmt.u64n (number + 65536 * tree)) ++
          (bytesToBits (_root_.Fmt.u64n index) ++ x)) := by
    simp only [bytesToBits_append, List.append_assoc]
  rw [e, tag16_at _ _ _ (by rw [List.length_append, length_bytesToBits, length_bytesToBits, _root_.Fmt.size_pblock number start hs]; rfl)]
  exact take16 _ _ (by rw [length_u64n]; omega)

theorem length_pre33 : pre33.length = 264 := by
  unfold pre33
  rw [length_bytesToBits]
  rfl

theorem tag16_pre33 (st w r : List Bool) (hst : st.length = 256) (hw : 16 ≤ w.length) :
    tag16 (pre33 ++ (st ++ (w ++ r))) = w.take 16 := by
  rw [← List.append_assoc, tag16_at _ _ _ (by rw [List.length_append, length_pre33, hst])]
  exact take16 _ _ hw

theorem length_mid32 : mid32.length = 256 := by
  unfold mid32
  rw [length_bytesToBits]
  rfl

theorem tag16_162 (hb : UInt8) (ρ r : List Bool) (hρ : ρ.length = 256) (w : ℕ) :
    tag16 (bitsOfByte hb ++ (mid32 ++ (ρ ++ (bytesToBits (_root_.Fmt.u64n w) ++ r)))) =
      (bytesToBits (_root_.Fmt.u64n w)).take 16 := by
  rw [← List.append_assoc, ← List.append_assoc,
    tag16_at _ _ _
      (by rw [List.length_append, List.length_append, length_bitsOfByte, length_mid32, hρ])]
  exact take16 _ _ (by rw [length_u64n]; omega)

def t160 : List Bool := (bytesToBits (_root_.Fmt.u64n 160)).take 16
def t162 : List Bool := (bytesToBits (_root_.Fmt.u64n 162)).take 16
def t164 : List Bool := (bytesToBits (_root_.Fmt.u64n 164)).take 16
def t166 : List Bool := (bytesToBits (_root_.Fmt.u64n 166)).take 16

theorem tags_differ :
    t160 ≠ t162 ∧ t160 ≠ t164 ∧ t160 ≠ t166 ∧ t162 ≠ t164 ∧ t162 ≠ t166 ∧ t164 ≠ t166 := by
  decide +kernel

/-- Different tags (`hab`, `hp`, `hq`), no common string. -/
theorem apart {A B : Type} (p : PCode A) (q : PCode B) (a b : List Bool) (hab : a ≠ b)
    (hp : ∀ x s, p.put x = some s → tag16 s = a) (hq : ∀ y s, q.put y = some s → tag16 s = b) :
    ∀ x y s, p.put x = some s → q.put y ≠ some s :=
  fun x y s h1 h2 => hab ((hp x s h1).symm.trans (hq y s h2))

/-- The tag of a node's string, for a start of 32 bytes (`hs`). -/
theorem pNode_tag (start : ByteArray) (hs : start.size = 32) (q : List Bool × List Bool)
    (s : List Bool) (h : (pNode start).put q = some s) : tag16 s = t166 := by
  obtain ⟨x, rfl⟩ := pNode_hdr start q s h
  exact tag16_hdr 0 166 0 0 start hs x

/-- The tag of a round's call, if the word with the chain's label has the rounds' number in its low
16 bits (`hl`). -/
theorem p162_tag {I X : Type} {L : BatchProtocol I X} {tg : Tag} (D : ChainD L tg)
    (hl : (bytesToBits (_root_.Fmt.u64n (162 + 65536 * D.label))).take 16 = t162) (K : ℕ)
    (x : FbIn 256 L tg × Fin (K + 1)) (s : List Bool) (h : (p162 D K).put x = some s) :
    tag16 s = t162 := by
  obtain ⟨hb, ρ, r, hρ, rfl⟩ := p162_shape D K x s h
  exact (tag16_162 _ ρ r hρ _).trans hl

end Run
