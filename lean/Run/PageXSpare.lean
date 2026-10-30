-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageXSpare.lean: three kinds of hash calls are points of the spare oracle, written as
themselves, under the encoding of Run/PageX.lean: a call number 160 under another label than the
chain's; a call number 162 under another label; a call whose number is none of 160, 162, 164, 166,
174. Among the first two: the calls from which the seeds of a stored table's record are drawn.

Run/CodingPageX.lean's `theImplX_other` says it of a string with none of the five tags (160, 162,
164, 166, 174). The seeds of a stored table's record are drawn from a chain of their own
(Fmt/Rules4.lean: `recordLabel`, `recordFirstW`; Fmt/Rules5.lean: `Chain.queryW`): its calls have
the numbers 160 and 162, so that theorem is silent on them. What keeps them apart from the calls of
an entry's chain is the label alone: it stands in the index of a call number 160 and in the tree's
place of a call number 162. Here: a string of such a call under a label other than the data's is
written by none of the partial codes, so the total code does not write it, so (`theImplX_spare`) it
is a point of the spare oracle, written as itself.
Definitions that compute; two properties (`FirstUnderLabel`, `OffFive`); theorems.

Main names:
  `labW0`, `labW1`: the bits 520 to 583 and 584 to 647 of a string: in a call's string the two
    words of its label; `labW0_hdr`, `labW1_hdr`, `tag16_hdrA`: at a call's header, for a start of
    any length (the format fits a start to 32 bytes: `size_fit32`); `labW0_162`: at the shape of a
    round's string.
  `FirstUnderLabel C`: every string of the data's code of the first query begins with the header of
    the call number 160 under the data's own label. A hypothesis on generic data; proved at
    `pageXPd`.
  `pAllX_kinds`: what a string that the format writes looks like, by kinds.
  `totalX_none`: a string that the partial codes do not write and that does not begin with the
    byte 2 is not written by the total code.
  `pAllX_no160`, `pAllX_no162`: no partial code writes the string of a call number 160 with another
    index, of a call number 162 with another number in the tree's place. The bounds are needed: a
    word is written modulo 2^64, so the labels l and l + 2^48 have one word 162 + 65536 l, and the
    indices i and i + 2^64 one word.
  `OffFive n`: the low 16 bits of the word n are none of the five tags; `offFive_eight`: so for the
    eight other numbers of the format's thirteen.
  `only_other`: a string that is a point of the spare oracle, written as itself, is the string of no
    point of another oracle.
  `PQ.labelOK D`: the test "the description's label is below the seeds' label, 2^32".
  `PQ.call160_parse`, `PQ.call162_parse`; `PQ.call160_spare`, `PQ.call162_spare`,
    `PQ.callOff_spare`: at the data `pageXPd dec pd K hcfg V` of a description, for a call as a
    value (`Fmt.OQ`).
  `HO_ask1`, `HO_ask2`, `recordFirstW_HO`, `callW_HO`: which strings the format's texts of the first
    value and of a round's call ask of a function O in the place of the oracle;
    `recordFirstW_oracle`: at the format's oracle the first is the format's own first value.
  `PQ.seedFirst_spare`, `PQ.seedRound_spare`: under `labelOK D`, the strings of the seeds' chain are
    points of the spare oracle, written as themselves; `PQ.seedFirst_only`, `PQ.seedRound_only`: and
    of no other oracle; `PQ.seedFirst_read`, `PQ.seedRound_read`: so the family that the encoding
    reads out of a single oracle g answers there, at its spare oracle, what g answers at the very
    string; `other_oBits`, `PQ.seedFirst_oBits`, `PQ.seedRound_oBits`, `PQ.recordFirst_other`,
    `PQ.recordFirst_H_other`: at `oBits` that is the format's oracle at the call's string, and for
    the first value the format's hash.

Why the test `labelOK` is stated. The format keeps the two kinds of chains apart by the label: a
chain that is started from parameters and a statement has a label below 2^32 (`Fmt.startChainW`
refuses another), the seeds' chain has the label 2^32. That refusal is a reader's. The texts of
`XD.ok`, `PQ.ok` and `Fmt.Spec.ok` name the label nowhere.

Limits: no run function of Run/ asks `labelOK`: it is a hypothesis of theorems here and no more. The
strict and the lenient reader refuse a label from 2^32 on through `Fmt.startChainW`: a reader's
refusal.
The spare oracle has a user in the library already: "The schemes with a seed ask it"
(lean/GLOSSARY.md, "spare oracle"; Compile/Batch/Oracles.lean's head, `other`), and the theorem on
coins derived from a seed has the hypothesis that the scheme's three algorithms never ask that
oracle (Rom/SpecDerive.lean: `ArgAvoids`). This file does not compare the strings treated here with
the points that such a scheme asks.
Not treated: a string of a call number 160 or 162 under the data's own label that the codes do not
write (a round's call with another kind, say); a string of a call number 164, 166 or 174 that no
typed query has (a leaf outside the range of the leaves' codes, say). Where the codes write them,
the calls number 164, 166 and 174 of another chain are typed points of this encoding.
Nothing here says which calls a program makes. `callW_HO` is one call; that `Chain.queryW` asks such
calls alone is its text (`fetchFrom`), no theorem here. For a round's call the step from the
format's oracle to the hash (`Fmt.HO_oracle`, on the hash's domain) is not taken here; outside the
format's image the format's oracle answers under a reserved number.
That the seeds are drawn outside the compiled verifier stays so: this file says only that their
strings are the strings of no point but the spare oracle's. The encoding's data, and so the family,
depend on the decision, and under a record the decision depends on the seeds: the family at whose
spare oracle the seeds' strings lie is fixed only once the seeds are drawn.
`size_fit32`, `size_pblock_any`, `bits_u64n_inj`, `HO_ask1`, `HO_ask2` are facts on Fmt/'s
definitions that stand here because this file alone uses them. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Run.PageX
import Run.CodingAgree
import Run.LaxDomProofs

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

/-! ### The two words of a call's label, as bits of its string -/

/-- The 64 bits of s from bit 520 on: in a call's string the first word of the label: the number,
and the tree's place behind a factor 65536. -/
def labW0 (s : List Bool) : List Bool := (s.drop 520).take 64

/-- The 64 bits of s from bit 584 on: in a call's string the second word of the label: the index. -/
def labW1 (s : List Bool) : List Bool := (s.drop 584).take 64

/-- Behind 520 bits, `labW0` reads the next 64. -/
theorem labW0_at (a w r : List Bool) (ha : a.length = 520) (hw : w.length = 64) :
    labW0 (a ++ (w ++ r)) = w := by
  unfold labW0
  rw [List.drop_left' ha, List.take_left' hw]

/-- Behind 520 bits and 64 more, `labW1` reads the next 64. -/
theorem labW1_at (a w v r : List Bool) (ha : a.length = 520) (hw : w.length = 64)
    (hv : v.length = 64) : labW1 (a ++ (w ++ (v ++ r))) = v := by
  unfold labW1
  rw [← List.append_assoc, List.drop_left' (by rw [List.length_append, ha, hw]),
    List.take_left' hv]

/-- The format fits a start to 32 bytes. -/
theorem size_fit32 (b : ByteArray) : (_root_.Fmt.fit 32 b).size = 32 := by
  unfold _root_.Fmt.fit
  split
  · rw [ByteArray.size_extract]
    omega
  · rw [ByteArray.size_append, _root_.Fmt.size_zeros]
    omega

/-- The parameter block has 64 bytes, whatever the start. -/
theorem size_pblock_any (n : ℕ) (s : ByteArray) : (_root_.Fmt.pblock n s).size = 64 := by
  unfold _root_.Fmt.pblock
  rw [ByteArray.size_append, ByteArray.size_append, _root_.Fmt.size_four, _root_.Fmt.size_zeros,
    size_fit32]

/-- A string with a call's header, cut before and behind the two words of the label. -/
theorem hdr_words (half : UInt8) (number tree index : ℕ) (start : ByteArray) (x : List Bool) :
    hdr half number tree index start ++ x =
      (bytesToBits ⟨#[half]⟩ ++ bytesToBits (_root_.Fmt.pblock number start)) ++
        (bytesToBits (_root_.Fmt.u64n (number + 65536 * tree)) ++
          (bytesToBits (_root_.Fmt.u64n index) ++ x)) := by
  unfold hdr _root_.Fmt.label
  simp only [bytesToBits_append, List.append_assoc]

/-- Before the label stand 520 bits. -/
theorem length_hdr0 (half : UInt8) (number : ℕ) (start : ByteArray) :
    (bytesToBits ⟨#[half]⟩ ++ bytesToBits (_root_.Fmt.pblock number start)).length = 520 := by
  rw [List.length_append, length_bytesToBits, length_bytesToBits, size_pblock_any]
  rfl

/-- In a string with a call's header, `labW0` reads the word with the number and the tree's
place. -/
theorem labW0_hdr (half : UInt8) (number tree index : ℕ) (start : ByteArray) (x : List Bool) :
    labW0 (hdr half number tree index start ++ x) =
      bytesToBits (_root_.Fmt.u64n (number + 65536 * tree)) := by
  rw [hdr_words]
  exact labW0_at _ _ _ (length_hdr0 half number start) (length_u64n _)

/-- In a string with a call's header, `labW1` reads the word with the index. -/
theorem labW1_hdr (half : UInt8) (number tree index : ℕ) (start : ByteArray) (x : List Bool) :
    labW1 (hdr half number tree index start ++ x) = bytesToBits (_root_.Fmt.u64n index) := by
  rw [hdr_words]
  exact labW1_at _ _ _ _ (length_hdr0 half number start) (length_u64n _) (length_u64n _)

/-- `tag16_hdr` (Run/CodingTag.lean) for a start of any length, with the number alone on the
right. -/
theorem tag16_hdrA (half : UInt8) (number tree index : ℕ) (start : ByteArray) (x : List Bool) :
    tag16 (hdr half number tree index start ++ x) =
      (bytesToBits (_root_.Fmt.u64n number)).take 16 := by
  rw [hdr_words, tag16_at _ _ _ (length_hdr0 half number start)]
  exact (take16 _ _ (by rw [length_u64n]; omega)).trans (tag_low number tree)

/-- The first word of the label in a string of the shape of a round's call. -/
theorem labW0_162 (hb : UInt8) (ρ r : List Bool) (hρ : ρ.length = 256) (w : ℕ) :
    labW0 (bitsOfByte hb ++ (mid32 ++ (ρ ++ (bytesToBits (_root_.Fmt.u64n w) ++ r)))) =
      bytesToBits (_root_.Fmt.u64n w) := by
  rw [← List.append_assoc, ← List.append_assoc]
  exact labW0_at _ _ _
    (by rw [List.length_append, List.length_append, length_bitsOfByte, length_mid32, hρ])
    (length_u64n w)

/-- Two numbers below 2^64 with the same word are the same. -/
theorem bits_u64n_inj {x y : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : bytesToBits (_root_.Fmt.u64n x) = bytesToBits (_root_.Fmt.u64n y)) : x = y := by
  have e : _root_.Fmt.u64n x = _root_.Fmt.u64n y := bytesToBits_inj h
  calc x = (_root_.Fmt.wordAt (_root_.Fmt.u64n x) 0).toNat := (_root_.Fmt.wordAt_u64n x hx).symm
    _ = (_root_.Fmt.wordAt (_root_.Fmt.u64n y) 0).toNat := by rw [e]
    _ = y := _root_.Fmt.wordAt_u64n y hy

/-! ### What the partial codes write, by kinds -/

variable {I X : Type} {L : BatchProtocol I X} {K : ℕ} {tg : Tag} (C : PageCX L K tg)

/-- Every string of the data's code of the first query begins with the header of the call number
160 under the data's own label. -/
def FirstUnderLabel : Prop :=
  ∀ q s, C.first.put q = some s → ∃ r, s = hdr160 C.chain.label ++ r

/-- A string that the format writes, by kinds: the header of the call number 160 under the
data's label; or the shape of a round's call, with the data's label in the tree's place; or one of
the tags 164, 166, 174. -/
theorem pAllX_kinds (hF : FirstUnderLabel C) (a : AllPts 256 K L) (s : List Bool)
    (h : (pAllX C).put a = some s) :
    (∃ r, s = hdr160 C.chain.label ++ r) ∨
    (∃ (hb : Bool) (ρ r : List Bool), ρ.length = 256 ∧
      s = bitsOfByte (if hb then 1 else 0) ++
        (mid32 ++ (ρ ++ (bytesToBits (_root_.Fmt.u64n (162 + 65536 * C.chain.label)) ++ r)))) ∨
    tag16 s = t164 ∨ tag16 s = t166 ∨ tag16 s = t174 := by
  cases hy : sel3 (tg := tg) a with
  | none =>
      have h0 : (sel3 a).bind (p3X C).put = some s := h
      rw [hy] at h0
      cases h0
  | some y =>
      have h0 : (sel3 a).bind (p3X C).put = some s := h
      rw [hy] at h0
      rcases y with q | q | q
      · have h1 : (pLeaf2 C).put q = some s := h0
        rcases (pLeaf2_facts C q s h1).1 with e | e
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
      · have h1 : (pNode C.cfg).put q = some s := h0
        exact Or.inr (Or.inr (Or.inr (Or.inl (pNode_facts C.toPageC q s h1).1)))
      · have h1 : (pFb C.toPageC).put q = some s := h0
        obtain ⟨y, -, hy'⟩ := PCode.pull_put _ _ _ _ _ q s h1
        rcases y with y | y
        · have h2 : (pFirstJ C.toPageC).put y = some s := hy'
          exact Or.inl (hF _ s (pFirstJ_put C.toPageC y s h2))
        · have h2 : (p162 C.chain K).put y = some s := hy'
          exact Or.inr (Or.inl (p162_shape C.chain K y s h2))

/-- A string that the partial codes do not write (`hA`) and that does not begin with the byte 2
(`h2`) is not written by the total code. -/
theorem totalX_none (s : List Bool) (h2 : ¬ bitsOfByte 2 <+: s)
    (hA : ∀ a, (pAllX C).put a ≠ some s) : (totalX C).parse s = none := by
  cases hp : (totalX C).parse s with
  | none => rfl
  | some a =>
      exfalso
      have hs := (totalX C).put_parse s a hp
      cases ha : (pAllX C).put a with
      | some u =>
          have e : u = s :=
            (PCode.orElse_put_some (pAllX C) C.back (bitsOfByte 2) (pAllX_no2 C) ha).symm.trans hs
          rw [e] at ha
          exact hA a ha
      | none =>
        exact h2 ⟨_, (PCode.orElse_put_none (pAllX C) C.back (bitsOfByte 2)
          (pAllX_no2 C) ha).symm.trans hs⟩

/-- No partial code writes the string of a call number 160 whose index is not the data's label,
both below 2^64. Any half, any number in the tree's place, any start, any bytes. -/
theorem pAllX_no160 (hF : FirstUnderLabel C) (half : UInt8) (tree i : ℕ) (start : ByteArray)
    (x : List Bool)
    (hi : i < 2 ^ 64) (hl : C.chain.label < 2 ^ 64) (hne : i ≠ C.chain.label)
    (a : AllPts 256 K L) : (pAllX C).put a ≠ some (hdr half 160 tree i start ++ x) := by
  intro h
  have ht : tag16 (hdr half 160 tree i start ++ x) = t160 := tag16_hdrA half 160 tree i start x
  rcases pAllX_kinds C hF a _ h with ⟨r, e⟩ | ⟨hb, ρ, r, hρ, e⟩ | e | e | e
  · have e0 := congrArg labW1 e
    unfold hdr160 at e0
    rw [labW1_hdr, labW1_hdr] at e0
    exact hne (bits_u64n_inj hi hl e0)
  · have e1 : tag16 (hdr half 160 tree i start ++ x) = t162 := by
      rw [e]
      exact (tag16_162 _ ρ r hρ _).trans C.chainTag
    exact tags_differ.1 (ht.symm.trans e1)
  · exact tags_differ.2.1 (ht.symm.trans e)
  · exact tags_differ.2.2.1 (ht.symm.trans e)
  · exact t174_differs.1 (e.symm.trans ht)

/-- No partial code writes the string of a call number 162 whose number in the tree's place is
not the data's label, both below 2^48. Any half, any index, any start, any bytes. -/
theorem pAllX_no162 (hF : FirstUnderLabel C) (half : UInt8) (l i : ℕ) (start : ByteArray)
    (x : List Bool)
    (hl' : l < 2 ^ 48) (hl : C.chain.label < 2 ^ 48) (hne : l ≠ C.chain.label)
    (a : AllPts 256 K L) : (pAllX C).put a ≠ some (hdr half 162 l i start ++ x) := by
  intro h
  have ht : tag16 (hdr half 162 l i start ++ x) = t162 := tag16_hdrA half 162 l i start x
  rcases pAllX_kinds C hF a _ h with ⟨r, e⟩ | ⟨hb, ρ, r, hρ, e⟩ | e | e | e
  · have e1 : tag16 (hdr half 162 l i start ++ x) = t160 := by
      rw [e]
      exact tag16_hdrA 0 160 0 C.chain.label _root_.Fmt.zero32 r
    exact tags_differ.1 (e1.symm.trans ht)
  · have e0 := congrArg labW0 e
    rw [labW0_hdr, labW0_162 _ ρ r hρ] at e0
    have e2 : 162 + 65536 * l = 162 + 65536 * C.chain.label :=
      bits_u64n_inj (by omega) (by omega) e0
    exact hne (by omega)
  · exact tags_differ.2.2.2.1 (ht.symm.trans e)
  · exact tags_differ.2.2.2.2.1 (ht.symm.trans e)
  · exact t174_differs.2.1 (e.symm.trans ht)

/-! ### Numbers outside the five -/

/-- The low 16 bits of the word n are none of the five tags. -/
def OffFive (n : ℕ) : Prop :=
  (bytesToBits (_root_.Fmt.u64n n)).take 16 ≠ t160 ∧
  (bytesToBits (_root_.Fmt.u64n n)).take 16 ≠ t162 ∧
  (bytesToBits (_root_.Fmt.u64n n)).take 16 ≠ t164 ∧
  (bytesToBits (_root_.Fmt.u64n n)).take 16 ≠ t166 ∧
  (bytesToBits (_root_.Fmt.u64n n)).take 16 ≠ t174

instance (n : ℕ) : Decidable (OffFive n) := by
  unfold OffFive
  infer_instance

/-- The eight numbers of the format's thirteen (`Fmt.numbers`) that are not among the five have
it. -/
theorem offFive_eight : ∀ n ∈ [168, 169, 171, 172, 173, 176, 178, 179], OffFive n := by
  decide +kernel

/-- These eight and the five are the format's thirteen numbers. -/
theorem numbers_off :
    _root_.Fmt.numbers.filter (fun n => !([160, 162, 164, 166, 174].contains n)) =
      [168, 169, 171, 172, 173, 176, 178, 179] := by
  decide

/-- The number 169 (the digests of parameters and of the public files) is off the five. -/
theorem offFive_169 : OffFive 169 := offFive_eight 169 (by decide)

/-- The number 172 (a run's value) is off the five. -/
theorem offFive_172 : OffFive 172 := offFive_eight 172 (by decide)

/-- The number 179 (the commitment ID) is off the five. -/
theorem offFive_179 : OffFive 179 := offFive_eight 179 (by decide)

/-- The string of a call with such a number has none of the five tags. -/
theorem offFive_tag (n : ℕ) (hn : OffFive n) (half : UInt8) (tree i : ℕ) (start : ByteArray)
    (x : List Bool) : ¬ Tag5 (hdr half n tree i start ++ x) := by
  unfold Tag5
  rw [tag16_hdrA]
  obtain ⟨d0, d2, d4, d6, d7⟩ := hn
  rintro (h | h | h | h | h)
  · exact d0 h
  · exact d2 h
  · exact d4 h
  · exact d6 h
  · exact d7 h

/-! ### A call as a value; what the spare oracle answers -/

/-- The bits of a call's string: its header, then the bits of its bytes. -/
theorem bits_strOf (c : _root_.Fmt.OQ) :
    bytesToBits (strOf c) = hdr c.half c.number c.tree c.index c.start ++ bytesToBits c.bytes :=
  oStr_bits c.half c.number c.tree c.index c.start c.bytes

/-- The family that the encoding reads out of a single oracle g answers, at its spare oracle, what g
answers at the point's string. -/
theorem readBlocks_other (g : Fam (rom 256)) (s : List Bool) :
    readBlocks (theImplX C) g .other s = g () ((theImplX C).code .other s (0 : Fin 1)) := rfl

/-- At the single oracle made from the format's (`oBits`, Run/OracleBits.lean): where a call's
string is a point of the spare oracle, written as itself (`hs`), the family's spare oracle answers
there what the format's oracle answers at the call's string (a first byte other than 4: `h4`). -/
theorem other_oBits (c : _root_.Fmt.OQ) (h4 : c.half ≠ 4)
    (hs : (theImplX C).code .other (bytesToBits (strOf c)) (0 : Fin 1) = bytesToBits (strOf c)) :
    readBlocks (theImplX C) oBits .other (bytesToBits (strOf c)) =
      bytesToDig (_root_.Fmt.oracle (strOf c)) := by
  rw [readBlocks_other, hs]
  exact oBits_call c (by
    rw [bits_strOf]
    exact hdr_not_prefix 4 c.half (Ne.symm h4) _ _ _ _ _)

/-- A string that is a point of the spare oracle, written as itself (`hs`), is the string of no
point of another oracle: the encoding is one-to-one (`OracleCoding.inj`, Rom/Family.lean). -/
theorem only_other (s : List Bool) (hs : (theImplX C).code .other s (0 : Fin 1) = s)
    (o : Batch.OracleName) (q : Batch.domOf 256 L o) (j : Fin (blk K o))
    (h : (theImplX C).code o q j = s) : o = .other :=
  congrArg Sigma.fst
    ((theImplX C).inj (a₁ := ⟨o, (q, j)⟩) (a₂ := ⟨Batch.OracleName.other, (s, (0 : Fin 1))⟩)
      (h.trans hs.symm))

/-! ### Which strings the format's texts ask of a function in the place of the oracle -/

/-- A hash with a number other than 162 is one question, at the half 0. -/
theorem HO_ask1 (O : ByteArray → ByteArray) (n t i : ℕ) (s b : ByteArray) (h : n ≠ 162) :
    _root_.Fmt.HO O n t i s b = O (strOf ⟨0, n, t, i, s, b⟩) := by
  unfold _root_.Fmt.HO
  exact if_neg h

/-- A hash with the number 162 is two questions, the half 0 first. -/
theorem HO_ask2 (O : ByteArray → ByteArray) (t i : ℕ) (s b : ByteArray) :
    _root_.Fmt.HO O 162 t i s b =
      O (strOf ⟨0, 162, t, i, s, b⟩) ++ O (strOf ⟨1, 162, t, i, s, b⟩) := by
  unfold _root_.Fmt.HO
  exact if_pos rfl

/-- The call for the first value of the chain of a stored table's record. -/
def seedFirstCall (name : ByteArray) : _root_.Fmt.OQ :=
  ⟨0, 160, 0, _root_.Fmt.recordLabel, _root_.Fmt.zero32,
    _root_.Fmt.firstBytes _root_.Fmt.zero32 name ByteArray.empty none⟩

/-- A half of a call of a round of that chain: round i, from the chain's value ρ, with any bytes. -/
def seedRoundCall (half : UInt8) (ρ : ByteArray) (i : ℕ) (b : ByteArray) : _root_.Fmt.OQ :=
  ⟨half, 162, _root_.Fmt.recordLabel, i, ρ, b⟩

/-- The format's text of that first value, at the hash over O, asks O at that call's string. -/
theorem recordFirstW_HO (O : ByteArray → ByteArray) (name : ByteArray) :
    (_root_.Fmt.recordFirstW (m := Id) (_root_.Fmt.HO O) name : ByteArray) =
      O (strOf (seedFirstCall name)) :=
  HO_ask1 O 160 0 _root_.Fmt.recordLabel _root_.Fmt.zero32 _ (by decide)

/-- What is hashed for that first value has 56 bytes more than the name. -/
theorem size_seedFirstBytes (name : ByteArray) :
    (_root_.Fmt.firstBytes _root_.Fmt.zero32 name ByteArray.empty none).size = name.size + 56 := by
  unfold _root_.Fmt.firstBytes
  simp only [ByteArray.size_append, _root_.Fmt.size_u64n]
  show 32 + 8 + name.size + 8 + 0 + 8 = name.size + 56
  omega

/-- At the format's oracle that text gives the format's own first value (`Fmt.recordFirst`: at
the hash `Fmt.formatHash`), for a name within the hash's bound on bytes (`Fmt.HO_oracle`,
Fmt/Rules23Laws.lean). -/
theorem recordFirstW_oracle (name : ByteArray) (hn : name.size + 56 ≤ 2 ^ 32 - 144) :
    (_root_.Fmt.recordFirstW (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) name : ByteArray) =
      _root_.Fmt.recordFirst name :=
  _root_.Fmt.HO_oracle 160 0 _root_.Fmt.recordLabel _root_.Fmt.zero32 _
    (dom0 160 _root_.Fmt.recordLabel _ (by decide) (by decide) (by decide)
      (by rw [size_seedFirstBytes]; exact hn))

/-- The format's text of call j of a round, under the seeds' label, at the hash over O, asks O at
the two halves' strings. -/
theorem callW_HO (O : ByteArray → ByteArray) (ρ : ByteArray) (i : ℕ) (msg : ByteArray)
    (kind : _root_.Fmt.Kind) (w nonce j : ℕ) :
    (_root_.Fmt.callW (m := Id) (_root_.Fmt.HO O) _root_.Fmt.recordLabel ρ i msg kind w nonce j :
        ByteArray) =
      O (strOf (seedRoundCall 0 ρ i (msg ++ _root_.Fmt.tail kind w nonce j))) ++
        O (strOf (seedRoundCall 1 ρ i (msg ++ _root_.Fmt.tail kind w nonce j))) :=
  HO_ask2 O _root_.Fmt.recordLabel i ρ _

end Run

namespace Run.PQ
open Rom Compile Compile.Batch Iop

variable {D : XD} (dec : View → Bool) (pd : Dig 256) (K : ℕ) (hcfg : D.base.cfg.size = 32)
  (V : StmInv D)

/-- At the data made from a description, the first query's strings begin with the header of the
call number 160 under the description's label. -/
theorem firstUnderLabel_pageXPd : FirstUnderLabel (pageXPd dec pd K hcfg V) :=
  fun q s h => firstPX_hdr dec pd V q s h

/-- (1) The string of a call number 160 whose index is not the description's label (both below
2^64; a first byte other than 2) is not written by the total code. -/
theorem call160_parse (c : _root_.Fmt.OQ) (hn : c.number = 160) (h2 : c.half ≠ 2)
    (hi : c.index < 2 ^ 64) (hl : D.base.label < 2 ^ 64) (hne : c.index ≠ D.base.label) :
    (totalX (pageXPd dec pd K hcfg V)).parse (bytesToBits (strOf c)) = none := by
  rw [bits_strOf, hn]
  exact totalX_none _ _ (hdr_not_prefix 2 c.half (Ne.symm h2) _ _ _ _ _)
    (pAllX_no160 _ (firstUnderLabel_pageXPd dec pd K hcfg V) c.half c.tree c.index c.start _ hi hl
      hne)

/-- So it is a point of the spare oracle, written as itself (a first byte other than 2 and 3). -/
theorem call160_spare (c : _root_.Fmt.OQ) (hn : c.number = 160) (h2 : c.half ≠ 2)
    (h3 : c.half ≠ 3) (hi : c.index < 2 ^ 64) (hl : D.base.label < 2 ^ 64)
    (hne : c.index ≠ D.base.label) (j : Fin 1) :
    (theImplX (pageXPd dec pd K hcfg V)).code .other (bytesToBits (strOf c)) j =
      bytesToBits (strOf c) :=
  theImplX_spare _ _ j (call160_parse dec pd K hcfg V c hn h2 hi hl hne) (by
    rw [bits_strOf]
    exact hdr_not_prefix 3 c.half (Ne.symm h3) _ _ _ _ _)

/-- (2) The string of a call number 162 whose number in the tree's place is not the description's
label (both below 2^48: from 2^48 on two labels can have one word; a first byte other than 2) is
not written by the total code. -/
theorem call162_parse (c : _root_.Fmt.OQ) (hn : c.number = 162) (h2 : c.half ≠ 2)
    (ht : c.tree < 2 ^ 48) (hl : D.base.label < 2 ^ 48) (hne : c.tree ≠ D.base.label) :
    (totalX (pageXPd dec pd K hcfg V)).parse (bytesToBits (strOf c)) = none := by
  rw [bits_strOf, hn]
  exact totalX_none _ _ (hdr_not_prefix 2 c.half (Ne.symm h2) _ _ _ _ _)
    (pAllX_no162 _ (firstUnderLabel_pageXPd dec pd K hcfg V) c.half c.tree c.index c.start _ ht hl
      hne)

/-- So it is a point of the spare oracle, written as itself (a first byte other than 2 and 3). -/
theorem call162_spare (c : _root_.Fmt.OQ) (hn : c.number = 162) (h2 : c.half ≠ 2)
    (h3 : c.half ≠ 3) (ht : c.tree < 2 ^ 48) (hl : D.base.label < 2 ^ 48)
    (hne : c.tree ≠ D.base.label) (j : Fin 1) :
    (theImplX (pageXPd dec pd K hcfg V)).code .other (bytesToBits (strOf c)) j =
      bytesToBits (strOf c) :=
  theImplX_spare _ _ j (call162_parse dec pd K hcfg V c hn h2 ht hl hne) (by
    rw [bits_strOf]
    exact hdr_not_prefix 3 c.half (Ne.symm h3) _ _ _ _ _)

/-- (3) The string of a call whose number is outside the five (`offFive_eight`: among them
169, 172, 179), with a first byte other than 2 and 3, is a point of the spare oracle, written as
itself, whatever its label. -/
theorem callOff_spare (c : _root_.Fmt.OQ) (hn : OffFive c.number) (h2 : c.half ≠ 2)
    (h3 : c.half ≠ 3) (j : Fin 1) :
    (theImplX (pageXPd dec pd K hcfg V)).code .other (bytesToBits (strOf c)) j =
      bytesToBits (strOf c) := by
  rw [bits_strOf]
  exact theImplX_other _ _ j (offFive_tag c.number hn c.half c.tree c.index c.start _)
    (hdr_not_prefix 2 c.half (Ne.symm h2) _ _ _ _ _)
    (hdr_not_prefix 3 c.half (Ne.symm h3) _ _ _ _ _)

/-! ### The seeds' chain -/

/-- The test: the description's label is below 2^32, as the format asks of a chain that is started
from parameters and a statement (`Fmt.startChainW`). The seeds' chain alone has the label 2^32. -/
def labelOK (D : XD) : Bool := decide (D.base.label < _root_.Fmt.recordLabel)

/-- What the test says, with the seeds' label written out. -/
theorem labelOK_lt (h : labelOK D = true) : D.base.label < 2 ^ 32 := of_decide_eq_true h

/-- Under the test, the string of the call for the first value of the seeds' chain is a point of
the spare oracle, written as itself, for every name. -/
theorem seedFirst_spare (h : labelOK D = true) (name : ByteArray) (j : Fin 1) :
    (theImplX (pageXPd dec pd K hcfg V)).code .other (bytesToBits (strOf (seedFirstCall name))) j =
      bytesToBits (strOf (seedFirstCall name)) := by
  have hl := labelOK_lt h
  have hr : _root_.Fmt.recordLabel = 2 ^ 32 := rfl
  exact call160_spare dec pd K hcfg V (seedFirstCall name) rfl
    (show (0 : UInt8) ≠ 2 by decide) (show (0 : UInt8) ≠ 3 by decide)
    (show _root_.Fmt.recordLabel < 2 ^ 64 by rw [hr]; omega) (by omega)
    (show _root_.Fmt.recordLabel ≠ D.base.label by rw [hr]; omega) j

/-- Under the test, so is the string of either half of a call of a round of the seeds' chain,
for every chain value, round and bytes. -/
theorem seedRound_spare (h : labelOK D = true) (half : UInt8) (hh : half = 0 ∨ half = 1)
    (ρ : ByteArray) (i : ℕ) (b : ByteArray) (j : Fin 1) :
    (theImplX (pageXPd dec pd K hcfg V)).code .other
        (bytesToBits (strOf (seedRoundCall half ρ i b))) j =
      bytesToBits (strOf (seedRoundCall half ρ i b)) := by
  have hl := labelOK_lt h
  have hr : _root_.Fmt.recordLabel = 2 ^ 32 := rfl
  have n2 : half ≠ 2 := by rcases hh with rfl | rfl <;> decide
  have n3 : half ≠ 3 := by rcases hh with rfl | rfl <;> decide
  exact call162_spare dec pd K hcfg V (seedRoundCall half ρ i b) rfl n2 n3
    (show _root_.Fmt.recordLabel < 2 ^ 48 by rw [hr]; omega) (by omega)
    (show _root_.Fmt.recordLabel ≠ D.base.label by rw [hr]; omega) j

/-- So the family that the encoding reads out of a single oracle g answers there, at its spare
oracle, what g answers at the very string. -/
theorem seedFirst_read (h : labelOK D = true) (g : Fam (rom 256)) (name : ByteArray) :
    readBlocks (theImplX (pageXPd dec pd K hcfg V)) g .other
        (bytesToBits (strOf (seedFirstCall name))) =
      g () (bytesToBits (strOf (seedFirstCall name))) := by
  rw [readBlocks_other, seedFirst_spare dec pd K hcfg V h name 0]

/-- The same at either half of a call of a round of the seeds' chain. -/
theorem seedRound_read (h : labelOK D = true) (g : Fam (rom 256)) (half : UInt8)
    (hh : half = 0 ∨ half = 1) (ρ : ByteArray) (i : ℕ) (b : ByteArray) :
    readBlocks (theImplX (pageXPd dec pd K hcfg V)) g .other
        (bytesToBits (strOf (seedRoundCall half ρ i b))) =
      g () (bytesToBits (strOf (seedRoundCall half ρ i b))) := by
  rw [readBlocks_other, seedRound_spare dec pd K hcfg V h half hh ρ i b 0]

/-- At `oBits`: what the format's oracle answers at the call's string. -/
theorem seedFirst_oBits (h : labelOK D = true) (name : ByteArray) :
    readBlocks (theImplX (pageXPd dec pd K hcfg V)) oBits .other
        (bytesToBits (strOf (seedFirstCall name))) =
      bytesToDig (_root_.Fmt.oracle (strOf (seedFirstCall name))) :=
  other_oBits _ (seedFirstCall name) (show (0 : UInt8) ≠ 4 by decide)
    (seedFirst_spare dec pd K hcfg V h name 0)

/-- The same at either half of a call of a round of the seeds' chain. -/
theorem seedRound_oBits (h : labelOK D = true) (half : UInt8) (hh : half = 0 ∨ half = 1)
    (ρ : ByteArray) (i : ℕ) (b : ByteArray) :
    readBlocks (theImplX (pageXPd dec pd K hcfg V)) oBits .other
        (bytesToBits (strOf (seedRoundCall half ρ i b))) =
      bytesToDig (_root_.Fmt.oracle (strOf (seedRoundCall half ρ i b))) :=
  other_oBits _ (seedRoundCall half ρ i b)
    (show half ≠ 4 by rcases hh with rfl | rfl <;> decide)
    (seedRound_spare dec pd K hcfg V h half hh ρ i b 0)

/-- The first value of the seeds' chain, by the format's text at the hash over the format's
oracle, is, as a digest, what the family read out of `oBits` answers at its spare oracle at that
call's string. -/
theorem recordFirst_other (h : labelOK D = true) (name : ByteArray) :
    bytesToDig (_root_.Fmt.recordFirstW (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) name) =
      readBlocks (theImplX (pageXPd dec pd K hcfg V)) oBits .other
        (bytesToBits (strOf (seedFirstCall name))) := by
  rw [seedFirst_oBits dec pd K hcfg V h name, recordFirstW_HO]

/-- So is the format's own first value of the seeds' chain (`Fmt.recordFirst`: at the hash), for
a name within the hash's bound on bytes. -/
theorem recordFirst_H_other (h : labelOK D = true) (name : ByteArray)
    (hn : name.size + 56 ≤ 2 ^ 32 - 144) :
    bytesToDig (_root_.Fmt.recordFirst name) =
      readBlocks (theImplX (pageXPd dec pd K hcfg V)) oBits .other
        (bytesToBits (strOf (seedFirstCall name))) := by
  rw [← recordFirstW_oracle name hn]
  exact recordFirst_other dec pd K hcfg V h name

/-- Under the test, no point of another oracle has the string of the call for the first value of
the seeds' chain. -/
theorem seedFirst_only (h : labelOK D = true) (name : ByteArray) (o : Batch.OracleName)
    (q : Batch.domOf 256 (D.L dec) o) (j : Fin (blk K o))
    (e : (theImplX (pageXPd dec pd K hcfg V)).code o q j =
      bytesToBits (strOf (seedFirstCall name))) : o = .other :=
  only_other _ _ (seedFirst_spare dec pd K hcfg V h name 0) o q j e

/-- Nor that of either half of a call of a round of the seeds' chain. -/
theorem seedRound_only (h : labelOK D = true) (half : UInt8) (hh : half = 0 ∨ half = 1)
    (ρ : ByteArray) (i : ℕ) (b : ByteArray) (o : Batch.OracleName) (q : Batch.domOf 256 (D.L dec) o)
    (j : Fin (blk K o))
    (e : (theImplX (pageXPd dec pd K hcfg V)).code o q j =
      bytesToBits (strOf (seedRoundCall half ρ i b))) : o = .other :=
  only_other _ _ (seedRound_spare dec pd K hcfg V h half hh ρ i b 0) o q j e

end Run.PQ
