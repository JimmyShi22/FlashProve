-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/KeyInj.lean: the function `cutKey` (OnBytes/K/Arm/KeyCut.lean), which writes the typed
queries of a key file's part of the compiled verifier as strings, is one to one where it writes:
from three laws on the key file's three chains, laws on two spellings that are taken as they are, a
digest of 32 bytes, and three inequalities: none of the file's three labels is the seeds'. Under
these hypotheses, and from a total code `back`, OnBytes/TypedOracleCompiler/Run/PageOf.lean makes an encoding in the
sense of the soundness theorem that writes these strings.

`cutKey_inj` and `rowKey_inj` of that file reduce the matter to: each kind of row is one to one;
chain queries and queries for the slot value share no call; the three spellings together are one to
one; no string of a spelling is the string of a row's call. Here the request tree's two kinds are
shown to be one to one. Strings of different kinds are told apart by the two words of the label that
every string of the format holds at a fixed place (`lw1`, `lw2`, OnBytes/TypedOracleCompiler/Run/Apart.lean;
`tag16`, Run/CodingTag.lean): the low 16 bits of the first word are the format's number; the label
of a chain stands in the second word of a first call and in the first word of a row's call. Of the
two spellings that the page holds, beside that each is one to one, only that much is asked: of a
leaf's string what every code of leaves has as a field (`PageG.Leaves.hlf`), of a seed's string what
the seeds' code is shown to have (`fbSeeds_is`, OnBytes/TypedOracleCompiler/Run/SeedPoints.lean). They are not asked
to lie in the domain of the format's hash. For proofs only; the program does not import this file.

Main definitions.
 `TakenCalls`     what is asked of the page's spelling of leaves and of the seeds' spelling: each is
                  one to one; a leaf's string has the tag of one of the two numbers of leaves and
                  begins with no byte other than 0; a seed's string has the form of a first call or
                  of a row's call under the seeds' label.
 `KeyLaws`        all that is asked, as one record.
 `mKey`           the encoding (`Rom.OracleCoding`) that OnBytes/TypedOracleCompiler/Run/PageOf.lean makes of `cutKey` under
                  `KeyLaws`, at a total code `back`.
Main theorems.
 `rnode_inj`      a request vertex's call is one to one on children of a digest's bits.
 `rleaf_inj`      a request leaf's call is one to one.
 `fb_place`       with `g_place`: a chain query's call is a first call with one of the file's three
                  labels as its index, or a row's with one of them as its tree; the call for the
                  slot value is a row's with the first label.
 `bitsOf_words`   the two words of the label in the string of a call in the domain.
 `no_inj`         the seven numbers of the format that occur here are known from their tags.
 `taken_inj`      the three spellings together are one to one.
 `taken_rows`     no string of a spelling is the string of a row's call, if none of the file's three
                  labels is the seeds'.
 `cutKey_one`     `cutKey` is one to one where it writes.
 `cutKey_hd`      with `bitsOf_hd`: its strings begin with no byte other than 0 and 1.

What is not claimed. That the three laws on the key file's chains (`hfb`, `hg`, `hfg`; the fields
`fb`, `g`, `fbg` of `KeyLaws`) hold at any data: OnBytes/K/Arm/FileInj.lean shows them for its own
two tests, under its laws `LawsJ`, and OnBytes/K/Arm/KeyGlue.lean draws `KeyLaws` from that
(`keyLaws_of`). That `TakenCalls` holds at any page. That the verifier's queries pass the tests of
fitness, or that their calls lie in the domain. That the cut is not hollow: where both tests of
fitness say no everywhere and the page's two spellings write nothing, nothing is left of the laws
but the digest's length and the three inequalities, and the encoding writes the vertices and the
request tree alone; every other query goes to `back`, behind the escape. So the laws are worth what
the tests let through. That a total code `back` exists at any interface. `mKey` has no program: its
parser is taken by choice. Nothing on the entry file's or the proof file's queries. Nothing on any
hash function; nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.KeyCut
import OnBytes.K.Arm.StrInj
import Run.CodingSeq
import OnBytes.TypedOracleCompiler.Run.PageOf

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open TypedOracleCompiler.Run.Apart
open OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- The format's number of a leaf of a tree over oracles. -/
def nLeaf : ℕ := 164
/-- Of a leaf of a stored table's tree. -/
def nStored : ℕ := 174
/-- The bytes of a digest. -/
def digBytes : ℕ := 32
/-- The bits of a word. -/
def wordBits : ℕ := 64

/-- A digest's bits are its bytes' bits. -/
theorem digBits_eq : digBits = 8 * digBytes := rfl

/-! ## The request tree -/

/-- **A request vertex's call is one to one** on children of a digest's bits. -/
theorem rnode_inj (cfg : ByteArray) (q q' : Bits × Bits) (c : Fmt.OQ) (f : fitTree q = true)
    (f' : fitTree q' = true) (h : rnodeCall cfg q = some c) (h' : rnodeCall cfg q' = some c) :
    q = q' := by
  unfold fitTree at f f'
  simp only [Bool.and_eq_true, beq_iff_eq] at f f'
  have e : bitsToBytes q.1 ++ bitsToBytes q.2 = bitsToBytes q'.1 ++ bitsToBytes q'.2 :=
    congrArg Fmt.OQ.bytes (Option.some.inj (h.trans h'.symm))
  have s1 := size_bitsToBytes q.1 digBytes (f.1.trans digBits_eq)
  have s1' := size_bitsToBytes q'.1 digBytes (f'.1.trans digBits_eq)
  obtain ⟨e1, e2⟩ := Fmt.append_cancel _ _ _ _ (s1.trans s1'.symm) e
  exact Prod.ext
    (bitsToBytes_inj (whole_of_len (f.1.trans digBits_eq)) (whole_of_len (f'.1.trans digBits_eq))
      e1)
    (bitsToBytes_inj (whole_of_len (f.2.trans digBits_eq)) (whole_of_len (f'.2.trans digBits_eq))
      e2)

/-- A string of a word's bits is known from the number that it spells. -/
theorem word_bits_inj (d d' : Bits) (h : d.length = wordBits) (h' : d'.length = wordBits)
    (e : (Fmt.wordAt (bitsToBytes d) 0).toNat = (Fmt.wordAt (bitsToBytes d') 0).toNat) :
    d = d' := by
  have p : pWord.parse d = some (Fmt.wordAt (bitsToBytes d) 0).toNat := if_pos h
  have p' : pWord.parse d' = some (Fmt.wordAt (bitsToBytes d') 0).toNat := if_pos h'
  rw [← e] at p'
  exact Option.some.inj ((pWord.put_parse _ _ p).symm.trans (pWord.put_parse _ _ p'))

/-- **A request leaf's call is one to one.** Its own test fixes the length of the typed string. -/
theorem rleaf_inj (cfg : ByteArray) (sR : ℕ) (q q' : Bits) (c : Fmt.OQ)
    (h : rleafCall cfg sR q = some c) (h' : rleafCall cfg sR q' = some c) : q = q' := by
  unfold rleafCall at h h'
  split at h
  · rename_i l
    split at h'
    · rename_i l'
      have e := (Option.some.inj h).trans (Option.some.inj h').symm
      have ei := congrArg Fmt.OQ.index e
      have eb := congrArg Fmt.OQ.bytes e
      simp only at ei eb
      have t1 : (q.take (256 + 8 * sR)).length = 8 * (digBytes + sR) := by
        rw [List.length_take, l]
        unfold digBytes
        omega
      have t1' : (q'.take (256 + 8 * sR)).length = 8 * (digBytes + sR) := by
        rw [List.length_take, l']
        unfold digBytes
        omega
      have d1 : (q.drop (256 + 8 * sR)).length = wordBits := by
        rw [List.length_drop, l]
        unfold wordBits
        omega
      have d1' : (q'.drop (256 + 8 * sR)).length = wordBits := by
        rw [List.length_drop, l']
        unfold wordBits
        omega
      rw [← List.take_append_drop (256 + 8 * sR) q, ← List.take_append_drop (256 + 8 * sR) q',
        bitsToBytes_inj (whole_of_len t1) (whole_of_len t1') eb, word_bits_inj _ _ d1 d1' ei]
    · cases h'
  · cases h

/-! ## Where a row's call holds its label -/

/-- A chain query's call: a first call with one of the three labels as its index, or a row's with
one of them as its tree. -/
theorem fb_place {t : Tag} (F : FileJ L t) (q : FbIn 256 L t) (j : Fin (K + 1)) (c : Fmt.OQ)
    (h : fbCallJ F K q j = some c) :
    (c.number = nFirst ∧ (c.index = F.lab₁ ∨ c.index = F.lab₂ ∨ c.index = F.lab₃)) ∨
      (c.number = nRow ∧ (c.tree = F.lab₁ ∨ c.tree = F.lab₂ ∨ c.tree = F.lab₃)) := by
  unfold fbCallJ at h
  split at h <;> (repeat' split at h) <;>
    first
      | (obtain rfl := Option.some.inj h
         first
           | exact Or.inl ⟨rfl, Or.inl rfl⟩
           | exact Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩
           | exact Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩
           | exact Or.inr ⟨rfl, Or.inl rfl⟩
           | exact Or.inr ⟨rfl, Or.inr (Or.inl rfl)⟩
           | exact Or.inr ⟨rfl, Or.inr (Or.inr rfl)⟩)
      | cases h

/-- The call for the slot value: a row's, with the first label as its tree. -/
theorem g_place {t : Tag} (F : FileJ L t) (q : JoiningRoundQuery 256 L t) (c : Fmt.OQ)
    (h : gCallJ F q = some c) : c.number = nRow ∧ c.tree = F.lab₁ := by
  unfold gCallJ at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
  · cases h

/-! ## The label's two words in a string -/

/-- **The two words of the label in the string of a call in the domain**, with the bounds that the
domain gives. -/
theorem bitsOf_words (c : Fmt.OQ) (s : List Bool) (h : bitsOf c = some s) :
    lw1 s = Wd (c.number + 65536 * c.tree) ∧ lw2 s = Wd c.index ∧ c.tree < 2 ^ 48 ∧
      c.index < 2 ^ 63 := by
  unfold bitsOf at h
  by_cases d : inDom c = true
  · rw [if_pos d] at h
    rw [← Option.some.inj h]
    unfold inDom at d
    simp only [Bool.and_eq_true] at d
    obtain ⟨-, ht, hi, hs⟩ := Fmt.hDom_spec _ _ _ _ _ d.2
    have e : bytesToBits (strOf c) =
        hdr c.half c.number c.tree c.index c.start ++ bytesToBits c.bytes := oStr_bits _ _ _ _ _ _
    rw [e]
    exact ⟨(lw_hdr _ _ _ _ _ hs _).1, (lw_hdr _ _ _ _ _ hs _).2, ht, hi⟩
  · rw [if_neg d] at h
    cases h

/-- The string has the tag of the number n. -/
def No (s : List Bool) (n : ℕ) : Prop := tag16 s = (Wd n).take 16

/-- The seven numbers of the format that occur in the key file's part. -/
def fmtNums : List ℕ := [nFirst, nRow, nLeaf, nNode, nRLeaf, nStored, nRNode]

/-- They are known from their tags. -/
theorem tags_inj : ∀ n ∈ fmtNums, ∀ m ∈ fmtNums, (Wd n).take 16 = (Wd m).take 16 → n = m := by
  decide +kernel

/-- All seven are in the list. -/
theorem mem_nums :
    nFirst ∈ fmtNums ∧ nRow ∈ fmtNums ∧ nLeaf ∈ fmtNums ∧ nNode ∈ fmtNums ∧ nRLeaf ∈ fmtNums ∧
      nStored ∈ fmtNums ∧ nRNode ∈ fmtNums := by
  decide

/-- **A string has the tag of one of the seven numbers at most.** -/
theorem no_inj (s : List Bool) (n m : ℕ) (hn : n ∈ fmtNums) (hm : m ∈ fmtNums) (h : No s n)
    (h' : No s m) : n = m :=
  tags_inj n hn m hm (h.symm.trans h')

/-- The string of a call in the domain has the tag of the call's number. -/
theorem bitsOf_no (c : Fmt.OQ) (s : List Bool) (h : bitsOf c = some s) : No s c.number :=
  tag_of_lw1 c.number c.tree s (bitsOf_words c s h).1

variable (C : KeyCut L K)

/-- **What is asked of the two spellings that the page holds.** -/
structure TakenCalls : Prop where
  /-- the spelling of leaves is one to one -/
  leafInj : ∀ q q' s, C.P.leafX q = some s → C.P.leafX q' = some s → q = q'
  /-- its strings' tag and first byte: the field `hlf` of a code of leaves
  (OnBytes/TypedOracleCompiler/Run/PageG.lean) -/
  leafTag : ∀ q s, C.P.leafX q = some s →
    (tag16 s = t164 ∨ tag16 s = t174) ∧ ∀ b : UInt8, b ≠ 0 → ¬ bitsOfByte b <+: s
  /-- the seeds' spelling is one to one -/
  seedInj : ∀ x x' s, C.P.seeds x = some s → C.P.seeds x' = some s → x = x'
  /-- its strings have the form of a first call or of a row's call, under the seeds' label -/
  seedIs : ∀ x s, C.P.seeds x = some s → Is160 Fmt.recordLabel s ∨ Is162 Fmt.recordLabel s

/-- The numbers of leaves, vertices, first calls, rows and the request tree's two differ. -/
theorem numbers_differ2 :
    nLeaf ≠ nNode ∧ nStored ≠ nNode ∧ nLeaf ≠ nFirst ∧ nLeaf ≠ nRow ∧ nStored ≠ nFirst ∧
      nStored ≠ nRow ∧ nNode ≠ nFirst ∧ nNode ≠ nRow ∧ nLeaf ≠ nRLeaf ∧ nLeaf ≠ nRNode ∧
      nStored ≠ nRLeaf ∧ nStored ≠ nRNode ∧ nNode ≠ nRLeaf ∧ nNode ≠ nRNode ∧ nFirst ≠ nRow := by
  decide

/-- What a spelling's string says of its point, with the tag of its number. -/
theorem taken_call (T : TakenCalls C) (hc : C.P.cfg.size = digBytes) (a : RealPts 256 K L)
    (s : List Bool) (h : takenKey C a = some s) :
    (∃ q, a = .inl q ∧ C.P.leafX q = some s ∧ (No s nLeaf ∨ No s nStored)) ∨
      (∃ q, a = .inr (.inl q) ∧ (pNode C.P.cfg).put q = some s ∧ No s nNode) ∨
      (∃ x, a = .inr (.inr (.inr (.inr (.inl ⟨.test, x⟩)))) ∧ C.P.seeds x = some s ∧
        ((No s nFirst ∧ Is160 Fmt.recordLabel s) ∨ (No s nRow ∧ Is162 Fmt.recordLabel s))) := by
  rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
  · exact Or.inl ⟨q, rfl, h, (T.leafTag q s h).1⟩
  · exact Or.inr (Or.inl ⟨q, rfl, h, pNode_tag C.P.cfg hc q s h⟩)
  · cases h
  · cases h
  · cases t
    · rcases T.seedIs x s h with g | g
      · exact Or.inr (Or.inr ⟨x, rfl, h, Or.inl ⟨tag_160 _ s g, g⟩⟩)
      · exact Or.inr (Or.inr ⟨x, rfl, h, Or.inr ⟨tag_162 _ s g, g⟩⟩)
    · cases h
    · cases h
  · cases t <;> cases h

/-- **The three spellings together are one to one.** -/
theorem taken_inj (T : TakenCalls C) (hc : C.P.cfg.size = digBytes) :
    ∀ a b s, takenKey C a = some s → takenKey C b = some s → a = b := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, -, -, -, -, -, -, -⟩ := numbers_differ2
  obtain ⟨e1, e2, e3, e4, -, e6, -⟩ := mem_nums
  intro a b s ha hb
  rcases taken_call C T hc a s ha with ⟨q, rfl, h1, k1⟩ | ⟨q, rfl, h1, k1⟩ | ⟨x, rfl, h1, k1⟩ <;>
    rcases taken_call C T hc b s hb with
      ⟨q', rfl, h2, k2⟩ | ⟨q', rfl, h2, k2⟩ | ⟨x', rfl, h2, k2⟩
  · rw [T.leafInj q q' s h1 h2]
  · rcases k1 with k1 | k1
    · exact absurd (no_inj s _ _ e3 e4 k1 k2) n1
    · exact absurd (no_inj s _ _ e6 e4 k1 k2) n2
  · rcases k1 with k1 | k1 <;> rcases k2 with ⟨k2, -⟩ | ⟨k2, -⟩
    · exact absurd (no_inj s _ _ e3 e1 k1 k2) n3
    · exact absurd (no_inj s _ _ e3 e2 k1 k2) n4
    · exact absurd (no_inj s _ _ e6 e1 k1 k2) n5
    · exact absurd (no_inj s _ _ e6 e2 k1 k2) n6
  · rcases k2 with k2 | k2
    · exact absurd (no_inj s _ _ e3 e4 k2 k1) n1
    · exact absurd (no_inj s _ _ e6 e4 k2 k1) n2
  · rw [(pNode C.P.cfg).inj h1 h2]
  · rcases k2 with ⟨k2, -⟩ | ⟨k2, -⟩
    · exact absurd (no_inj s _ _ e4 e1 k1 k2) n7
    · exact absurd (no_inj s _ _ e4 e2 k1 k2) n8
  · rcases k2 with k2 | k2 <;> rcases k1 with ⟨k1, -⟩ | ⟨k1, -⟩
    · exact absurd (no_inj s _ _ e3 e1 k2 k1) n3
    · exact absurd (no_inj s _ _ e3 e2 k2 k1) n4
    · exact absurd (no_inj s _ _ e6 e1 k2 k1) n5
    · exact absurd (no_inj s _ _ e6 e2 k2 k1) n6
  · rcases k1 with ⟨k1, -⟩ | ⟨k1, -⟩
    · exact absurd (no_inj s _ _ e4 e1 k2 k1) n7
    · exact absurd (no_inj s _ _ e4 e2 k2 k1) n8
  · rw [T.seedInj x x' s h1 h2]

/-- What a row's call says: its number, and for the chains' rows where a label stands. -/
theorem row_call (a : RealPts 256 K L) (c : Fmt.OQ) (h : rowKey C a = some c) :
    c.number = nRLeaf ∨ c.number = nRNode ∨
      (c.number = nFirst ∧
        (c.index = C.P.key.lab₁ ∨ c.index = C.P.key.lab₂ ∨ c.index = C.P.key.lab₃)) ∨
      (c.number = nRow ∧
        (c.tree = C.P.key.lab₁ ∨ c.tree = C.P.key.lab₂ ∨ c.tree = C.P.key.lab₃)) := by
  rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
  · cases h
  · cases h
  · exact Or.inl (rleaf_number _ _ _ _ h)
  · have h' : (if fitTree q = true then rnodeCall C.P.cfg q else none) = some c := h
    by_cases f : fitTree q = true
    · rw [if_pos f] at h'
      exact Or.inr (Or.inl (rnode_number _ _ _ h'))
    · rw [if_neg f] at h'
      cases h'
  · cases t
    · have h' : (if C.fitFb x = true then fbCallJ C.P.key K x.1 x.2 else none) = some c := h
      by_cases f : C.fitFb x = true
      · rw [if_pos f] at h'
        exact Or.inr (Or.inr (fb_place _ _ _ _ h'))
      · rw [if_neg f] at h'
        cases h'
    · cases h
    · cases h
  · cases t
    · have h' : (if C.fitG q = true then gCallJ C.P.key q else none) = some c := h
      by_cases f : C.fitG q = true
      · rw [if_pos f] at h'
        obtain ⟨g1, g2⟩ := g_place _ _ _ h'
        exact Or.inr (Or.inr (Or.inr ⟨g1, Or.inl g2⟩))
      · rw [if_neg f] at h'
        cases h'
    · cases h
    · cases h

/-- The seeds' label fits its place. -/
theorem recordLabel_lt : Fmt.recordLabel < 2 ^ 48 := by decide

/-- A call in the domain whose string has the form of a first call under the label l has l as its
index. -/
theorem first_label (c : Fmt.OQ) (s : List Bool) (h : bitsOf c = some s) (l : ℕ) (hl : l < 2 ^ 48)
    (g : Is160 l s) : c.index = l := by
  obtain ⟨-, w2, -, hi⟩ := bitsOf_words c s h
  exact word_inj _ _ (by omega) (by omega) (w2.symm.trans g.2.1)

/-- A row's call in the domain whose string has the form of a row's call under the label l has l as
its tree. -/
theorem row_label (c : Fmt.OQ) (s : List Bool) (h : bitsOf c = some s) (hn : c.number = nRow)
    (l : ℕ) (hl : l < 2 ^ 48) (g : Is162 l s) : c.tree = l := by
  obtain ⟨w1, -, ht, -⟩ := bitsOf_words c s h
  rw [hn] at w1
  have e := word_inj _ _ (by unfold nRow; omega) (by omega) (w1.symm.trans g.1)
  unfold nRow at e
  omega

/-- **No string of a spelling is the string of a row's call**, if none of the key file's three
labels is the seeds'. -/
theorem taken_rows (T : TakenCalls C) (hc : C.P.cfg.size = digBytes)
    (l1 : C.P.key.lab₁ ≠ Fmt.recordLabel) (l2 : C.P.key.lab₂ ≠ Fmt.recordLabel)
    (l3 : C.P.key.lab₃ ≠ Fmt.recordLabel) :
    ∀ a b s c, takenKey C a = some s → rowKey C b = some c → bitsOf c ≠ some s := by
  obtain ⟨-, -, n3, n4, n5, n6, n7, n8, m1, m2, m3, m4, m5, m6, m7⟩ := numbers_differ2
  obtain ⟨-, d2, d3, d4, d5⟩ := numbers_differ
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := mem_nums
  intro a b s c ha hb hs
  have kc := bitsOf_no c s hs
  have kb := row_call C b c hb
  rcases taken_call C T hc a s ha with
      ⟨q, -, -, k1 | k1⟩ | ⟨q, -, -, k1⟩ | ⟨x, -, -, ⟨k1, i1⟩ | ⟨k1, i1⟩⟩ <;>
    rcases kb with k2 | k2 | ⟨k2, i2⟩ | ⟨k2, i2⟩ <;> rw [k2] at kc
  · exact m1 (no_inj s _ _ e3 e5 k1 kc)
  · exact m2 (no_inj s _ _ e3 e7 k1 kc)
  · exact n3 (no_inj s _ _ e3 e1 k1 kc)
  · exact n4 (no_inj s _ _ e3 e2 k1 kc)
  · exact m3 (no_inj s _ _ e6 e5 k1 kc)
  · exact m4 (no_inj s _ _ e6 e7 k1 kc)
  · exact n5 (no_inj s _ _ e6 e1 k1 kc)
  · exact n6 (no_inj s _ _ e6 e2 k1 kc)
  · exact m5 (no_inj s _ _ e4 e5 k1 kc)
  · exact m6 (no_inj s _ _ e4 e7 k1 kc)
  · exact n7 (no_inj s _ _ e4 e1 k1 kc)
  · exact n8 (no_inj s _ _ e4 e2 k1 kc)
  · exact d2 (no_inj s _ _ e5 e1 kc k1)
  · exact d4 (no_inj s _ _ e7 e1 kc k1)
  · have e := first_label c s hs _ recordLabel_lt i1
    rcases i2 with i2 | i2 | i2
    · exact l1 (i2.symm.trans e)
    · exact l2 (i2.symm.trans e)
    · exact l3 (i2.symm.trans e)
  · exact m7 (no_inj s _ _ e1 e2 k1 kc)
  · exact d3 (no_inj s _ _ e5 e2 kc k1)
  · exact d5 (no_inj s _ _ e7 e2 kc k1)
  · exact m7 (no_inj s _ _ e1 e2 kc k1)
  · have e := row_label c s hs k2 _ recordLabel_lt i1
    rcases i2 with i2 | i2 | i2
    · exact l1 (i2.symm.trans e)
    · exact l2 (i2.symm.trans e)
    · exact l3 (i2.symm.trans e)

/-- **The strings of the key file's part are one to one where they are written.** -/
theorem cutKey_one (T : TakenCalls C) (hc : C.P.cfg.size = digBytes)
    (l1 : C.P.key.lab₁ ≠ Fmt.recordLabel) (l2 : C.P.key.lab₂ ≠ Fmt.recordLabel)
    (l3 : C.P.key.lab₃ ≠ Fmt.recordLabel)
    (hfb : ∀ x x' c, C.fitFb x = true → C.fitFb x' = true → fbCallJ C.P.key K x.1 x.2 = some c →
      fbCallJ C.P.key K x'.1 x'.2 = some c → x = x')
    (hg : ∀ q q' c, C.fitG q = true → C.fitG q' = true → gCallJ C.P.key q = some c →
      gCallJ C.P.key q' = some c → q = q')
    (hfg : ∀ x q c, C.fitFb x = true → C.fitG q = true → fbCallJ C.P.key K x.1 x.2 = some c →
      gCallJ C.P.key q ≠ some c) :
    ∀ a b s, cutKey C a = some s → cutKey C b = some s → a = b :=
  cutKey_inj C
    (rowKey_inj C (fun q q' c => rleaf_inj _ _ q q' c) (fun q q' c => rnode_inj _ q q' c) hfb hg
      hfg)
    (taken_inj C T hc) (taken_rows C T hc l1 l2 l3)

/-! ## The first byte, and the encoding -/

/-- The string of a call in the domain begins with no byte other than 0 and 1. -/
theorem bitsOf_hd (c : Fmt.OQ) (s : List Bool) (h : bitsOf c = some s) (e : UInt8) (h0 : e ≠ 0)
    (h1 : e ≠ 1) : ¬ bitsOfByte e <+: s := by
  unfold bitsOf at h
  by_cases d : inDom c = true
  · rw [if_pos d] at h
    rw [← Option.some.inj h]
    unfold inDom at d
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at d
    show ¬ bitsOfByte e <+: bytesToBits (Fmt.oStr c.half c.number c.tree c.index c.start c.bytes)
    rw [oStr_bits]
    refine hdr_not_prefix e c.half ?_ _ _ _ _ _
    rcases d.1 with g | g
    · rw [g]
      exact h0
    · rw [g]
      exact h1
  · rw [if_neg d] at h
    cases h

/-- **Its strings begin with no byte other than 0 and 1.** -/
theorem cutKey_hd (T : TakenCalls C) (a : RealPts 256 K L) (s : List Bool)
    (h : cutKey C a = some s) (e : UInt8) (h0 : e ≠ 0) (h1 : e ≠ 1) : ¬ bitsOfByte e <+: s := by
  unfold cutKey at h
  cases ta : takenKey C a with
  | some u =>
    rw [ta] at h
    obtain rfl : u = s := Option.some.inj h
    rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
    · exact (T.leafTag q u ta).2 e h0
    · obtain ⟨y, rfl⟩ := pNode_hdr C.P.cfg q u ta
      exact hdr_not_prefix e 0 h0 _ _ _ _ _
    · cases ta
    · cases ta
    · cases t
      · rcases T.seedIs x u ta with g | g
        · exact g.2.2 e h0
        · exact g.2 e h0 h1
      · cases ta
      · cases ta
    · cases t <;> cases ta
  | none =>
    rw [ta] at h
    obtain ⟨c, -, hs⟩ := Option.bind_eq_some_iff.1 h
    exact bitsOf_hd c s hs e h0 h1

/-- **What is asked for an encoding of the key file's part**: the two spellings' laws; a digest of
32 bytes; none of the three labels is the seeds'; the three laws on the file's chains. -/
structure KeyLaws : Prop where
  /-- the laws on the two spellings that the page holds -/
  taken : TakenCalls C
  /-- the page's digest has 32 bytes -/
  cfg : C.P.cfg.size = digBytes
  /-- none of the file's three labels is the seeds' -/
  lab1 : C.P.key.lab₁ ≠ Fmt.recordLabel
  lab2 : C.P.key.lab₂ ≠ Fmt.recordLabel
  lab3 : C.P.key.lab₃ ≠ Fmt.recordLabel
  /-- two fitting chain queries with a block that have one call are one -/
  fb : ∀ x x' c, C.fitFb x = true → C.fitFb x' = true → fbCallJ C.P.key K x.1 x.2 = some c →
    fbCallJ C.P.key K x'.1 x'.2 = some c → x = x'
  /-- two fitting queries for the slot value that have one call are one -/
  g : ∀ q q' c, C.fitG q = true → C.fitG q' = true → gCallJ C.P.key q = some c →
    gCallJ C.P.key q' = some c → q = q'
  /-- a fitting chain query and a fitting query for the slot value share no call -/
  fbg : ∀ x q c, C.fitFb x = true → C.fitG q = true → fbCallJ C.P.key K x.1 x.2 = some c →
    gCallJ C.P.key q ≠ some c

/-- **The encoding of all typed oracles into one hash function that writes the key file's part as
`cutKey` does**; every other typed point by `back`, behind an escape. -/
noncomputable def mKey (H : KeyLaws C) (back : StrCode (AllPts 256 K L)) :
    OracleCoding (typedOracleFamily 256 K L) 256 :=
  PageOf.implOf (cutKey C)
    (cutKey_one C H.taken H.cfg H.lab1 H.lab2 H.lab3 H.fb H.g H.fbg)
    (cutKey_hd C H.taken) back

end OnBytes.K.Arm
