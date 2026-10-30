-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ProofInj.lean: the function `cutProof` (OnBytes/K/Arm/ProofCut.lean), which writes the
typed queries of a proof file's part of the compiled verifier as strings, is one to one where it
writes: from three laws on the proof file's three chains, laws on two spellings that are taken as
they are, a digest of 32 bytes, and three inequalities: none of the file's three labels is the
seeds'. Under these hypotheses, and from a total code `back`, OnBytes/TypedOracleCompiler/Run/PageOf.lean makes an
encoding in the sense of the soundness theorem that writes these strings.

Strings of different kinds are told apart by the two words of the label that every string of the
format holds at a fixed place (`lw1`, `lw2`, OnBytes/TypedOracleCompiler/Run/Apart.lean; `tag16`,
Run/CodingTag.lean). The laws of OnBytes/K/Arm/KeyInj.lean that name no cut are used here: the
request tree's two kinds (`rleaf_inj`, `rnode_inj`), `fb_place`, `g_place`, `bitsOf_no`, `no_inj`,
`first_label`, `row_label`, `bitsOf_hd`. The named numbers of the format's calls (`nFirst`, `nRow`
and their like) are those of OnBytes/K/Arm/KeyCut.lean and KeyInj.lean. For proofs only; the program
does not import this file.

Main definitions.
 `TakenCallsP`    what is asked of the page's spelling of leaves and of the seeds' spelling: what
                  `TakenCalls` (OnBytes/K/Arm/KeyInj.lean) asks, at a proof file's cut.
 `ProofLaws`      all that is asked, as one record.
 `mProof`         the encoding (`Rom.OracleCoding`) that OnBytes/TypedOracleCompiler/Run/PageOf.lean makes of `cutProof`
                  under `ProofLaws`, at a total code `back`.
Main theorems.
 `takenP_inj`     the three spellings together are one to one.
 `takenP_rows`    no string of a spelling is the string of a row's call, if none of the file's three
                  labels is the seeds'.
 `cutProof_one`   `cutProof` is one to one where it writes.
 `cutProof_hd`    its strings begin with no byte other than 0 and 1.

What is not claimed. That the three laws on the proof file's chains hold at any data. That
`TakenCallsP` holds at any page. That the verifier's queries pass the tests of fitness, or that
their calls lie in the domain. That the cut is not hollow: where both tests of fitness say no
everywhere and the page's two spellings write nothing, nothing is left of the laws but the digest's
length and the three inequalities, and the encoding writes the vertices and the request tree alone;
every other query goes to `back`, behind the escape. So the laws are worth what the tests let
through. That a total code `back` exists at any interface. `mProof` has no program: its parser is
taken by choice. Nothing on the key file's own or the entry file's queries. Nothing on any hash
function; nothing on soundness. Where the page's first statement holds a request through the
format's item, which is made of digests of the request, `ProofLaws` cannot hold at a test of fitness
that lets the first query of every request through: there are more requests than items, so two such
queries would have one call. Nothing here shows that it holds at any test; what this cause leaves
open is a test that lets through a set of instances on which the item is one to one. That it is so
on a given set is a hypothesis on the hash that makes the digests. The set stands in the encoding.
Whoever lays it has to name it without knowledge of the hash function and before any run; nothing
here enforces that. For a request outside the set nothing is tied here. In Lean: the statement is
the field `stm₁` of `C.P.proof` (`FileJ`, OnBytes/Maker/Page/Frame.lean), the law is `ProofLaws.fb`,
the test is `ProofCut.fitFb`.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.ProofCut
import OnBytes.K.Arm.KeyInj

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open TypedOracleCompiler.Run.Apart
open OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : ProofCut L K)

/-- **What is asked of the two spellings that the page holds.** -/
structure TakenCallsP : Prop where
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

/-- What a spelling's string says of its point, with the tag of its number. -/
theorem takenP_call (T : TakenCallsP C) (hc : C.P.cfg.size = digBytes) (a : RealPts 256 K L)
    (s : List Bool) (h : takenProof C a = some s) :
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
theorem takenP_inj (T : TakenCallsP C) (hc : C.P.cfg.size = digBytes) :
    ∀ a b s, takenProof C a = some s → takenProof C b = some s → a = b := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, -, -, -, -, -, -, -⟩ := numbers_differ2
  obtain ⟨e1, e2, e3, e4, -, e6, -⟩ := mem_nums
  intro a b s ha hb
  rcases takenP_call C T hc a s ha with ⟨q, rfl, h1, k1⟩ | ⟨q, rfl, h1, k1⟩ | ⟨x, rfl, h1, k1⟩ <;>
    rcases takenP_call C T hc b s hb with
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
theorem rowP_call (a : RealPts 256 K L) (c : Fmt.OQ) (h : rowProof C a = some c) :
    c.number = nRLeaf ∨ c.number = nRNode ∨
      (c.number = nFirst ∧
        (c.index = C.P.proof.lab₁ ∨ c.index = C.P.proof.lab₂ ∨ c.index = C.P.proof.lab₃)) ∨
      (c.number = nRow ∧
        (c.tree = C.P.proof.lab₁ ∨ c.tree = C.P.proof.lab₂ ∨ c.tree = C.P.proof.lab₃)) := by
  rcases rowProof_cases C a c h with ⟨q, -, h1⟩ | ⟨q, -, -, h1⟩ | ⟨x, -, -, h1⟩ | ⟨q, -, -, h1⟩
  · exact Or.inl (rleaf_number _ _ _ _ h1)
  · exact Or.inr (Or.inl (rnode_number _ _ _ h1))
  · exact Or.inr (Or.inr (fb_place _ _ _ _ h1))
  · obtain ⟨g1, g2⟩ := g_place _ _ _ h1
    exact Or.inr (Or.inr (Or.inr ⟨g1, Or.inl g2⟩))

/-- **No string of a spelling is the string of a row's call**, if none of the proof file's three
labels is the seeds'. -/
theorem takenP_rows (T : TakenCallsP C) (hc : C.P.cfg.size = digBytes)
    (l1 : C.P.proof.lab₁ ≠ Fmt.recordLabel) (l2 : C.P.proof.lab₂ ≠ Fmt.recordLabel)
    (l3 : C.P.proof.lab₃ ≠ Fmt.recordLabel) :
    ∀ a b s c, takenProof C a = some s → rowProof C b = some c → bitsOf c ≠ some s := by
  obtain ⟨-, -, n3, n4, n5, n6, n7, n8, m1, m2, m3, m4, m5, m6, m7⟩ := numbers_differ2
  obtain ⟨-, d2, d3, d4, d5⟩ := numbers_differ
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := mem_nums
  intro a b s c ha hb hs
  have kc := bitsOf_no c s hs
  have kb := rowP_call C b c hb
  rcases takenP_call C T hc a s ha with
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

/-- **The strings of the proof file's part are one to one where they are written.** -/
theorem cutProof_one (T : TakenCallsP C) (hc : C.P.cfg.size = digBytes)
    (l1 : C.P.proof.lab₁ ≠ Fmt.recordLabel) (l2 : C.P.proof.lab₂ ≠ Fmt.recordLabel)
    (l3 : C.P.proof.lab₃ ≠ Fmt.recordLabel)
    (hfb : ∀ x x' c, C.fitFb x = true → C.fitFb x' = true → fbCallJ C.P.proof K x.1 x.2 = some c →
      fbCallJ C.P.proof K x'.1 x'.2 = some c → x = x')
    (hg : ∀ q q' c, C.fitG q = true → C.fitG q' = true → gCallJ C.P.proof q = some c →
      gCallJ C.P.proof q' = some c → q = q')
    (hfg : ∀ x q c, C.fitFb x = true → C.fitG q = true → fbCallJ C.P.proof K x.1 x.2 = some c →
      gCallJ C.P.proof q ≠ some c) :
    ∀ a b s, cutProof C a = some s → cutProof C b = some s → a = b :=
  cutProof_inj C
    (rowProof_inj C (fun q q' c => rleaf_inj _ _ q q' c) (fun q q' c => rnode_inj _ q q' c) hfb hg
      hfg)
    (takenP_inj C T hc) (takenP_rows C T hc l1 l2 l3)

/-! ## The first byte, and the encoding -/

/-- **Its strings begin with no byte other than 0 and 1.** -/
theorem cutProof_hd (T : TakenCallsP C) (a : RealPts 256 K L) (s : List Bool)
    (h : cutProof C a = some s) (e : UInt8) (h0 : e ≠ 0) (h1 : e ≠ 1) : ¬ bitsOfByte e <+: s := by
  unfold cutProof at h
  cases ta : takenProof C a with
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

/-- **What is asked for an encoding of the proof file's part**: the two spellings' laws; a digest of
32 bytes; none of the three labels is the seeds'; the three laws on the file's chains. -/
structure ProofLaws : Prop where
  /-- the laws on the two spellings that the page holds -/
  taken : TakenCallsP C
  /-- the page's digest has 32 bytes -/
  cfg : C.P.cfg.size = digBytes
  /-- none of the file's three labels is the seeds' -/
  lab1 : C.P.proof.lab₁ ≠ Fmt.recordLabel
  lab2 : C.P.proof.lab₂ ≠ Fmt.recordLabel
  lab3 : C.P.proof.lab₃ ≠ Fmt.recordLabel
  /-- two fitting chain queries with a block that have one call are one -/
  fb : ∀ x x' c, C.fitFb x = true → C.fitFb x' = true → fbCallJ C.P.proof K x.1 x.2 = some c →
    fbCallJ C.P.proof K x'.1 x'.2 = some c → x = x'
  /-- two fitting queries for the slot value that have one call are one -/
  g : ∀ q q' c, C.fitG q = true → C.fitG q' = true → gCallJ C.P.proof q = some c →
    gCallJ C.P.proof q' = some c → q = q'
  /-- a fitting chain query and a fitting query for the slot value share no call -/
  fbg : ∀ x q c, C.fitFb x = true → C.fitG q = true → fbCallJ C.P.proof K x.1 x.2 = some c →
    gCallJ C.P.proof q ≠ some c

/-- **The encoding of all typed oracles into one hash function that writes the proof file's part as
`cutProof` does**; every other typed point by `back`, behind an escape. -/
noncomputable def mProof (H : ProofLaws C) (back : StrCode (AllPts 256 K L)) :
    OracleCoding (typedOracleFamily 256 K L) 256 :=
  PageOf.implOf (cutProof C)
    (cutProof_one C H.taken H.cfg H.lab1 H.lab2 H.lab3 H.fb H.g H.fbg)
    (cutProof_hd C H.taken) back

end OnBytes.K.Arm
