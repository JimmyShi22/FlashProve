-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/KeyPage.lean: THE PAGE FOR A KEY's JUDGE, AS A FUNCTION OF PINS, A CODE OF LEAVES
AND A CODE `back`: one total one-to-one code of all typed oracle points, under both tags, in which
every point that KeyFb.lean's two partial codes, the library's code of vertices and the given code
of leaves write has that code's string; and the family over one oracle that it gives. That such a
string is `Fmt.oStr` of a call of the format's form is shown here, each at a typed query of one form
and under conditions on lengths and on K, for the four first values, the hash under 173 and the
seeds' drawing round. For the rounds of the three chains it is shown here under a condition: that
`rcG` writes the bits of a message's bytes and of a nonce's word; OnBytes/TypedOracleCompiler/Run/KeyPageRounds.lean
meets it, at each round's own plain part, where the roots fit the round's items and the nonce fits a
word, with the sibling's spelling `PQ.bytesL` as the message's bytes.

The judge of OnBytes/TypedOracleCompiler/Slice/Plain3XSeeds.lean asks typed oracles: leaves, vertices, chain queries
under the key's tag and under the seeds' tag. To run it over ONE oracle on strings one needs a
one-to-one code of all typed points as strings, with its inverse (library, Rom: `OracleCoding`). This file
joins OnBytes/TypedOracleCompiler/Run/KeyFb.lean's two codes of chain queries, the library's code of vertices and
any code of leaf queries (`PageG.Leaves`) into one partial code of the real points (`PageG.realOf`),
and takes OnBytes/TypedOracleCompiler/Run/PageG.lean's total code and family at it. The sibling is a second
form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `fbAll`: chain queries under all tags: the seeds' under `.test`, none under `.link`, the key's
   under `.onl`; `fbAll_facts`;
 - `realK`: leaves, vertices, chain queries; nothing at the request tree's two oracles and at g,
   which this judge does not ask; `realK_hd`;
 - `pageK : PageG.Page`, `implK : OracleCoding (typedOracleFamily 256 K L) 256`: THE PAGE: total and one to one by its
   type;
 - `oneBlock_implK`: a leaf's and a vertex's answer is one block, taken as it is;
   `implK_not_public`: no typed query but the spare oracle's has a string with another tag than the
   page's six that does not begin with the byte 2;
 - `NotSix`, `notSix_spare`, `implK_call`: the string of a call under 169, 172 or 179 (either half,
   a start of 32 bytes) is a point of the spare oracle, written as itself, and the string of no
   other typed query;
 - `implK_onl`, `implK_test`, `implK_leaf`, `implK_node`: the string of a typed query at which the
   partial code writes IS the partial code's string;
 - `implK_first`, `implK_seedFirst`: two of them spelled out, under conditions on lengths: the key's
   first query (d beside fewer than 2 ^ 32 answers, a salt that is empty or of 256 bits, no root,
   the seam's fixed plain part) has at its tail the bits of `Fmt.oStr` of the hash under 160 at the
   pins' first label, digest and name; the seeds' first query's tail that of the seeds' chain's
   first value, for fixed bytes of fewer than 2 ^ 32.
 - `implK_173`, `implK_first2`, `implK_first3`, `implK_seedRound`: the like at the seams s1, s2, s3
   (at the block of the tail) and at the seeds' drawing round (at every block), under conditions on
   lengths;
 - `implK_round`: the like at a written round, at every block, under the condition named above; also
   asked: the round is on; its index below 2 ^ 64, kind and work below 256; K below 2 ^ 48; a chain
   value of 256 bits;
 - `implK_vertex`: a vertex query on two strings of 256 bits has `Fmt.oStr` of the hash under 166.
   (A leaf query's string: a file of this project that is not in this library, at that file's code
   of leaves.)

Main definitions: `fbAll`, `realK`, `pageK`, `implK`, `NotSix`.
Main theorems: `oneBlock_implK`, `implK_not_public`, `notSix_spare`, `implK_call`, `implK_onl`,
`implK_test`, `implK_leaf`, `implK_node`, `implK_vertex`, `implK_first`, `implK_seedFirst`,
`implK_173`, `implK_first2`, `implK_first3`, `implK_seedRound`, `implK_round`.

Not claimed. NO PINS, NO CODE OF LEAVES AND NO `back` ARE GIVEN: the page is a function of them.
That a key file's typing asks only points that the format writes. No checker, no fit, no tie to the
program. Of what a part asks of its page beyond `OneBlock`: that `back` is the one by which two
parts read a stored table alike; that a part's public strings ARE calls under 169 with a start of 32
bytes (then `implK_call` speaks of them); the pins as hash values over two tables; which K (the
judge's family is over its K + 1). What the heads of KeyFb.lean and PageG.lean do not claim. Nothing
on soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with;
it builds on definitions of Compile/.
THAT THE COMPILED VERIFIER's CHAIN ASKS, UNDER THE
KEY's TAG, THE TYPED QUERIES OF WHICH THESE EQUATIONS SPEAK is stated by no theorem (under the
seeds' tag: OnBytes/TypedOracleCompiler/Slice/SeedsRun.lean).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.KeyFb
import OnBytes.TypedOracleCompiler.Run.PageG
import OnBytes.TypedOracleCompiler.Run.PlainIn

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.KeyPage
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.KeyFb TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.SeamAt
open TypedOracleCompiler.Run.PlainAt TypedOracleCompiler.Run.KeyRanges TypedOracleCompiler.Run.FirstLater
open TypedOracleCompiler.Run.Chain162G
open TypedOracleCompiler.Run.FirstAnswers (T3)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {Sd : Type} {G : Stretches}
  {dec : List T3 × Sd → PQ.View → PQ.View → PQ.View → Bool} {d : Sd} {e : _root_.Fmt.Entry}
  (P : Pins G dec d e) (K : ℕ) (V : Leaves (Lk G dec d e))
  (back : StrCode (AllPts 256 K (Lk G dec d e)))

/-- Chain queries with a block under all tags. -/
def fbAll : PCode (Σ t : Tag, FbIn 256 (Lk G dec d e) t × Fin (K + 1)) :=
  byTag (fbTest P K) (PCode.empty _) (fbOnl P K) (fun _ _ _ h => by cases h)
    (fun _ _ _ _ h => by cases h) (fb_apart P K)

/-- Its strings have the tag of 160, 162 or 173 and begin with the byte 0 or 1. -/
theorem fbAll_facts (b : Σ t : Tag, FbIn 256 (Lk G dec d e) t × Fin (K + 1)) (s : List Bool)
    (h : (fbAll P K).put b = some s) :
    (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ c : UInt8, c ≠ 0 → c ≠ 1 → ¬ bitsOfByte c <+: s := by
  rcases byTag_put _ _ _ _ _ _ b s h with ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨x, hx⟩
  · exact fb_facts P K s (Or.inr ⟨x, hx⟩)
  · cases hx
  · exact fb_facts P K s (Or.inl ⟨x, hx⟩)

/-- The partial code of the real points: leaves, vertices, chain queries. -/
def realK : PCode (RealPts 256 K (Lk G dec d e)) :=
  realOf V P.cfg P.hcfg (fbAll P K) (fbAll_facts P K)

/-- Its strings begin with no byte other than 0 and 1. -/
theorem realK_hd (a : RealPts 256 K (Lk G dec d e)) (s : List Bool)
    (h : (realK P K V).put a = some s) (c : UInt8) (h0 : c ≠ 0) (h1 : c ≠ 1) :
    ¬ bitsOfByte c <+: s := realOf_hd V P.cfg P.hcfg (fbAll P K) (fbAll_facts P K) a s h c h0 h1

/-- The page's data. -/
def pageK : Page (Lk G dec d e) K := ⟨realK P K V, realK_hd P K V, back⟩

/-- THE PAGE: the family over one oracle: a total one-to-one code of all typed points, with its
inverse and both laws. -/
def implK : OracleCoding (typedOracleFamily 256 K (Lk G dec d e)) 256 := implG (pageK P K V back)

/-- A leaf's and a vertex's answer is one block, taken as it is. -/
theorem oneBlock_implK : OneBlock (implK P K V back) := oneBlock_implG (pageK P K V back)

/-- No typed query but the spare oracle's has a string with another tag than the page's six that
does not begin with the byte 2. -/
theorem implK_not_public (o : TypedOracleCompiler.Compile.Batch.OracleName) (ho : o ≠ .other)
    (q : domOf 256 (Lk G dec d e) o) (j : Fin (blk K o)) (s : List Bool)
    (ht : tag16 s ≠ t160 ∧ tag16 s ≠ t162 ∧ tag16 s ≠ t164 ∧ tag16 s ≠ t166 ∧ tag16 s ≠ t173 ∧
      tag16 s ≠ t174) (h2 : ¬ bitsOfByte 2 <+: s) : (implK P K V back).code o q j ≠ s := by
  refine implG_not_public (pageK P K V back) o ho q j s ?_ h2
  cases h : (pageK P K V back).real.parse s with
  | none => rfl
  | some a =>
    exfalso
    rcases realOf_tag V P.cfg P.hcfg (fbAll P K) (fbAll_facts P K) a s
      ((pageK P K V back).real.put_parse s a h) with e | e | e | e | e | e
    · exact ht.1 e
    · exact ht.2.1 e
    · exact ht.2.2.1 e
    · exact ht.2.2.2.1 e
    · exact ht.2.2.2.2.1 e
    · exact ht.2.2.2.2.2 e

/-- The number n has another tag than the page's six. -/
def NotSix (n : ℕ) : Prop :=
  (Wd n).take 16 ≠ t160 ∧ (Wd n).take 16 ≠ t162 ∧ (Wd n).take 16 ≠ t164 ∧
    (Wd n).take 16 ≠ t166 ∧ (Wd n).take 16 ≠ t173 ∧ (Wd n).take 16 ≠ t174

/-- The numbers of the calls that a key's checker makes beside the typed ones: 169 (a digest of
public bytes), 172 (a run value), 179 (a commitment ID). -/
theorem notSix_spare : NotSix 169 ∧ NotSix 172 ∧ NotSix 179 := by
  unfold NotSix
  decide +kernel

/-- The tag of the string of a call, for a start of 32 bytes. -/
theorem tag_call (half : UInt8) (n t i : ℕ) (st bs : ByteArray) (hst : st.size = 32) :
    tag16 (bytesToBits (_root_.Fmt.oStr half n t i st bs)) = (Wd n).take 16 := by
  rw [oStr_bits]
  exact (tag16_hdr half n t i st hst _).trans (tag_low n t)

/-- The string of a call under a number with another tag than the six (so under 169, 172, 179),
either half, a start of 32 bytes, is a point of the spare oracle, written as itself, and the string
of no other typed query. -/
theorem implK_call (n : ℕ) (hn : NotSix n) (half : UInt8) (hh : half = 0 ∨ half = 1) (t i : ℕ)
    (st bs : ByteArray) (hst : st.size = 32) :
    (∀ j, (implK P K V back).code .other (bytesToBits (_root_.Fmt.oStr half n t i st bs)) j =
        bytesToBits (_root_.Fmt.oStr half n t i st bs)) ∧
      ∀ (o : TypedOracleCompiler.Compile.Batch.OracleName), o ≠ .other → ∀ (q : domOf 256 (Lk G dec d e) o)
        (j : Fin (blk K o)),
        (implK P K V back).code o q j ≠ bytesToBits (_root_.Fmt.oStr half n t i st bs) := by
  have ht := tag_call half n t i st bs hst
  have hb : ∀ c : UInt8, c ≠ half →
      ¬ bitsOfByte c <+: bytesToBits (_root_.Fmt.oStr half n t i st bs) := fun c hc => by
    rw [oStr_bits]
    exact hdr_not_prefix c half hc _ _ _ _ _
  have n2 : (2 : UInt8) ≠ half := by rcases hh with rfl | rfl <;> decide
  have n3 : (3 : UInt8) ≠ half := by rcases hh with rfl | rfl <;> decide
  have h6 : tag16 (bytesToBits (_root_.Fmt.oStr half n t i st bs)) ≠ t160 ∧
      tag16 (bytesToBits (_root_.Fmt.oStr half n t i st bs)) ≠ t162 ∧
      tag16 (bytesToBits (_root_.Fmt.oStr half n t i st bs)) ≠ t164 ∧
      tag16 (bytesToBits (_root_.Fmt.oStr half n t i st bs)) ≠ t166 ∧
      tag16 (bytesToBits (_root_.Fmt.oStr half n t i st bs)) ≠ t173 ∧
      tag16 (bytesToBits (_root_.Fmt.oStr half n t i st bs)) ≠ t174 := by
    rw [ht]
    exact hn
  refine ⟨fun j => implG_other' (pageK P K V back) _ j (fun a ha => ?_) (hb 2 n2) (hb 3 n3),
    fun o ho q j => implK_not_public P K V back o ho q j _ h6 (hb 2 n2)⟩
  rcases realOf_tag V P.cfg P.hcfg (fbAll P K) (fbAll_facts P K) a _ ha with e | e | e | e | e | e
  · exact h6.1 e
  · exact h6.2.1 e
  · exact h6.2.2.1 e
  · exact h6.2.2.2.1 e
  · exact h6.2.2.2.2.1 e
  · exact h6.2.2.2.2.2 e

/-- The string of a chain query under the key's tag at which `fbOnl` writes. -/
theorem implK_onl (q : FbIn 256 (Lk G dec d e) .onl) (j : Fin (K + 1)) (s : List Bool)
    (h : (fbOnl P K).put (q, j) = some s) : (implK P K V back).code (.fb .onl) q j = s :=
  implG_fb (pageK P K V back) .onl q j s h

/-- The string of a chain query under the seeds' tag at which `fbTest` writes. -/
theorem implK_test (q : FbIn 256 (Lk G dec d e) .test) (j : Fin (K + 1)) (s : List Bool)
    (h : (fbTest P K).put (q, j) = some s) : (implK P K V back).code (.fb .test) q j = s :=
  implG_fb (pageK P K V back) .test q j s h

/-- The string of a leaf query at which the code of leaves writes. -/
theorem implK_leaf (q : LeafIn (Lk G dec d e)) (s : List Bool) (h : V.lf.put q = some s)
    (j : Fin 1) : (implK P K V back).code .leaf q j = s := implG_leaf (pageK P K V back) q s h j

/-- The string of a node query at which the library's code of vertices writes. -/
theorem implK_node (q : Bits × Bits) (s : List Bool) (h : (pNode P.cfg).put q = some s)
    (j : Fin 1) : (implK P K V back).code .node q j = s := implG_node (pageK P K V back) q s h j

/-- A vertex query on two strings of 256 bits has `Fmt.oStr` of the hash under 166, with the
configuration's digest as the start, on the two strings' bytes. -/
theorem implK_vertex (l r : Bits) (hl : l.length = 256) (hr : r.length = 256) (j : Fin 1) :
    (implK P K V back).code .node (l, r) j =
      bytesToBits (_root_.Fmt.oStr 0 166 0 0 P.cfg (bitsToBytes l ++ bitsToBytes r)) :=
  implK_node P K V back (l, r) _ (pNode_put P.cfg l r hl hr) j

/-- The key's first typed query, at the block of its tail, has the format's string of chain 1's
first value: the hash under 160 with the first label, on the first parameter digest, the table's
item of root and answers, an empty record, and the salt as the run value. For fewer than 2 ^ 32
answers and a salt that is empty or has 256 bits. -/
theorem implK_first (cm : Dig 256) (x : List T3) (salt : List Bool) (hx : x.length < 2 ^ 32)
    (hl : salt = [] ∨ salt.length = 256) :
    (implK P K V back).code (.fb .onl)
        ⟨0, .f1 [cm] (some (x, d)) salt, [], in0 G G.s0.r.dPlain⟩ (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 P.l₁ _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes P.pd₁) (_root_.Fmt.tableItem P.name (digToBytes cm) x)
          ByteArray.empty (runOf salt))) := by
  refine implK_onl P K V back _ _ _ ?_
  rw [fbOnl_at0 P K _ rfl]
  exact tailP_some _ K _ _ (FirstAnswers.firstPA_put _ _ _ _ _ _ _ _ _ _ _ _ cm x salt hx hl)

/-- The seeds' chain's first typed query, at the block of its tail, has the format's string of
that chain's first value, with the root and the pins' fixed bytes as the statement. For fixed
bytes of fewer than 2 ^ 32. -/
theorem implK_seedFirst (cm : Dig 256) (hr : P.rest.size < 2 ^ 32) :
    (implK P K V back).code (.fb .test) (q0S (L := Lk G dec d e) .test G.C e _ id [cm])
        (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 _root_.Fmt.recordLabel _root_.Fmt.zero32
        (_root_.Fmt.firstBytes _root_.Fmt.zero32 (digToBytes cm ++ P.rest) ByteArray.empty
          none)) := by
  refine implK_test P K V back _ _ _ ?_
  rw [fbTest_at0 P K _ rfl]
  refine tailP_some _ K _ _ ?_
  have h := FirstName.firstPN_put P.rest (Lk G dec d e) .test
    (p0S (L := Lk G dec d e) .test G.C e _ id) (isEq _) FirstName.zeroPd (isEq_iff _)
    _root_.Fmt.recordLabel cm hr
  rw [FirstName.zeroPd_bytes] at h
  exact h

/-- The typed query at the seam s1, at the block of its tail, has `Fmt.oStr` of the hash under
173: at the pins' two numbers, with the configuration's digest as the start, on the chain value's
bytes and the salt's. For a chain value of 256 bits and a salt of the pins' number of bytes. -/
theorem implK_173 (ρ sa : Bits) (hρ : ρ.length = 256) (hs : sa.length = 8 * P.sB) :
    (implK P K V back).code (.fb .onl) ⟨at1 G, .f2 none ρ, [], in1 G (P.e₁.symm sa)⟩ (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 173 P.above P.index P.cfg
        (bitsToBytes ρ ++ bitsToBytes sa)) := by
  refine implK_onl P K V back _ _ _ ?_
  rw [fbOnl_at1 P K _ rfl]
  exact tailP_some _ K _ _ (seamP_some (d1 P) _ ρ sa _
    (p173_str P.cfg P.hcfg P.above P.index P.sB ρ sa hρ hs))

/-- The typed query at the seam s2, at the block of its tail, has `Fmt.oStr` of the hash under 160
with the second label: on the second parameter digest, the table's item of the root and answers
that the seam's plain part carries and then the item of the chain value as the binding root, an
empty record, and the run value that the plain part carries. For a chain value of 256 bits, fewer
than 2 ^ 32 answers, a statement of fewer than 2 ^ 64 bytes, a run value of 256 bits or none. -/
theorem implK_first2 (ρ : Bits) (hρ : ρ.length = 256) (cm : Dig 256) (x : List T3) (run : Bits)
    (hx : x.length < 2 ^ 32)
    (hs : (_root_.Fmt.tableItem P.name (digToBytes cm) x ++
      _root_.Fmt.item _root_.Fmt.bindRootName (digToBytes (digOf ρ))).size < 2 ^ 64)
    (hl : run = [] ∨ run.length = 256) :
    (implK P K V back).code (.fb .onl)
        ⟨at2 G, .f2 none ρ, [], in2 G (P.e₂.symm ((cm, x), run))⟩ (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 P.l₂ _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes P.pd₂)
          (_root_.Fmt.tableItem P.name (digToBytes cm) x ++
            _root_.Fmt.item _root_.Fmt.bindRootName (digToBytes (digOf ρ)))
          ByteArray.empty (runOf run))) := by
  refine implK_onl P K V back _ _ _ ?_
  rw [fbOnl_at2 P K _ rfl]
  exact tailP_some _ K _ _ (seamP_some (d2 P) _ ρ ((cm, x), run) _
    (pFirstAt_str _ _ _ _ _ _ ρ hρ (cm, x) run _ (if_pos hx) hs hl))

/-- The typed query at the seam s3, at the block of its tail, has `Fmt.oStr` of the hash under 160
with the third label: on the third parameter digest, the items of two seals, first the one that
the seam's plain part carries, then the chain value, an empty record, and the run value that the
plain part carries. For a chain value of 256 bits, a statement of fewer than 2 ^ 64 bytes, a run
value of 256 bits or none. -/
theorem implK_first3 (ρ : Bits) (hρ : ρ.length = 256) (s1 : Dig 256) (run : Bits)
    (hs : (_root_.Fmt.sealItems [digToBytes s1, digToBytes (digOf ρ)]).size < 2 ^ 64)
    (hl : run = [] ∨ run.length = 256) :
    (implK P K V back).code (.fb .onl)
        ⟨at3 G, .f2 none ρ, [], in3 G (P.e₃.symm (s1, run))⟩ (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 P.l₃ _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes P.pd₃)
          (_root_.Fmt.sealItems [digToBytes s1, digToBytes (digOf ρ)])
          ByteArray.empty (runOf run))) := by
  refine implK_onl P K V back _ _ _ ?_
  rw [fbOnl_at3 P K _ rfl]
  exact tailP_some _ K _ _ (seamP_some (d3 P) _ ρ (s1, run) _
    (pFirstAt_str _ _ _ _ _ _ ρ hρ s1 run _ rfl hs hl))

/-- The seeds' chain's drawing round's typed query, at every block, has `Fmt.oStr` of one half of
a hash under 162 on the seeds' chain: round 1, the chain value as the start, no message, the kind
"seeds", no work, the nonce 0; b, the typed block's number in the format's row, gives the half and
the call. For a chain value of 256 bits and K below 2 ^ 48. -/
theorem implK_seedRound (hK : K < 2 ^ 48) (ρ : Bits) (hρ : ρ.length = 256) (j : Fin (K + 1)) :
    (implK P K V back).code (.fb .test) (q1S (L := Lk G dec d e) .test G.C e _ id ρ) j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (blockNo 0 K j % 2)) 162
        _root_.Fmt.recordLabel 1 (bitsToBytes ρ)
        (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 (blockNo 0 K j / 2))) := by
  refine implK_test P K V back _ _ _ ?_
  rw [fbTest_else P K _ (by show (1 : ℕ) ≠ 0; decide)]
  exact SeedRound.secondPS_put _ _ _ _ _ K hK ρ hρ j

/-- A typed query at a written round, at every block, has `Fmt.oStr` of one half of a hash under
162, with the label and index of `KeyRanges.threeOf`, the chain value as the start, on the
library's `roundBytes` of the message, the round's kind and work, the call and the nonce: UNDER THE
CONDITION hr that `rcG` writes, at this round, roots and plain part, the bits of the message's bytes
and then of the nonce's word. Also asked: the round is on; index below 2 ^ 64, kind and work below
256, K below 2 ^ 48; a chain value of 256 bits. b is the block's number in the row, by `ordAt`. -/
theorem implK_round (hK : K < 2 ^ 48) (i : ℕ) (ho : (threeOf G P.l₁ P.l₂ P.l₃).on i = true)
    (hi : (threeOf G P.l₁ P.l₂ P.l₃).idx i < 2 ^ 64) (hk : kindAt G i < 256)
    (hw : workAt G i < 256) (ρ : Bits) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (pl : PBa G.sh) (msg : ByteArray) (nonce : ℕ)
    (hr : (rcG G i).put (rt, pl) =
      some (bytesToBits msg ++ bytesToBits (_root_.Fmt.u64n nonce))) (j : Fin (K + 1)) :
    (implK P K V back).code (.fb .onl) ⟨i, .f2 none ρ, rt, pl⟩ j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat ((blockTo (ordAt G i) K j).val % 2)) 162
        ((threeOf G P.l₁ P.l₂ P.l₃).lab i) ((threeOf G P.l₁ P.l₂ P.l₃).idx i) (bitsToBytes ρ)
        (roundBytes msg (kindAt G i) (workAt G i) ((blockTo (ordAt G i) K j).val / 2) nonce)) := by
  have hs := PlainIn.rdAt_seam G
  have hon : (rdAt G i).isSome = true := (PlainIn.on_iff G P.l₁ P.l₂ P.l₃ i).symm.trans ho
  have hne : ∀ k, rdAt G k = none → i ≠ k := fun k hk e => by
    rw [e, hk] at hon
    cases hon
  have hl : (threeOf G P.l₁ P.l₂ P.l₃).lab i < 2 ^ 48 := by
    rcases lab_mem (threeOf G P.l₁ P.l₂ P.l₃) i with e1 | e1 | e1 <;> rw [e1]
    · exact P.hlt.1
    · exact P.hlt.2.1
    · exact P.hlt.2.2
  refine implK_onl P K V back _ _ _ ?_
  rw [fbOnl_else P K _ (hne 0 hs.1) (hne _ hs.2.1) (hne _ hs.2.2.1) (hne _ hs.2.2.2)]
  exact p162G_str (keyChain (L := Lk G dec d e) (tg := .onl) G P.l₁ P.l₂ P.l₃ P.h12 P.h13 P.h23
    (rcG G) (rcG_ge G)) K hK i ho hl hi hk hw ρ hρ rt pl msg nonce hr j

end TypedOracleCompiler.Run.KeyPage
