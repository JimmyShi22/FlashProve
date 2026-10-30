-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/EntryPage.lean: THE PAGE FOR AN ENTRY's JUDGE, AS A FUNCTION OF PINS, A CODE OF
LEAVES AND A CODE `back`: one total one-to-one code of all typed oracle points, under the link's and
the seeds' tags, in which every point that EntryFb.lean's two partial codes, the library's code of
vertices and the given code of leaves write has that code's string; the family over one oracle that
it gives; and, for chain queries of the four forms named below and for vertices on two strings of
256 bits, under conditions, that string as `Fmt.oStr` of a call of the format's form. For leaves no
such equation is stated here (OnBytes/TypedOracleCompiler/Slice/EntryFill.lean: `pageForE_leaf`). That the partial
codes write at no other query is not stated.

It does for an entry what OnBytes/TypedOracleCompiler/Run/KeyPage.lean and KeyPageRounds.lean do for a key. The
judge of an entry file with instances (OnBytes/TypedOracleCompiler/Slice/EntryXJudge.lean) asks typed oracles:
leaves, vertices, chain queries under the link's tag and under the seeds' tag. To run it over ONE
oracle on strings one needs a one-to-one code of all typed points as strings, with its inverse
(library, Rom: `OracleCoding`). The sibling is a second form of the library's soundness road, under
OnBytes/TypedOracleCompiler/.
 - `fbAllE`: chain queries under all tags: the seeds' under `.test`, the link's under `.link`, none
   under `.onl`; `fbAllE_facts`;
 - `realE`, `pageE`, `implE : OracleCoding (typedOracleFamily 256 K L) 256`: THE PAGE: total and one to one by its type;
 - `oneBlock_implE`: a leaf's and a vertex's answer is one block, taken as it is; `implE_blocks`: no
   answer has more than K + 1 blocks;
 - `implE_not_public`: no typed query but the spare oracle's has a string with another tag than 160,
   162, 164, 166, 173, 174 that does not begin with the byte 2; `implE_call`: the string of a call
   under 169, 172 or 179 (either half, a start of 32 bytes) is a point of the spare oracle, written
   as itself, and the string of no other typed query;
 - `implE_link`, `implE_test`, `implE_leaf`, `implE_node`: the string of a typed query at which the
   partial code writes IS the partial code's string;
 - THE EQUATIONS, each at a typed query of one form, under conditions on lengths and on K:
   `implE_first`: the first query (two outer roots, both tables' answers beside dd, a salt that is
   empty or of 256 bits), at the block of its tail: the hash under 160 at the pins' label and digest
   on the two tables' items; `implE_round`: the written round k, at its own plain part, at every
   block: one half of a hash under 162 with the pins' label and the index k + 1, on the sibling's
   spelling `PQ.bytesL` of the message and the format's `Fmt.tail`; where the roots fit the round's
   items and the nonce fits a word; `implE_seedFirst`, `implE_seedRound`: the seeds' chain's two
   queries; `implE_vertex`: a vertex query on two strings of 256 bits.

Main definitions: `fbAllE`, `realE`, `pageE`, `implE`.
Main theorems: `oneBlock_implE`, `implE_blocks`, `implE_not_public`, `implE_call`, `implE_link`,
`implE_test`, `implE_leaf`, `implE_node`, `implE_first`, `implE_round`, `implE_seedFirst`,
`implE_seedRound`, `implE_vertex`.

Not claimed. NO PINS, NO CODE OF LEAVES AND NO `back` ARE GIVEN: the page is a function of them.
THAT THE COMPILED VERIFIER's CHAIN ASKS, UNDER THE LINK's TAG, THE TYPED QUERIES OF WHICH THESE
EQUATIONS SPEAK is stated by no theorem here. The link's wiring at this interface is carried along
an equation between two markings of "all rounds local" that is no unfolding: so which queries the
chain asks does not follow by unfolding, as it does under the seeds' tag. That the salt of a typed
proof is the run's value, a hash under 172 of the parameter digest and the file's 32 random bytes:
the typing's duty. That the roots which the chain takes in a round (as many as the round has trees)
fit the round's items. The pins' cfg and pd are meant to be hash values over two tables: one page
for each pair of tables; which K. That `PQ.bytesL` is the message that a program's reader hashes.
`Fmt.oStr` is total: that a call lies in the format's domain is not asked. That a part's public
strings are calls under 169 with a start of 32 bytes. That `back` is the one by which two parts read
a stored table alike. b, a block's number in the row, is by the order `EntryFb.ordE`. What the heads
of EntryFb.lean, EntryFirst.lean and PageG.lean do not claim. No checker, no fit, no tie to the
program. Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.EntryFb
import OnBytes.TypedOracleCompiler.Run.KeyPageRounds

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.EntryPage
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.SeamAt
open TypedOracleCompiler.Run.PlainIn TypedOracleCompiler.Run.Chain162G
open TypedOracleCompiler.Run.KeyPage (NotSix tag_call)
open TypedOracleCompiler.Run.KeyPageRounds (pRound_eq kind_lt ordOf)
open TypedOracleCompiler.Run.KeyFb (isEq isEq_iff)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {Sd : Type} {D : XD}
  {early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd} {e : _root_.Fmt.Entry}
  (P : PinsE D early e) (dd : Sd) (K : ℕ) (V : Leaves (Le D early e))
  (back : StrCode (AllPts 256 K (Le D early e)))

/-- Chain queries with a block under all tags. -/
def fbAllE : PCode (Σ t : Tag, FbIn 256 (Le D early e) t × Fin (K + 1)) :=
  byTag (fbSeeds P K) (fbLink P dd K) (PCode.empty _) (fun _ _ _ _ h => by cases h)
    (fbE_apart P dd K) (fun _ _ _ _ h => by cases h)

/-- Its strings have the tag of 160 or 162 (stated with a third case, 173, which the general page
admits and no string here has) and begin with the byte 0 or 1. -/
theorem fbAllE_facts (b : Σ t : Tag, FbIn 256 (Le D early e) t × Fin (K + 1)) (s : List Bool)
    (h : (fbAllE P dd K).put b = some s) :
    (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ c : UInt8, c ≠ 0 → c ≠ 1 → ¬ bitsOfByte c <+: s := by
  rcases byTag_put _ _ _ _ _ _ b s h with ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨x, hx⟩
  · exact fbE_facts P dd K s (Or.inr ⟨x, hx⟩)
  · exact fbE_facts P dd K s (Or.inl ⟨x, hx⟩)
  · cases hx

/-- The partial code of the real points: leaves, vertices, chain queries. -/
def realE : PCode (RealPts 256 K (Le D early e)) :=
  realOf V P.cfg P.hcfg (fbAllE P dd K) (fbAllE_facts P dd K)

/-- The page's data. -/
def pageE : Page (Le D early e) K :=
  ⟨realE P dd K V, realOf_hd V P.cfg P.hcfg (fbAllE P dd K) (fbAllE_facts P dd K), back⟩

/-- THE PAGE: the family over one oracle: a total one-to-one code of all typed points, with its
inverse and both laws. -/
def implE : OracleCoding (typedOracleFamily 256 K (Le D early e)) 256 := implG (pageE P dd K V back)

/-- A leaf's and a vertex's answer is one block, taken as it is. -/
theorem oneBlock_implE : OneBlock (implE P dd K V back) := oneBlock_implG (pageE P dd K V back)

/-- No answer has more than K + 1 blocks. -/
theorem implE_blocks (o : TypedOracleCompiler.Compile.Batch.OracleName) :
    (implE P dd K V back).blocks o ≤ K + 1 := by
  cases o with
  | fb t => exact Nat.le_refl _
  | fbw t k => exact Nat.le_refl _
  | ann => exact Nat.zero_le _
  | leaf => exact Nat.le_add_left 1 K
  | node => exact Nat.le_add_left 1 K
  | rleaf => exact Nat.le_add_left 1 K
  | rnode => exact Nat.le_add_left 1 K
  | g t => exact Nat.le_add_left 1 K
  | other => exact Nat.le_add_left 1 K

/-- No typed query but the spare oracle's has a string with another tag than the six that does not
begin with the byte 2. -/
theorem implE_not_public (o : TypedOracleCompiler.Compile.Batch.OracleName) (ho : o ≠ .other)
    (q : domOf 256 (Le D early e) o) (j : Fin (blk K o)) (s : List Bool)
    (ht : tag16 s ≠ t160 ∧ tag16 s ≠ t162 ∧ tag16 s ≠ t164 ∧ tag16 s ≠ t166 ∧ tag16 s ≠ t173 ∧
      tag16 s ≠ t174) (h2 : ¬ bitsOfByte 2 <+: s) : (implE P dd K V back).code o q j ≠ s := by
  refine implG_not_public (pageE P dd K V back) o ho q j s ?_ h2
  cases h : (pageE P dd K V back).real.parse s with
  | none => rfl
  | some a =>
    exfalso
    rcases realOf_tag V P.cfg P.hcfg (fbAllE P dd K) (fbAllE_facts P dd K) a s
      ((pageE P dd K V back).real.put_parse s a h) with e | e | e | e | e | e
    · exact ht.1 e
    · exact ht.2.1 e
    · exact ht.2.2.1 e
    · exact ht.2.2.2.1 e
    · exact ht.2.2.2.2.1 e
    · exact ht.2.2.2.2.2 e

/-- The string of a call under a number with another tag than the six (so under 169, 172, 179:
`KeyPage.notSix_spare`), either half, a start of 32 bytes, is a point of the spare oracle, written
as itself, and the string of no other typed query. -/
theorem implE_call (n : ℕ) (hn : NotSix n) (half : UInt8) (hh : half = 0 ∨ half = 1) (t i : ℕ)
    (st bs : ByteArray) (hst : st.size = 32) :
    (∀ j, (implE P dd K V back).code .other (bytesToBits (_root_.Fmt.oStr half n t i st bs)) j =
        bytesToBits (_root_.Fmt.oStr half n t i st bs)) ∧
      ∀ (o : TypedOracleCompiler.Compile.Batch.OracleName), o ≠ .other → ∀ (q : domOf 256 (Le D early e) o)
        (j : Fin (blk K o)),
        (implE P dd K V back).code o q j ≠ bytesToBits (_root_.Fmt.oStr half n t i st bs) := by
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
  refine ⟨fun j => implG_other' (pageE P dd K V back) _ j (fun a ha => ?_) (hb 2 n2) (hb 3 n3),
    fun o ho q j => implE_not_public P dd K V back o ho q j _ h6 (hb 2 n2)⟩
  rcases realOf_tag V P.cfg P.hcfg (fbAllE P dd K) (fbAllE_facts P dd K) a _ ha with
    e | e | e | e | e | e
  · exact h6.1 e
  · exact h6.2.1 e
  · exact h6.2.2.1 e
  · exact h6.2.2.2.1 e
  · exact h6.2.2.2.2.1 e
  · exact h6.2.2.2.2.2 e

/-- The string of a chain query under the link's tag at which `fbLink` writes. -/
theorem implE_link (q : FbIn 256 (Le D early e) .link) (j : Fin (K + 1)) (s : List Bool)
    (h : (fbLink P dd K).put (q, j) = some s) : (implE P dd K V back).code (.fb .link) q j = s :=
  implG_fb (pageE P dd K V back) .link q j s h

/-- The string of a chain query under the seeds' tag at which `fbSeeds` writes. -/
theorem implE_test (q : FbIn 256 (Le D early e) .test) (j : Fin (K + 1)) (s : List Bool)
    (h : (fbSeeds P K).put (q, j) = some s) : (implE P dd K V back).code (.fb .test) q j = s :=
  implG_fb (pageE P dd K V back) .test q j s h

/-- The string of a leaf query at which the code of leaves writes. -/
theorem implE_leaf (q : LeafIn (Le D early e)) (s : List Bool) (h : V.lf.put q = some s)
    (j : Fin 1) : (implE P dd K V back).code .leaf q j = s :=
  implG_leaf (pageE P dd K V back) q s h j

/-- The string of a node query at which the library's code of vertices writes. -/
theorem implE_node (q : Bits × Bits) (s : List Bool) (h : (pNode P.cfg).put q = some s)
    (j : Fin 1) : (implE P dd K V back).code .node q j = s :=
  implG_node (pageE P dd K V back) q s h j

/-- A vertex query on two strings of 256 bits has `Fmt.oStr` of the hash under 166, with the
configuration's digest as the start, on the two strings' bytes. -/
theorem implE_vertex (l r : Bits) (hl : l.length = 256) (hr : r.length = 256) (j : Fin 1) :
    (implE P dd K V back).code .node (l, r) j =
      bytesToBits (_root_.Fmt.oStr 0 166 0 0 P.cfg (bitsToBytes l ++ bitsToBytes r)) :=
  implE_node P dd K V back (l, r) _ (pNode_put P.cfg l r hl hr) j

/-- The link's first typed query, at the block of its tail, has `Fmt.oStr` of the hash under 160
with the pins' label: on the pins' parameter digest, the first table's item and then the further
table's, an empty record, and the salt as the run value. For fewer than 2 ^ 32 answers each and a
salt that is empty or has 256 bits. -/
theorem implE_first (r₀ r₁ : Dig 256) (a₀ a₁ : List T3) (salt : List Bool)
    (h₀ : a₀.length < 2 ^ 32) (h₁ : a₁.length < 2 ^ 32) (hl : salt = [] ∨ salt.length = 256) :
    (implE P dd K V back).code (.fb .link)
        ⟨0, .f1 [r₀, r₁] (some ((a₀, a₁), dd)) salt, [], p0E D early e⟩ (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 P.l _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes P.pd)
          (_root_.Fmt.tableItem "the first table" (digToBytes r₀) a₀ ++
            _root_.Fmt.tableItem "the further table" (digToBytes r₁) a₁)
          ByteArray.empty (runOf salt))) := by
  refine implE_link P dd K V back _ _ _ ?_
  rw [fbLink_at0 P dd K _ rfl]
  exact tailP_some _ K _ _ (EntryFirst.firstPE_put _ _ _ _ _ _ _ _ _ _ r₀ r₁ a₀ a₁ salt h₀ h₁ hl)

/-- The written round k, at its own plain part, at every block, has `Fmt.oStr` of one half of a
hash under 162 with the pins' label and the index k + 1, the chain value as the start, on the
sibling's spelling of the message and then the format's tail. Asked: the roots fit the round's items
and the nonce fits a word; work below 256; the index below 2 ^ 64; K below 2 ^ 48; a chain value of
256 bits. b, the block's number in the row, is by the order `ordOf` of the round. -/
theorem implE_round (hK : K < 2 ^ 48) (k : Fin D.ds.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (D.ds.get k).entry.work < 256) (ρ : Bits) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (z : PlainD (D.ds.get k))
    (hok : PQ.okRound (D.ds.get k).entry.work (D.ds.get k).items rt z = true)
    (j : Fin (K + 1)) :
    (implE P dd K V back).code (.fb .link) ⟨k.val + 1, .f2 none ρ, rt, inE D early e k z⟩ j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat ((blockTo (ordOf (D.ds.get k)) K j).val % 2)) 162
        P.l (k.val + 1) (bitsToBytes ρ)
        (PQ.bytesL (rt.map digToBytes) (D.ds.get k).items
            (GPlain.old (b := (D.ds.get k).entry.work) z) ++
          _root_.Fmt.tail (D.ds.get k).kind (D.ds.get k).entry.work
            (GPlain.nonce (b := (D.ds.get k).entry.work) z)
            ((blockTo (ordOf (D.ds.get k)) K j).val / 2))) := by
  have hr := rdE_at D k
  have ek : kindE D (k.val + 1) = (D.ds.get k).kind.num := by unfold kindE; rw [hr]; rfl
  have ew : workE D (k.val + 1) = (D.ds.get k).entry.work := by unfold workE; rw [hr]; rfl
  have eo : ordE D (k.val + 1) = ordOf (D.ds.get k) := by unfold ordE; rw [hr]; rfl
  have ho : onE D.ds.length (k.val + 1) = true :=
    decide_eq_true ⟨Nat.le_add_left 1 _, k.isLt⟩
  refine implE_link P dd K V back _ _ _ ?_
  rw [fbLink_else P dd K _ (Nat.succ_ne_zero _)]
  have h := p162G_str (linkChain P) K hK (k.val + 1) ho P.hlt hi
    (by show kindE D (k.val + 1) < 256; rw [ek]; exact kind_lt _)
    (by show workE D (k.val + 1) < 256; rw [ew]; exact hw) ρ hρ rt (inE D early e k z) _ _
    ((rcE_at D early e k rt z).trans (pRound_eq _ _ rt z hok)) j
  have h' : (e162 P K).put (⟨k.val + 1, .f2 none ρ, rt, inE D early e k z⟩, j) =
      some (bytesToBits (_root_.Fmt.oStr
        (UInt8.ofNat ((blockTo (ordE D (k.val + 1)) K j).val % 2)) 162 P.l (k.val + 1)
        (bitsToBytes ρ)
        (roundBytes (PQ.bytesL (rt.map digToBytes) (D.ds.get k).items
            (GPlain.old (b := (D.ds.get k).entry.work) z))
          (kindE D (k.val + 1)) (workE D (k.val + 1))
          ((blockTo (ordE D (k.val + 1)) K j).val / 2)
          (GPlain.nonce (b := (D.ds.get k).entry.work) z)))) := h
  rw [ek, ew, eo, KeyPageRounds.roundBytes_tail] at h'
  exact h'

/-- The seeds' chain's first typed query, at the block of its tail, has `Fmt.oStr` of that chain's
first value, with the root and the pins' fixed bytes as the statement. For fixed bytes of fewer
than 2 ^ 32. -/
theorem implE_seedFirst (cm : Dig 256) (hr : P.rest.size < 2 ^ 32) :
    (implE P dd K V back).code (.fb .test) (q0S (L := Le D early e) .test D.C e _ id [cm])
        (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 _root_.Fmt.recordLabel _root_.Fmt.zero32
        (_root_.Fmt.firstBytes _root_.Fmt.zero32 (digToBytes cm ++ P.rest) ByteArray.empty
          none)) := by
  refine implE_test P dd K V back _ _ _ ?_
  rw [fbSeeds_at0 P K _ rfl]
  refine tailP_some _ K _ _ ?_
  have h := FirstName.firstPN_put P.rest (Le D early e) .test
    (p0S (L := Le D early e) .test D.C e _ id) (isEq _) FirstName.zeroPd (isEq_iff _)
    _root_.Fmt.recordLabel cm hr
  rw [FirstName.zeroPd_bytes] at h
  exact h

/-- The seeds' chain's drawing round's typed query, at every block, has `Fmt.oStr` of one half of
a hash under 162 on the seeds' chain: round 1, the chain value as the start, no message, the kind
"seeds", no work, the nonce 0. For a chain value of 256 bits and K below 2 ^ 48. -/
theorem implE_seedRound (hK : K < 2 ^ 48) (ρ : Bits) (hρ : ρ.length = 256) (j : Fin (K + 1)) :
    (implE P dd K V back).code (.fb .test) (q1S (L := Le D early e) .test D.C e _ id ρ) j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (blockNo 0 K j % 2)) 162
        _root_.Fmt.recordLabel 1 (bitsToBytes ρ)
        (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 (blockNo 0 K j / 2))) := by
  refine implE_test P dd K V back _ _ _ ?_
  rw [fbSeeds_else P K _ (by show (1 : ℕ) ≠ 0; decide)]
  exact SeedRound.secondPS_put _ _ _ _ _ K hK ρ hρ j

end TypedOracleCompiler.Run.EntryPage
