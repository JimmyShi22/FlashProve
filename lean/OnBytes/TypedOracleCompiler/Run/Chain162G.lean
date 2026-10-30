-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/Chain162G.lean: one partial code for the later-round queries of a typed chain that
is SEVERAL chains of a file: a typed query with the number of a block of its answer, as the string
of one half of a hash under the number 162, with the chain's label, the round's index and the order
of the blocks as functions of the typed round.

The sibling (a second form of the library's soundness road, under OnBytes/TypedOracleCompiler/) has such a
code for one chain: `p162` (OnBytes/TypedOracleCompiler/Run/CodingPage162.lean): one label; the typed round is the
format's index; the typed tail of an answer is block 0 of the format's row, or block 1 where the
round has proof of work. A key file or a proof file is typed as one chain that runs through several
chains of the file. There the label and the index hang on the typed round. And at a round in which a
chain is sealed the seal, block 1 of the row, has to be the typed tail, since the next typed query
holds the tail and the next hash input holds the seal, while the round has no work. (Words: a hash
under 162 gives 64 bytes, two blocks of 32: its two halves; a round's row is the blocks of all its
calls, counted from 0; the typed tail is the last of an answer's K + 1 typed blocks, the chain's
next value.)

The data, `ChainG L tg`: `on i`: whether the code writes at the typed round i; `lab i`, `idx i`:
label and index; `back`: the typed round of a label and an index, with one law (by which no two
rounds that are on share label and index); `ord i`: the order of blocks, by the library's `blockTo`
(false: tail to block 0, typed block k to k + 1; true: the library's order with work: tail to block
1, typed block 0 to 0, every other k to k + 1; at K = 0 the one block stays); `kind i`, `work i`:
the numbers in the word behind the message; `rc i`: a partial code of (roots, plain part) that
writes the message and then the nonce's word; `mkH`, `selH`: how the chain value stands in the
query's head, with both laws.
 - `pLab`: the word 162 + 65536 · label, as a code of the label;
 - `pTupG`, `toTupG`, `ofTupG`, with both laws; `p162G D K : PCode (FbIn 256 L tg × Fin (K + 1))`;
 - `p162G_put`: AN EQUATION: where `on i`, the chain value has 256 bits, the label is below 2 ^ 48,
   the index below 2 ^ 64, kind and work below 256, K below 2 ^ 48, and `rc i` writes m ++ w with w
   of 64 bits: at (⟨i, mkH ρ, rt, pl⟩, j) the code writes the half's byte, 32 fixed bytes, ρ, the
   label's word, the index's word, m, the word of kind, work and call, w;
 - `p162G_str`: if m and w are the bits of a message's bytes and of a nonce's word, that is the bits
   of the format's string `Fmt.oStr` of half (b mod 2), the number 162, `lab i`, `idx i`, ρ's bytes
   as the start, on the library's `roundBytes` of message, kind, work, call (b div 2) and nonce; b
   is the block's number in the row;
 - `p162G_shape`: every string that it writes: the half's byte, the 32 bytes, 256 bits, the label's
   word and the index's word of the query's round, a rest;
 - `p162G_only`: whatever it writes, it writes at a query whose round is on and whose head is
   `mkH ρ`.

Main definitions: `ChainG`, `pLab`, `pTupG`, `toTupG`, `ofTupG`, `p162G`.
Main theorems: `ofTupG_toTupG`, `toTupG_ofTupG`, `p162G_put`, `p162G_str`, `p162G_shape`,
`p162G_only`.

Not claimed. A CODE, NO PAGE: that its strings are apart from other codes' is not said. No data are
given: which rounds, labels, orders. That `ord` is the format's order at any round is not asked: any
choice gives a lawful code. WHAT `ord i = true` COSTS AT A ROUND WITHOUT WORK: typed block 0, the
first block of the typed verifier's message, is then block 0 of the row, which in the format is the
chain's next value and no part of the verifier's message. The typed message of that round is not the
format's: the digest that a sealed round draws on the typed side is not the seal. Whoever uses this
order owes that the decision does not read it. Not shown here. A sealed round WITH work has its seal
at block 2 of the row; neither order sends the tail there: this code does not serve such a plan.
`Fmt.oStr` is total. That a call lies in the format's domain is not asked: an index from 1 to 2 ^ 63
− 1, a message of whole words, at most 64 bits of work, a nonce that is a word and 0 without work
(library, Fmt/Rules23.lean: `hDom`; Fmt/Rules5.lean: `askOK`). Whoever ties these strings to the
format's hash asks them. `mkH` does not hang on the round: a round whose head holds a late instance
has no string. That the sibling's `p162` is an instance is not shown. That any program hashes these
strings. Nothing on any hash. Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.CodingPut
import OnBytes.TypedOracleCompiler.Run.PutSome

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Chain162G
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PutSome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## The label's word -/

/-- The word of the number 162 and a label. -/
def labTo (l : ℕ) : Option ℕ := some (162 + 65536 * l)

/-- The label, of such a word. -/
def labOf (w : ℕ) : Option ℕ := if w % 65536 = 162 then some (w / 65536) else none

/-- The reading undoes the writing. -/
theorem labOf_labTo (l w : ℕ) (h : labTo l = some w) : labOf w = some l := by
  have e : 162 + 65536 * l = w := Option.some.inj h
  unfold labOf
  rw [← e, if_pos (by omega)]
  exact congrArg some (by omega)

/-- The writing undoes the reading. -/
theorem labTo_labOf (w l : ℕ) (h : labOf w = some l) : labTo l = some w := by
  unfold labOf at h
  by_cases hc : w % 65536 = 162
  · rw [if_pos hc] at h
    have e : w / 65536 = l := Option.some.inj h
    unfold labTo
    exact congrArg some (by omega)
  · rw [if_neg hc] at h
    cases h

/-- The word 162 + 65536 · label, as a code of the label. -/
def pLab : PCode ℕ := pWord.pull labTo labOf labOf_labTo labTo_labOf

/-- It writes 64 bits. -/
theorem pLab_len : pLab.Len 64 := PCode.pull_len _ _ _ _ _ 64 pWord_len

/-- What it writes, for a label below 2 ^ 48. -/
theorem pLab_some (l : ℕ) (hl : l < 2 ^ 48) :
    pLab.put l = some (bytesToBits (_root_.Fmt.u64n (162 + 65536 * l))) :=
  pull_some _ _ _ _ _ l _ _ rfl (if_pos (by omega))

/-- Whatever it writes is that word's bits. -/
theorem pLab_put_eq (l : ℕ) (s : List Bool) (h : pLab.put l = some s) :
    s = bytesToBits (_root_.Fmt.u64n (162 + 65536 * l)) := by
  obtain ⟨v, hv, hs⟩ := PCode.pull_put _ _ _ _ _ l s h
  rw [← Option.some.inj hv] at hs
  exact pWord_put_eq _ s hs

/-! ## The data -/

variable {I X : Type}

/-- The data of a typed chain that runs through several chains of a file. -/
structure ChainG (L : BatchProtocolWithLeafBody I X) (tg : Tag) where
  /-- whether the code writes at the typed round i -/
  on : ℕ → Bool
  /-- the label of the file's chain in which the typed round i lies -/
  lab : ℕ → ℕ
  /-- the round's index in that chain -/
  idx : ℕ → ℕ
  /-- the typed round of a label and an index -/
  back : ℕ → ℕ → Option ℕ
  /-- `back l j` is the round that is on with this label and index, and none if there is none; so no
  two rounds that are on share label and index -/
  hback : ∀ l j i, back l j = some i ↔ (on i = true ∧ lab i = l ∧ idx i = j)
  /-- the order of an answer's blocks, by the library's `blockTo`: false: the typed tail is block 0
  of the row; true, for K ≥ 1: block 1 (at K = 0 there is one block, and it stays block 0) -/
  ord : ℕ → Bool
  /-- the kind's number in the word behind the message -/
  kind : ℕ → ℕ
  /-- the bits of work in that word -/
  work : ℕ → ℕ
  /-- the code of (roots, plain part): the message, then the nonce's word -/
  rc : ℕ → PCode (List (Dig 256) × PlainPart (shapeOf L tg) (annOf L tg))
  /-- its strings have at least 64 bits: room for the nonce's word -/
  hrc : ∀ i y s, (rc i).put y = some s → 64 ≤ s.length
  /-- the head that holds the chain value ρ -/
  mkH : Bits → Head 256 X
  /-- the chain value of such a head -/
  selH : Head 256 X → Option Bits
  /-- reading undoes making -/
  hsel : ∀ ρ, selH (mkH ρ) = some ρ
  /-- making undoes reading -/
  hmk : ∀ h ρ, selH h = some ρ → mkH ρ = h

variable {L : BatchProtocolWithLeafBody I X} {tg : Tag}

/-- The tuple: half, chain value, label, index, ((roots, plain part), number of the call). -/
abbrev TupG (L : BatchProtocolWithLeafBody I X) (tg : Tag) : Type :=
  Bool × (List Bool × (ℕ × (ℕ × ((List (Dig 256) × PlainPart (shapeOf L tg) (annOf L tg)) × ℕ))))

/-- The code of what stands behind label and index. -/
def pRest (D : ChainG L tg) (l j : ℕ) :
    PCode ((List (Dig 256) × PlainPart (shapeOf L tg) (annOf L tg)) × ℕ) :=
  match D.back l j with
  | some i => (D.rc i).ins (pKwc (D.kind i) (D.work i)) 64 64 (pKwc_len _ _) (D.hrc i)
  | none => PCode.empty _

/-- The code of the tuple. -/
def pTupG (D : ChainG L tg) : PCode (TupG L tg) :=
  pHalf.cons 8 pHalf_len fun _ =>
    PCode.pre mid32
      ((pBits 256).cons 256 (pBits_len 256) fun _ =>
        pLab.cons 64 pLab_len fun l =>
          pWord.cons 64 pWord_len fun j => pRest D l j)

/-- A typed point as a tuple. -/
def toTupG (D : ChainG L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) : Option (TupG L tg) :=
  match D.selH x.1.head with
  | some ρ =>
      if D.on x.1.round = true then
        some (decide ((blockTo (D.ord x.1.round) K x.2).val % 2 = 1), ρ, D.lab x.1.round,
          D.idx x.1.round, ((x.1.rt, x.1.plain), (blockTo (D.ord x.1.round) K x.2).val / 2))
      else none
  | none => none

/-- And back. -/
def ofTupG (D : ChainG L tg) (K : ℕ) (t : TupG L tg) : Option (FbIn 256 L tg × Fin (K + 1)) :=
  match D.back t.2.2.1 t.2.2.2.1 with
  | some i =>
      if hb : 2 * t.2.2.2.2.2 + (if t.1 then 1 else 0) < K + 1 then
        some (⟨i, D.mkH t.2.1, t.2.2.2.2.1.1, t.2.2.2.2.1.2⟩,
          blockOf (D.ord i) K ⟨2 * t.2.2.2.2.2 + (if t.1 then 1 else 0), hb⟩)
      else none
  | none => none

/-- A number from its half and its parity. -/
theorem half_parity (b : ℕ) : 2 * (b / 2) + (if decide (b % 2 = 1) = true then 1 else 0) = b := by
  by_cases h2 : b % 2 = 1
  · rw [if_pos (decide_eq_true h2)]; omega
  · rw [if_neg (by simpa using h2)]; omega

/-- The way back undoes the way there. -/
theorem ofTupG_toTupG (D : ChainG L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1))
    (t : TupG L tg) (h : toTupG D K x = some t) : ofTupG D K t = some x := by
  obtain ⟨⟨round, head, rt, plain⟩, j⟩ := x
  unfold toTupG at h
  dsimp only at h
  cases hs : D.selH head with
  | none => rw [hs] at h; cases h
  | some ρ =>
    rw [hs] at h
    dsimp only at h
    by_cases ho : D.on round = true
    · rw [if_pos ho] at h
      rw [← Option.some.inj h]
      have hbk : D.back (D.lab round) (D.idx round) = some round :=
        (D.hback _ _ _).2 ⟨ho, rfl, rfl⟩
      have hb := (blockTo (D.ord round) K j).isLt
      have e := half_parity (blockTo (D.ord round) K j).val
      unfold ofTupG
      dsimp only
      rw [hbk]
      dsimp only
      rw [dif_pos (by rw [e]; exact hb)]
      have e' : (⟨2 * ((blockTo (D.ord round) K j).val / 2) +
            (if decide ((blockTo (D.ord round) K j).val % 2 = 1) = true then 1 else 0),
          by rw [e]; exact hb⟩ : Fin (K + 1)) = blockTo (D.ord round) K j := Fin.ext e
      rw [e', blockOf_blockTo, D.hmk head ρ hs]
    · rw [if_neg ho] at h
      cases h

/-- The way there undoes the way back. -/
theorem toTupG_ofTupG (D : ChainG L tg) (K : ℕ) (t : TupG L tg)
    (x : FbIn 256 L tg × Fin (K + 1)) (h : ofTupG D K t = some x) : toTupG D K x = some t := by
  obtain ⟨hf, ρ, l, j, ⟨rt, pl⟩, c⟩ := t
  unfold ofTupG at h
  dsimp only at h
  cases hbk : D.back l j with
  | none => rw [hbk] at h; cases h
  | some i =>
    rw [hbk] at h
    dsimp only at h
    obtain ⟨ho, hl, hj⟩ := (D.hback _ _ _).1 hbk
    by_cases hb : 2 * c + (if hf then 1 else 0) < K + 1
    · rw [dif_pos hb] at h
      rw [← Option.some.inj h]
      unfold toTupG
      dsimp only
      rw [D.hsel ρ]
      dsimp only
      rw [if_pos ho, blockTo_blockOf, hl, hj]
      cases hf
      · have e1 : (2 * c + 0) % 2 ≠ 1 := by omega
        have e2 : (2 * c + 0) / 2 = c := by omega
        show some (decide ((2 * c + 0) % 2 = 1), ρ, l, j, ((rt, pl), (2 * c + 0) / 2)) = _
        rw [decide_eq_false e1, e2]
      · have e1 : (2 * c + 1) % 2 = 1 := by omega
        have e2 : (2 * c + 1) / 2 = c := by omega
        show some (decide ((2 * c + 1) % 2 = 1), ρ, l, j, ((rt, pl), (2 * c + 1) / 2)) = _
        rw [decide_eq_true e1, e2]
    · rw [dif_neg hb] at h
      cases h

/-- A later-round query of the typed chain, with the number of a block of its answer. -/
def p162G (D : ChainG L tg) (K : ℕ) : PCode (FbIn 256 L tg × Fin (K + 1)) :=
  (pTupG D).pull (toTupG D K) (ofTupG D K) (ofTupG_toTupG D K) (toTupG_ofTupG D K)

/-- What it writes, as an equation: the half's byte, 32 fixed bytes, the chain value, the
label's word, the index's word, the message, the word of kind, work and call, the nonce's word. b is
the block's number in the row. -/
theorem p162G_put (D : ChainG L tg) (K : ℕ) (hK : K < 2 ^ 48) (i : ℕ) (ho : D.on i = true)
    (hl : D.lab i < 2 ^ 48) (hi : D.idx i < 2 ^ 64) (hk : D.kind i < 256) (hw : D.work i < 256)
    (ρ : List Bool) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (pl : PlainPart (shapeOf L tg) (annOf L tg)) (m w : List Bool) (hlen : w.length = 64)
    (hr : (D.rc i).put (rt, pl) = some (m ++ w)) (j : Fin (K + 1)) :
    (p162G D K).put (⟨i, D.mkH ρ, rt, pl⟩, j) =
      some (bitsOfByte (if decide ((blockTo (D.ord i) K j).val % 2 = 1) = true then 1 else 0) ++
        (mid32 ++ (ρ ++ (bytesToBits (_root_.Fmt.u64n (162 + 65536 * D.lab i)) ++
          (bytesToBits (_root_.Fmt.u64n (D.idx i)) ++
            (m ++ (bytesToBits (_root_.Fmt.u64n (D.kind i + 256 * D.work i +
              65536 * ((blockTo (D.ord i) K j).val / 2))) ++ w))))))) := by
  have hb := (blockTo (D.ord i) K j).isLt
  have ht : toTupG D K ((⟨i, D.mkH ρ, rt, pl⟩ : FbIn 256 L tg), j) =
      some (decide ((blockTo (D.ord i) K j).val % 2 = 1), ρ, D.lab i, D.idx i,
        ((rt, pl), (blockTo (D.ord i) K j).val / 2)) := by
    unfold toTupG
    dsimp only
    rw [D.hsel ρ]
    dsimp only
    rw [if_pos ho]
  have hkw : (pKwc (D.kind i) (D.work i)).put ((blockTo (D.ord i) K j).val / 2) =
      some (bytesToBits (_root_.Fmt.u64n (D.kind i + 256 * D.work i +
        65536 * ((blockTo (D.ord i) K j).val / 2)))) := by
    refine pull_some _ _ _ _ _ _ (D.kind i + 256 * D.work i +
      65536 * ((blockTo (D.ord i) K j).val / 2)) _ ?_ (if_pos (by omega))
    unfold kwcTo
    rw [if_pos ⟨hk, hw, by omega⟩]
  have h6 := ins_some (D.rc i) (pKwc (D.kind i) (D.work i)) 64 64 (pKwc_len _ _) (D.hrc i)
    (rt, pl) ((blockTo (D.ord i) K j).val / 2) _ _ hr hkw
  have e6 : (m ++ w).take ((m ++ w).length - 64) = m := by
    rw [List.length_append, hlen, Nat.add_sub_cancel]
    exact List.take_left' rfl
  have e7 : (m ++ w).drop ((m ++ w).length - 64) = w := by
    rw [List.length_append, hlen, Nat.add_sub_cancel]
    exact List.drop_left' rfl
  rw [e6, e7] at h6
  have h5 : (pRest D (D.lab i) (D.idx i)).put ((rt, pl), (blockTo (D.ord i) K j).val / 2) =
      some (m ++ (bytesToBits (_root_.Fmt.u64n (D.kind i + 256 * D.work i +
        65536 * ((blockTo (D.ord i) K j).val / 2))) ++ w)) := by
    unfold pRest
    rw [(D.hback _ _ _).2 ⟨ho, rfl, rfl⟩]
    exact h6
  have hwi : pWord.put (D.idx i) = some (bytesToBits (_root_.Fmt.u64n (D.idx i))) := if_pos hi
  have h4 := cons_some pWord 64 pWord_len (fun j' => pRest D (D.lab i) j') (D.idx i) _ _ _ hwi h5
  have h3 := cons_some pLab 64 pLab_len
    (fun l => pWord.cons 64 pWord_len fun j' => pRest D l j') (D.lab i) _ _ _
    (pLab_some _ hl) h4
  have h2 := cons_some (pBits 256) 256 (pBits_len 256)
    (fun _ => pLab.cons 64 pLab_len fun l => pWord.cons 64 pWord_len fun j' => pRest D l j') ρ _ _ _
    (if_pos hρ : (pBits 256).put ρ = some ρ) h3
  have h1 := pre_some mid32 _ _ _ h2
  have h0 := cons_some pHalf 8 pHalf_len (fun _ => PCode.pre mid32 _)
    (decide ((blockTo (D.ord i) K j).val % 2 = 1)) _ _ _ rfl h1
  exact pull_some _ _ _ _ _ _ _ _ ht h0

/-- That is `Fmt.oStr` of the round's call, if the message's and the nonce's bits are those of
bytes and of a word: half (b mod 2) of call (b div 2) of the round, a hash under the number 162,
with the round's label and index, the chain value as the start. -/
theorem p162G_str (D : ChainG L tg) (K : ℕ) (hK : K < 2 ^ 48) (i : ℕ) (ho : D.on i = true)
    (hl : D.lab i < 2 ^ 48) (hi : D.idx i < 2 ^ 64) (hk : D.kind i < 256) (hw : D.work i < 256)
    (ρ : List Bool) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (pl : PlainPart (shapeOf L tg) (annOf L tg)) (msg : ByteArray) (nonce : ℕ)
    (hr : (D.rc i).put (rt, pl) =
      some (bytesToBits msg ++ bytesToBits (_root_.Fmt.u64n nonce))) (j : Fin (K + 1)) :
    (p162G D K).put (⟨i, D.mkH ρ, rt, pl⟩, j) =
      some (bytesToBits (_root_.Fmt.oStr (UInt8.ofNat ((blockTo (D.ord i) K j).val % 2)) 162
        (D.lab i) (D.idx i) (bitsToBytes ρ)
        (roundBytes msg (D.kind i) (D.work i) ((blockTo (D.ord i) K j).val / 2) nonce))) := by
  rw [p162G_put D K hK i ho hl hi hk hw ρ hρ rt pl _ _
    (by rw [length_bytesToBits]; rfl) hr j,
    oStr64_bits _ _ _ _ _ (size_bitsToBytes ρ 32 hρ),
    bytesToBits_bitsToBytes ρ ((whole_iff ρ).2 ⟨32, hρ⟩), ← half_bits]
  unfold roundBytes
  rw [bytesToBits_append, bytesToBits_append, List.append_assoc]

/-- Whatever it writes, it writes at a query whose round is on and whose head holds a chain
value. -/
theorem p162G_only (D : ChainG L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) (s : List Bool)
    (h : (p162G D K).put x = some s) : D.on x.1.round = true ∧ ∃ ρ, x.1.head = D.mkH ρ := by
  obtain ⟨t, ht, -⟩ := PCode.pull_put _ _ _ _ _ x s h
  unfold toTupG at ht
  cases hs : D.selH x.1.head with
  | none => rw [hs] at ht; cases ht
  | some ρ =>
    rw [hs] at ht
    dsimp only at ht
    by_cases ho : D.on x.1.round = true
    · exact ⟨ho, ρ, (D.hmk _ _ hs).symm⟩
    · rw [if_neg ho] at ht
      cases ht

/-- The shape of every string that it writes: the half's byte, the 32 fixed bytes, 256 bits, the
label's word and the index's word of the query's round, a rest. -/
theorem p162G_shape (D : ChainG L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) (s : List Bool)
    (h : (p162G D K).put x = some s) :
    ∃ (hb : Bool) (ρ r : List Bool), ρ.length = 256 ∧
      s = bitsOfByte (if hb then 1 else 0) ++ (mid32 ++ (ρ ++
        (bytesToBits (_root_.Fmt.u64n (162 + 65536 * D.lab x.1.round)) ++
          (bytesToBits (_root_.Fmt.u64n (D.idx x.1.round)) ++ r)))) := by
  obtain ⟨t, ht, hs⟩ := PCode.pull_put _ _ _ _ _ x s h
  have hlab : t.2.2.1 = D.lab x.1.round ∧ t.2.2.2.1 = D.idx x.1.round := by
    unfold toTupG at ht
    cases hsel : D.selH x.1.head with
    | none => rw [hsel] at ht; cases ht
    | some ρ =>
      rw [hsel] at ht
      dsimp only at ht
      by_cases ho : D.on x.1.round = true
      · rw [if_pos ho] at ht
        rw [← Option.some.inj ht]
        exact ⟨rfl, rfl⟩
      · rw [if_neg ho] at ht
        cases ht
  obtain ⟨u, v, hu, hv, rfl⟩ := PCode.cons_put _ _ _ _ t s hs
  obtain ⟨v1, hv1, rfl⟩ := PCode.pre_put' _ _ _ v hv
  obtain ⟨u2, v2, hu2, hv2, rfl⟩ := PCode.cons_put _ _ _ _ t.2 v1 hv1
  obtain ⟨u3, v3, hu3, hv3, rfl⟩ := PCode.cons_put _ _ _ _ t.2.2 v2 hv2
  obtain ⟨u4, v4, hu4, -, rfl⟩ := PCode.cons_put _ _ _ _ t.2.2.2 v3 hv3
  refine ⟨t.1, u2, v4, pBits_len 256 _ _ hu2, ?_⟩
  rw [← Option.some.inj hu, pLab_put_eq _ u3 hu3, pWord_put_eq _ u4 hu4, hlab.1, hlab.2]

end TypedOracleCompiler.Run.Chain162G
