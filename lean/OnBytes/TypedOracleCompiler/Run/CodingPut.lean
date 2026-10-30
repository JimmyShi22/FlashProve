-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingPut.lean.
Run/CodingPut.lean: THE TWO TIES BETWEEN THE PARTIAL CODES AND THE FUNCTIONS: WHAT THE CODE OF A
ROUND'S CHAIN QUERY WRITES, AND WHAT THE CODE OF A LEAF QUERY WRITES, IS THE BIT STRING OF THE
FORMAT'S STRING OF THE CALL TO WHICH THE FUNCTIONS SEND THAT QUERY. Theorems and proofs. The format
page (FORMAT.md, which comes with the programs, that is, with the C++ implementation that
accompanies this Lean code), rules R2.2, R2.4, R3.1, R5.2, R7.3. The
statements speak of the definitions of Fmt/ as they stand (for the page's sections 2 and 3 that is
Fmt/Rules23.lean). This file has not been held against the page as it ships, and may differ from
it, for instance at R2.2, R2.4, R3.1 and R7.3.

TWO DESCRIPTIONS OF ONE MAP stand in this folder. Run/CodingFn.lean: functions from a typed query
(and the number of a block of its answer) to a hash call of the format (fbCall, leafCall; strOf: the
call's string): by them the verifier is run over a function on the format's strings (famOf).
Run/CodingPage162.lean, Run/CodingPage164.lean: partial codes with put, parse and both laws (p162,
pLeaf): of them the encoding of the queries into a SINGLE oracle is made. For a node and for the
chain's first value the tie is proved where the codes stand (pNode_put, pFirst0_put). HERE THE OTHER
TWO.
    ChainFit C D     (at any tag; the default is "test") THE HYPOTHESIS OF FIT between the code's
                     data (C : ChainD) and the functions' data (D : PageD): the same label, kinds,
                     bits of work; what C.rc i writes for (root or none, plain part) is the bits of
                     D.msg i .. and then the 64 bits of the word of D.nonce i ..
    p162_put         0 < K, ChainFit C D: whenever p162 C K writes s for (q, j): fbCall D K q j is
                     some call c, and s = the bits of strOf c
    pLeaf_put        the file's salt has a whole number of bytes (n = 8 k); what p writes for a
                     symbol with its position is the bits of the leaf's label and then of the column
                     with its fill, by D.leaf: whenever pLeaf n p writes s for q: leafCall D q is
                     some call c, and s = the bits of strOf c
    blockNo_eq       the two numberings of the blocks of a chain answer (blockNo: a number; blockTo:
                     a permutation) are one, IF 0 < K OR THE ROUND HAS NO WORK
    oStr64_bits          the bits of the string of a call of a round's query: the half's byte, 32
                         bytes, the start, the word of number and label, the word of the round, the
                         bytes
    PCode.ins_put, pWord_put_eq, pBits_put_eq, pKwc_put_eq, bits_one, half_bits what the combinators
    write
WHERE THE TWO NUMBERINGS PART: K = 0 WITH WORK. An answer without any block of verifier message, in
a round with work: blockNo sends the chain value to block 1, blockTo (a permutation of one point) to
block 0. The wiring with tests has a block for the test bits in front, so K is at least 1 wherever a
round has work: hence the premise 0 < K.
WHAT IS NOT SAID. That the two hypotheses of fit hold at a given protocol: data of the toy. The
converse (that the code writes wherever the functions give a call): it does not hold: the functions
test no lengths. Anything on the single oracle.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPut
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage162
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingImpl
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
import OnBytes.TypedOracleCompiler.Run.CodingPage
import OnBytes.TypedOracleCompiler.Run.CodingFn
import Run.CodingFnTag

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol
open _root_.Run

namespace PCode
variable {A B : Type}

end PCode

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {tg : Tag}

/-- The data of the partial code and the data of the functions fit. -/
structure ChainFit (C : ChainD L tg) (D : PageD L tg) : Prop where
  label : C.label = D.label
  kind  : ∀ i, C.kind i = D.kind i
  work  : ∀ i, C.work i = D.work i
  rc    : ∀ i rt pl s, (C.rc i).put (rt, pl) = some s →
    s = bytesToBits (D.msg i (rt.map digToBytes) pl) ++ bytesToBits (_root_.Fmt.u64n (D.nonce i pl))

/-- THE TIE FOR A ROUND'S QUERY: WHAT THE PARTIAL CODE WRITES IS THE FORMAT'S STRING OF THE CALL. -/
theorem p162_put (C : ChainD L tg) (D : PageD L tg) (K : ℕ) (hK : 0 < K) (F : ChainFit C D)
    (x : FbIn 256 L tg × Fin (K + 1)) (s : List Bool) (h : (p162 C K).put x = some s) :
    ∃ c, fbCall D K x.1 x.2 = some c ∧ s = bytesToBits (strOf c) := by
  obtain ⟨t, ht, hs⟩ := PCode.pull_put _ _ _ _ _ x s h
  obtain ⟨⟨round, head, rt, plain⟩, j⟩ := x
  cases round with
  | zero => cases ht
  | succ i =>
      cases head with
      | f2 xl ρ =>
          cases xl with
          | some _ => cases ht
          | none =>
              rw [← Option.some.inj ht] at hs
              obtain ⟨u, v, hu, hv, rfl⟩ := PCode.cons_put _ _ _ _ _ s hs
              obtain ⟨v1, hv1, rfl⟩ := PCode.pre_put' _ _ _ v hv
              obtain ⟨u2, v2, hu2, hv2, rfl⟩ := PCode.cons_put _ _ _ _ _ v1 hv1
              obtain ⟨v3, hv3, rfl⟩ := PCode.pre_put' _ _ _ v2 hv2
              obtain ⟨u4, v4, hu4, hv4, rfl⟩ := PCode.cons_put _ _ _ _ _ v3 hv3
              obtain ⟨s0, w0, hs0, hw0, rfl⟩ := PCode.ins_put _ _ _ _ _ _ _ v4 hv4
              obtain ⟨e2, hρ⟩ := pBits_put_eq 256 _ u2 hu2
              simp only at e2 hρ
              have e4 := pWord_put_eq _ u4 hu4
              have ew := pKwc_put_eq _ _ _ w0 hw0
              have e0 := F.rc _ _ _ s0 hs0
              have eu : u =
                  bitsOfByte
                    (if decide ((blockTo (decide (C.work (i + 1) ≠ 0)) K j).val % 2 = 1) = true then
                        1
                      else 0) :=
                (Option.some.inj hu).symm
              simp only at e4 ew e0
              have hb : blockNo (D.work (i + 1)) K j =
                  (blockTo (decide (C.work (i + 1) ≠ 0)) K j).val := by
                rw [F.work]
                exact blockNo_eq _ K j (Or.inl hK)
              have hl : (bytesToBits (_root_.Fmt.u64n (D.nonce (i + 1) plain))).length = 64 := by
                rw [length_bytesToBits]
                rfl
              have hlen : s0.length - 64 =
                  (bytesToBits (D.msg (i + 1) (rt.map digToBytes) plain)).length := by
                rw [e0, List.length_append, hl]
                omega
              refine ⟨_, rfl, ?_⟩
              show _ = bytesToBits
                  (_root_.Fmt.oStr _ 162 D.label (i + 1) (bitsToBytes ρ) (roundBytes _ _ _ _ _))
              rw [oStr64_bits _ _ _ _ _ (size_bitsToBytes ρ 32 hρ),
                bytesToBits_bitsToBytes ρ ((whole_iff ρ).2 ⟨32, hρ⟩), hb, ← half_bits,
                ← eu, ← F.label, ← e4, ← e2]
              unfold roundBytes
              rw [bytesToBits_append, bytesToBits_append, ← F.kind, ← F.work, ← ew, hlen, e0,
                List.take_left' rfl, List.drop_left' rfl, List.append_assoc]
      | f1 _ _ _ => cases ht
      | f3 _ _ => cases ht
      | f4 _ _ => cases ht
      | f5 _ => cases ht

/-- THE TIE FOR A LEAF. TWO: over bodies. The hypothesis fit here also says that D.leaf SPELLS every
body that the code p writes (in the library D.leaf is total on the symbols under the page's tag, and
leafCall_self gives the call). -/
theorem pLeaf_put (D : PageD L tg) (n k : ℕ) (hn : n = 8 * k) (p : PCode L.Bd)
    (fit : ∀ y m, p.put y = some m → ∃ z, D.leaf y = some z ∧
      m = bytesToBits (_root_.Fmt.label 164 z.1 z.2.1) ++ bytesToBits z.2.2)
    (q : LeafIn L) (s : List Bool) (h : (pLeaf n p).put q = some s) :
    ∃ c, leafCall D q = some c ∧ s = bytesToBits (strOf c) := by
  obtain ⟨y, sa⟩ := q
  have h1 : (if sa.length = 256 + n then
          (p.put y).map (fun m => pre33 ++ (sa.take 256 ++ (m ++ sa.drop 256)))
        else none) = some s := h
  by_cases hl : sa.length = 256 + n
  · rw [if_pos hl] at h1
    cases hm : p.put y with
    | none => rw [hm] at h1; cases h1
    | some m =>
        rw [hm] at h1
        have es : s = pre33 ++ (sa.take 256 ++ (m ++ sa.drop 256)) := (Option.some.inj h1).symm
        have e1 : (sa.take 256).length = 8 * 32 := by rw [List.length_take, hl]; omega
        have e2 : (sa.drop 256).length = 8 * k := by rw [List.length_drop, hl]; omega
        obtain ⟨z, hz, hfit⟩ := fit y m hm
        refine ⟨⟨0, 164, z.1, z.2.1, bitsToBytes (sa.take 256), z.2.2 ++ bitsToBytes (sa.drop 256)⟩,
          ?_, ?_⟩
        · show (D.leaf y).map _ = _
          rw [hz]
          rfl
        · show s = bytesToBits
              (_root_.Fmt.oStr 0 164 z.1 z.2.1 (bitsToBytes (sa.take 256))
                (z.2.2 ++ bitsToBytes (sa.drop 256)))
          rw [oStr32_bits _ _ _ _ _ (by decide) (size_bitsToBytes _ 32 e1),
            bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, e1⟩),
            bytesToBits_append, bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨k, e2⟩),
            es, hfit, List.append_assoc]
  · rw [if_neg hl] at h1
    cases h1

end TypedOracleCompiler.Run
