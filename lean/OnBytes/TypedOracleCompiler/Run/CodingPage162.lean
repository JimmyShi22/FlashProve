-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingPage162.lean.
Run/CodingPage162.lean: THE PARTIAL CODE OF A CHAIN QUERY WITH THE NUMBER OF A BLOCK OF ITS ANSWER,
FOR THE ROUNDS 1, 2, .., IN THE PROGRAMS' FORMAT. Definitions that compute, with their laws. After
the format page's rules R2.2, R2.4 (the oracle's strings), R5.2 (call j of round i), R5.4 (the row
of blocks), in which THE CHAIN'S LABEL STANDS IN THE TREE'S PLACE of the call's label (not held
against the page as it ships); and after a convention of this library that
THE ORDER OF A CHAIN ANSWER'S BLOCKS IS DATA OF THE ENCODING OF THE QUERIES (Run/CodingImpl.lean:
blockTo, blockOf).
THE STRING of block b of round i:   the half b mod 2 (one byte); digest length 64, key length,
                                    fanout, depth, 28 zero bytes; the chain's value before the round
                                    (32 bytes); the word (the rounds' number) + 2^16 (the chain's
                                    label); the word i; the prover's message; the word kind + 2^8 w
                                    + 2^16 (b div 2); the word of the nonce.
THE DATA (ChainD L t; THE PROTOCOL'S TAG t IS A PARAMETER; where none is written it is "test"):
label: the chain's; kind i, work i: by the plan; rc i : A PARTIAL CODE OF (root or none, typed plain
part) AT ROUND i, which writes THE PROVER'S MESSAGE AND THEN THE 64 BITS OF THE NONCE's WORD (the
nonce is a component of the typed plain part; 0 where the round has no work). A round that the plan
does not have: rc i writes nothing.
   pHalf, pKwc kind w   the half as a byte; the number of a call in its word, beside the round's
                        kind and work
   pTup D               the code of the tuple (half, chain value, round, ((root, plain part), number
                        of the call))
   toTup, ofTup         a typed point (query, block) as such a tuple, and back: a query of a round i
                        + 1 whose head is the later-round format with no late field; block j of the
                        typed answer is block (blockTo ..) of the format's row
   p162 D K : PCode (FbIn 256 L tg × Fin (K + 1))
   p162_shape, p162_head      every string that it writes: the half's byte, the 32 bytes, 256 bits,
                              the word of the rounds' number and the label, a rest; so it begins
                              with the byte 0 or the byte 1
NOT ASKED HERE: that the chain's label is below 2^48 and the round below 2^63, as the format's rule
R2.3 wants. The code is a code all the same: the label enters as ONE CONSTANT WORD, and a round is
any number below 2^64. BUT a label of 2^48 or more does not fit its word, which holds the number
modulo 2^64: the string is then that of another label; and a round from 2^63 on gives a string that
is none of the format's. Whoever ties these strings to the format's hash must ask both bounds.
WHAT IS NOT SAID. Which rc: it is data of the toy protocol. Round 0 (the chain's first value) is
another file's. That what is written is the string of the functions of Run/CodingFn.lean is proved
in Run/CodingPut.lean (p162_put), not here.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPage162
import Run.CodingSeq
import OnBytes.TypedOracleCompiler.Run.CodingImpl

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol
open _root_.Run

namespace PCode
variable {A B : Type}

end PCode

variable {I X : Type}

/-- The data. -/
structure ChainD (L : BatchProtocolWithLeafBody I X) (t : Tag := .test) where
  /-- the chain's label: it stands in the tree's place of the label of a round's call -/
  label : ℕ
  kind : ℕ → ℕ
  work : ℕ → ℕ
  rc   : ℕ → PCode (List (Dig 256) × PlainPart (shapeOf L t) (annOf L t))
  hrc  : ∀ i y s, (rc i).put y = some s → 64 ≤ s.length

variable {L : BatchProtocolWithLeafBody I X} {tg : Tag}

/-- the tuple -/
abbrev Tup (L : BatchProtocolWithLeafBody I X) (tg : Tag := .test) : Type :=
  Bool × (List Bool × (ℕ × ((List (Dig 256) × PlainPart (shapeOf L tg) (annOf L tg)) × ℕ)))

/-- The code of the tuple. -/
def pTup (D : ChainD L tg) : PCode (Tup L tg) :=
  pHalf.cons 8 pHalf_len fun _ =>
    PCode.pre mid32
      ((pBits 256).cons 256 (pBits_len 256) fun _ =>
        PCode.pre (bytesToBits (_root_.Fmt.u64n (162 + 65536 * D.label)))
          (pWord.cons 64 pWord_len fun i =>
            (D.rc i).ins (pKwc (D.kind i) (D.work i)) 64 64 (pKwc_len _ _) (D.hrc i)))

/-- a typed point as a tuple -/
def toTup (D : ChainD L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) : Option (Tup L tg) :=
  match x.1.round, x.1.head with
  | i + 1, .f2 none ρ =>
      some (decide ((blockTo (decide (D.work (i + 1) ≠ 0)) K x.2).val % 2 = 1),
        ρ, i + 1,
        ((x.1.rt, x.1.plain), (blockTo (decide (D.work (i + 1) ≠ 0)) K x.2).val / 2))
  | _, _ => none

/-- and back -/
def ofTup (D : ChainD L tg) (K : ℕ) (t : Tup L tg) : Option (FbIn 256 L tg × Fin (K + 1)) :=
  match t.2.2.1 with
  | 0 => none
  | i + 1 =>
      if hb : 2 * t.2.2.2.2 + (if t.1 then 1 else 0) < K + 1 then
        some (⟨i + 1, .f2 none t.2.1, t.2.2.2.1.1, t.2.2.2.1.2⟩,
          blockOf (decide (D.work (i + 1) ≠ 0)) K ⟨2 * t.2.2.2.2 + (if t.1 then 1 else 0), hb⟩)
      else none

theorem ofTup_toTup (D : ChainD L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1))
    (t : Tup L tg) (h : toTup D K x = some t) : ofTup D K t = some x := by
  obtain ⟨⟨round, head, rt, plain⟩, j⟩ := x
  cases round with
  | zero => cases h
  | succ i =>
      cases head with
      | f2 xl ρ =>
          cases xl with
          | some _ => cases h
          | none =>
              rw [← Option.some.inj h]
              have hb := (blockTo (decide (D.work (i + 1) ≠ 0)) K j).isLt
              have e : 2 * ((blockTo (decide (D.work (i + 1) ≠ 0)) K j).val / 2) +
                    (if decide ((blockTo (decide (D.work (i + 1) ≠ 0)) K j).val % 2 = 1) = true then
                        1
                      else 0) =
                  (blockTo (decide (D.work (i + 1) ≠ 0)) K j).val := by
                by_cases h2 : (blockTo (decide (D.work (i + 1) ≠ 0)) K j).val % 2 = 1
                · rw [if_pos (decide_eq_true h2)]; omega
                · rw [if_neg (by simpa using h2)]; omega
              show (if hb : 2 * ((blockTo (decide (D.work (i + 1) ≠ 0)) K j).val / 2) +
                        (if decide ((blockTo (decide (D.work (i + 1) ≠ 0)) K j).val % 2 = 1) =
                              true then 1
                          else 0) < K + 1 then
                    some ((⟨i + 1, .f2 none ρ, rt, plain⟩ : FbIn 256 L tg),
                        blockOf (decide (D.work (i + 1) ≠ 0)) K ⟨_, hb⟩)
                  else none) = _
              rw [dif_pos (by rw [e]; exact hb)]
              have e' : (⟨2 * ((blockTo (decide (D.work (i + 1) ≠ 0)) K j).val / 2) +
                      (if decide ((blockTo (decide (D.work (i + 1) ≠ 0)) K j).val % 2 = 1) =
                            true then 1
                        else 0),
                    by rw [e]; exact hb⟩ : Fin (K + 1)) =
                  blockTo (decide (D.work (i + 1) ≠ 0)) K j := Fin.ext e
              rw [e', blockOf_blockTo]
      | f1 _ _ _ => cases h
      | f3 _ _ => cases h
      | f4 _ _ => cases h
      | f5 _ => cases h

theorem toTup_ofTup (D : ChainD L tg) (K : ℕ) (t : Tup L tg)
    (x : FbIn 256 L tg × Fin (K + 1)) (h : ofTup D K t = some x) : toTup D K x = some t := by
  obtain ⟨hf, ρ, i, ⟨rt, pl⟩, c⟩ := t
  cases i with
  | zero => cases h
  | succ i =>
      by_cases hb : 2 * c + (if hf then 1 else 0) < K + 1
      · have h0 : (if hb : 2 * c + (if hf then 1 else 0) < K + 1 then
                some ((⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 L tg),
                    blockOf (decide (D.work (i + 1) ≠ 0)) K ⟨2 * c + (if hf then 1 else 0), hb⟩)
              else none) = some x := h
        rw [dif_pos hb] at h0
        rw [← Option.some.inj h0]
        show some (decide
                ((blockTo (decide (D.work (i + 1) ≠ 0)) K
                      (blockOf (decide (D.work (i + 1) ≠ 0)) K
                        ⟨2 * c + (if hf then 1 else 0), hb⟩)).val % 2 = 1),
              ρ, i + 1,
              ((rt, pl),
                (blockTo (decide (D.work (i + 1) ≠ 0)) K
                    (blockOf (decide (D.work (i + 1) ≠ 0)) K
                      ⟨2 * c + (if hf then 1 else 0), hb⟩)).val / 2)) = _
        rw [blockTo_blockOf]
        cases hf
        · have e1 : (2 * c + 0) % 2 ≠ 1 := by omega
          have e2 : (2 * c + 0) / 2 = c := by omega
          show some (decide ((2 * c + 0) % 2 = 1), ρ, i + 1, ((rt, pl), (2 * c + 0) / 2)) = _
          rw [decide_eq_false e1, e2]
        · have e1 : (2 * c + 1) % 2 = 1 := by omega
          have e2 : (2 * c + 1) / 2 = c := by omega
          show some (decide ((2 * c + 1) % 2 = 1), ρ, i + 1, ((rt, pl), (2 * c + 1) / 2)) = _
          rw [decide_eq_true e1, e2]
      · have h0 : (if hb : 2 * c + (if hf then 1 else 0) < K + 1 then
                some ((⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 L tg),
                    blockOf (decide (D.work (i + 1) ≠ 0)) K ⟨2 * c + (if hf then 1 else 0), hb⟩)
              else none) = some x := h
        rw [dif_neg hb] at h0
        cases h0

/-- A chain query of a round 1, 2, .. with the number of a block of its answer. -/
def p162 (D : ChainD L tg) (K : ℕ) : PCode (FbIn 256 L tg × Fin (K + 1)) :=
  (pTup D).pull (toTup D K) (ofTup D K) (ofTup_toTup D K) (toTup_ofTup D K)

/-- The shape of every string that it writes. -/
theorem p162_shape (D : ChainD L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1))
    (s : List Bool) (h : (p162 D K).put x = some s) :
    ∃ (hb : Bool) (ρ r : List Bool),
      ρ.length = 256 ∧
      s = bitsOfByte (if hb then 1 else 0) ++
          (mid32 ++ (ρ ++ (bytesToBits (_root_.Fmt.u64n (162 + 65536 * D.label)) ++ r))) := by
  obtain ⟨t, -, ht⟩ := PCode.pull_put _ _ _ _ _ x s h
  obtain ⟨u, v, hu, hv, rfl⟩ := PCode.cons_put _ _ _ _ t s ht
  obtain ⟨v1, hv1, rfl⟩ := PCode.pre_put' _ _ _ v hv
  obtain ⟨u2, v2, hu2, hv2, rfl⟩ := PCode.cons_put _ _ _ _ t.2 v1 hv1
  obtain ⟨v3, -, rfl⟩ := PCode.pre_put' _ _ _ v2 hv2
  exact ⟨t.1, u2, v3, pBits_len 256 _ _ hu2, by rw [← Option.some.inj hu]⟩

/-- every string that it writes begins with the byte 0 or the byte 1 -/
theorem p162_head (D : ChainD L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) (s : List Bool)
    (h : (p162 D K).put x = some s) (e : UInt8) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    ¬ bitsOfByte e <+: s := by
  obtain ⟨hb, ρ, r, -, rfl⟩ := p162_shape D K x s h
  rintro ⟨t, ht⟩
  have := bitsOfByte_inj (List.append_inj_left ht (by rw [length_bitsOfByte, length_bitsOfByte]))
  cases hb
  · exact h0 this
  · exact h1 this

end TypedOracleCompiler.Run
