-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingPage162.lean: the partial code of a chain query with the number of a block of its answer,
for the rounds 1, 2, .., in the programs' format.

Definitions that compute, with their laws.
A partial code (`PCode`, Run/CodingPart.lean) writes some points of a type as bit strings,
injectively, with a parser. A chain query (`FbIn`, Compile/Batch/Oracles.lean) is the typed query
that draws a round's verifier message (Fiat-Shamir); its answer is K blocks of verifier message and
the chain's next value.

After the format page's rules R2.2, R2.4 (the oracle's strings), R5.2 (call j of round i), R5.4
(the row of blocks), in an edition that is not the one that ships, in which the chain's label stands
in the tree's place of the call's label (at the label 0 the string is that of a second edition, also
not the one that ships); and after a convention of this library that the order of a chain answer's
blocks is data of the encoding of the queries (`blockTo`, `blockOf`, Run/CodingImpl.lean).

The string of block b of round i, with rc i as it is meant (below): the half b mod 2 (one byte: a
call of a round has a digest of 64 bytes, two blocks of 32); digest length 64, key length, fanout,
depth, 28 zero bytes; the chain's value before the round (32 bytes); the word (the rounds' number) +
2^16 (the chain's label); the word i; the prover's message; the word kind + 2^8 w + 2^16 (b div 2);
the word of the nonce.

The data (`ChainD L t`; the protocol's tag t is a parameter; where none is written it is "test"):
label: the chain's; kind i, work i: by the plan; rc i : a partial code of (root or none, typed plain
part) at round i, meant to write the prover's message and then the 64 bits of the nonce's word (the
nonce is a component of the typed plain part; 0 where the round has no work). A round that the plan
does not have: rc i is meant to write nothing. The record asks of rc i only `hrc` (its strings have
at least 64 bits); message and nonce are asked in `ChainFit.rc`, Run/CodingPut.lean.

Main names:
  `pTup D`: the code of the tuple (half, chain value, round, ((root, plain part), number of the
    call)).
  `toTup`, `ofTup`: a typed point (query, block) as such a tuple, and back: a query of a round i + 1
    whose head is the later-round format with no late field; block j of the typed answer is block
    (blockTo ..) of the format's row.
  `p162`: the partial code of the title.
  `p162_shape`, `p162_head`: every string that it writes: the half's byte, the 32 bytes, 256 bits,
    the word of the rounds' number and the label, a rest.

Limits: it is not asked here that the chain's label is below 2^48 and the round below 2^63, as the
format's rule R2.3 wants. The code is a code all the same: the label enters as one constant word,
and a round is any number below 2^64. But a label of 2^48 or more does not fit its word, which holds
the number modulo 2^64: the string is then that of another label; and a round from 2^63 on gives a
string that is none of the format's. Whoever ties these strings to the format's hash must ask both
bounds.
This file does not say which rc: rc is data, a field of `ChainD`. Round 0 (the chain's first value)
is another file's. That what is written is the string of the functions of Run/CodingFn.lean is
proved in Run/CodingPut.lean (`p162_put`, under its hypotheses), not here.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingSeq
import Run.CodingImpl

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

namespace PCode
variable {A B : Type}

theorem pull_len (p : PCode A) (f : B → Option A) (g : A → Option B)
    (h1 : ∀ b a, f b = some a → g a = some b) (h2 : ∀ a b, g a = some b → f b = some a)
    (n : ℕ) (hp : p.Len n) :
    (p.pull f g h1 h2).Len n := fun b s h => by
  cases hf : f b with
  | none =>
      have h0 : (f b).bind p.put = some s := h
      rw [hf] at h0
      cases h0
  | some a =>
      have h0 : (f b).bind p.put = some s := h
      rw [hf] at h0
      exact hp a s h0

theorem pull_put (p : PCode A) (f : B → Option A) (g : A → Option B)
    (h1 : ∀ b a, f b = some a → g a = some b) (h2 : ∀ a b, g a = some b → f b = some a) (b : B)
    (s : List Bool) (h : (p.pull f g h1 h2).put b = some s) :
    ∃ a, f b = some a ∧ p.put a = some s := by
  cases hf : f b with
  | none =>
      have h0 : (f b).bind p.put = some s := h
      rw [hf] at h0
      cases h0
  | some a =>
      have h0 : (f b).bind p.put = some s := h
      rw [hf] at h0
      exact ⟨a, rfl, h0⟩

theorem cons_put (a : PCode A) (n : ℕ) (ha : a.Len n) (p : A → PCode B) (x : A × B)
    (s : List Bool) (h : (a.cons n ha p).put x = some s) :
    ∃ u v, a.put x.1 = some u ∧ (p x.1).put x.2 = some v ∧ s = u ++ v := by
  have h0 : (a.put x.1).bind (fun u => ((p x.1).put x.2).map (u ++ ·)) = some s := h
  cases hu : a.put x.1 with
  | none => rw [hu] at h0; cases h0
  | some u =>
      rw [hu] at h0
      have h1 : ((p x.1).put x.2).map (u ++ ·) = some s := h0
      cases hv : (p x.1).put x.2 with
      | none => rw [hv] at h1; cases h1
      | some v =>
          rw [hv] at h1
          exact ⟨u, v, rfl, rfl, (Option.some.inj h1).symm⟩

theorem pre_put' (c : List Bool) (p : PCode A) (a : A)
    (s : List Bool) (h : (p.pre c).put a = some s) :
    ∃ u, p.put a = some u ∧ s = c ++ u := by
  have h0 : (p.put a).map (c ++ ·) = some s := h
  cases hp : p.put a with
  | none => rw [hp] at h0; cases h0
  | some u =>
      rw [hp] at h0
      exact ⟨u, rfl, (Option.some.inj h0).symm⟩

end PCode

/-- The half as a byte. -/
def pHalf : PCode Bool where
  put := fun h => some (bitsOfByte (if h then 1 else 0))
  parse := fun s =>
    if s = bitsOfByte 0 then some false else if s = bitsOfByte 1 then some true else none
  parse_put := fun h s hs => by
    rw [← Option.some.inj hs]
    cases h
    · exact if_pos rfl
    · show (if bitsOfByte 1 = bitsOfByte 0 then some false
          else if bitsOfByte 1 = bitsOfByte 1 then some true
          else none) = some true
      rw [if_neg (by decide), if_pos rfl]
  put_parse := fun s h hs => by
    by_cases h0 : s = bitsOfByte 0
    · rw [if_pos h0] at hs
      rw [← Option.some.inj hs, h0]
      rfl
    · rw [if_neg h0] at hs
      by_cases h1 : s = bitsOfByte 1
      · rw [if_pos h1] at hs
        rw [← Option.some.inj hs, h1]
        rfl
      · rw [if_neg h1] at hs
        cases hs

theorem pHalf_len : pHalf.Len 8 := fun h s hs => by
  rw [← Option.some.inj hs]
  exact length_bitsOfByte _

/-- The word that holds kind, work and the number of a call. -/
def kwcTo (kind w c : ℕ) : Option ℕ :=
  if kind < 256 ∧ w < 256 ∧ c < 2 ^ 48 then some (kind + 256 * w + 65536 * c) else none

/-- The number of the call, read off such a word. -/
def kwcOf (kind w v : ℕ) : Option ℕ :=
  if kind < 256 ∧ w < 256 ∧ v / 65536 < 2 ^ 48 ∧ v % 65536 = kind + 256 * w then some (v / 65536)
  else none

theorem kwcOf_kwcTo (kind w c v : ℕ) (h : kwcTo kind w c = some v) : kwcOf kind w v = some c := by
  unfold kwcTo at h
  unfold kwcOf
  by_cases hc : kind < 256 ∧ w < 256 ∧ c < 2 ^ 48
  · rw [if_pos hc] at h
    rw [← Option.some.inj h]
    obtain ⟨a1, a2, a3⟩ := hc
    have e1 : (kind + 256 * w + 65536 * c) / 65536 = c := by omega
    have e2 : (kind + 256 * w + 65536 * c) % 65536 = kind + 256 * w := by omega
    rw [if_pos ⟨a1, a2, by rw [e1]; exact a3, e2⟩, e1]
  · rw [if_neg hc] at h
    cases h

theorem kwcTo_kwcOf (kind w v c : ℕ) (h : kwcOf kind w v = some c) : kwcTo kind w c = some v := by
  unfold kwcOf at h
  unfold kwcTo
  by_cases hv : kind < 256 ∧ w < 256 ∧ v / 65536 < 2 ^ 48 ∧ v % 65536 = kind + 256 * w
  · rw [if_pos hv] at h
    rw [← Option.some.inj h]
    obtain ⟨a1, a2, a3, a4⟩ := hv
    rw [if_pos ⟨a1, a2, a3⟩]
    congr 1
    omega
  · rw [if_neg hv] at h
    cases h

/-- The number of a call in its word, beside the round's kind and work. -/
def pKwc (kind w : ℕ) : PCode ℕ :=
  pWord.pull (kwcTo kind w) (kwcOf kind w) (kwcOf_kwcTo kind w) (kwcTo_kwcOf kind w)

theorem pKwc_len (kind w : ℕ) : (pKwc kind w).Len 64 := PCode.pull_len _ _ _ _ _ 64 pWord_len

variable {I X : Type}

/-- The data. -/
structure ChainD (L : BatchProtocol I X) (t : Tag := .test) where
  /-- The chain's label: it stands in the tree's place of the label of a round's call. -/
  label : ℕ
  kind : ℕ → ℕ
  work : ℕ → ℕ
  rc   : ℕ → PCode (Option (Dig 256) × PlainPart (shapeOf L t) (annOf L t))
  hrc  : ∀ i y s, (rc i).put y = some s → 64 ≤ s.length

variable {L : BatchProtocol I X} {tg : Tag}

/-- The 32 bytes after the half in the string of a call with a digest of 64 bytes. -/
def mid32 : List Bool := bytesToBits (⟨#[64, 0, 1, 1]⟩ ++ _root_.Fmt.zeroBytes 28)

/-- The tuple. -/
abbrev Tup (L : BatchProtocol I X) (tg : Tag := .test) : Type :=
  Bool × (List Bool × (ℕ × ((Option (Dig 256) × PlainPart (shapeOf L tg) (annOf L tg)) × ℕ)))

/-- The code of the tuple. -/
def pTup (D : ChainD L tg) : PCode (Tup L tg) :=
  pHalf.cons 8 pHalf_len fun _ =>
    PCode.pre mid32
      ((pBits 256).cons 256 (pBits_len 256) fun _ =>
        PCode.pre (bytesToBits (_root_.Fmt.u64n (162 + 65536 * D.label)))
          (pWord.cons 64 pWord_len fun i =>
            (D.rc i).ins (pKwc (D.kind i) (D.work i)) 64 64 (pKwc_len _ _) (D.hrc i)))

/-- A typed point as a tuple. -/
def toTup (D : ChainD L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) : Option (Tup L tg) :=
  match x.1.round, x.1.head with
  | i + 1, .f2 none ρ =>
      some (decide ((blockTo (decide (D.work (i + 1) ≠ 0)) K x.2).val % 2 = 1),
        ρ, i + 1,
        ((x.1.rt, x.1.plain), (blockTo (decide (D.work (i + 1) ≠ 0)) K x.2).val / 2))
  | _, _ => none

/-- And back. -/
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

/-- The partial code of a chain query of a round 1, 2, .. with the number of a block of its answer.
-/
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

/-- No string that `p162` writes begins with a byte other than 0 and 1 (`h0`, `h1`). -/
theorem p162_head (D : ChainD L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) (s : List Bool)
    (h : (p162 D K).put x = some s) (e : UInt8) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    ¬ bitsOfByte e <+: s := by
  obtain ⟨hb, ρ, r, -, rfl⟩ := p162_shape D K x s h
  rintro ⟨t, ht⟩
  have := bitsOfByte_inj (List.append_inj_left ht (by rw [length_bitsOfByte, length_bitsOfByte]))
  cases hb
  · exact h0 this
  · exact h1 this

end Run
