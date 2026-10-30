-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/SeedRound.lean: a partial code of the typed query of the round in which the seeds of
a stored table's record are drawn, with the number of a block of its answer, as the string of one
half of the format's call number 162 on the seeds' chain.

Why. The seeds of a stored table's record are drawn on a chain of hash calls of its own, which has
one round; in it the prover says nothing, there is no proof of work, and the kind is "seeds". The
round's answer is a row of blocks of 32 bytes: block b is half (b mod 2) of the call number (b div
2); block 0 is the chain's next value, and the draw reads the blocks from 1 on (library,
Fmt/Rules5.lean: `Fmt.tail`, `Fmt.firstBlock`). In the sibling (a second form of the library's
soundness road, under OnBytes/TypedOracleCompiler/) that round is ONE typed query, of round 1 with the head
`.f2 none ρ`, whose answer has K blocks of verifier's message and then the chain's next value. A
page spells each pair (query, typed block) as one string. The sibling has a partial code for such
pairs at given data of a chain (`p162`, OnBytes/TypedOracleCompiler/Run/CodingPage162.lean). This file gives the
data of the seeds' chain and says what the code then writes. OnBytes/TypedOracleCompiler/Run/FirstName.lean has that
chain's first query.
 - `rcS i`: the code of a round's roots and plain part: at round 1 it writes, for no root and the
   round's fixed plain part, the word 0 (no message; the nonce 0); it writes nothing else;
 - `chainDS`: the chain's data: the label `Fmt.recordLabel`, the kind's number 3, no work, `rcS`;
 - `secondPS K := p162 chainDS K`;
 - `secondPS_put`: for a chain value ρ of 256 bits and K below 2 ^ 48: at the query ⟨1, .f2 none ρ,
   [], p1⟩ and the typed block j it writes the bits of the format's string of half (b mod 2) of the
   call number 162 under `Fmt.recordLabel`, round 1, start ρ's bytes, on the bytes
   `ByteArray.empty ++ Fmt.tail .seeds 0 0 (b div 2)`; b := `blockNo 0 K j`, the library's number of
   the typed block in the format's row;
 - `blockNo_last`, `blockNo_cast`: the typed block K (the chain's next value) is block 0 of the row;
   the typed block k below K is block k + 1;
 - `secondPS_only`: whatever it writes, it writes at a query ⟨1, .f2 none ρ, [], p1⟩ for some ρ.

The interface L, the tag, the fixed plain part with its test and K are parameters.

Main definitions: `rcS`, `chainDS`, `secondPS`.
Main theorems: `secondPS_put`, `secondPS_only`, `blockNo_last`, `blockNo_cast`.

Not claimed. A CODE, NO PAGE: that its strings are apart from those of other codes is not said. The
program asks whole calls, two strings each: for a draw that reads n blocks, the rows 0 to 2 ((n + 2)
div 2) − 1. This code writes the rows 0 to K. So every string that the program hashes is written if
K is at least that last row's number; a row beyond K is written at no typed block. Rows that no
program hashes may be written too. Nothing ties K to a draw. That any program hashes these strings
is not shown here; that they are the strings which another file of this tree writes out for the
seeds' round is not shown here. How the blocks become seeds is not said. Nothing on any hash.
Nothing on soundness.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.CodingPut
import OnBytes.TypedOracleCompiler.Run.PutSome

set_option autoImplicit false

namespace TypedOracleCompiler.Run.SeedRound
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PutSome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## The data of the seeds' chain -/

variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (tg : Tag) (p1 : PlainPart (shapeOf L tg) (annOf L tg))
  (isP1 : PlainPart (shapeOf L tg) (annOf L tg) → Bool) (hp : ∀ p, isP1 p = true ↔ p = p1)

/-- The word 0, as bits. -/
def word0 : List Bool := bytesToBits (_root_.Fmt.u64n 0)

/-- The code of a round's roots and plain part on the seeds' chain: at round 1, for no root and the
round's fixed plain part: no message, then the nonce 0. Nothing else is written. -/
def rcS (i : ℕ) : PCode (List (Dig 256) × PlainPart (shapeOf L tg) (annOf L tg)) where
  put := fun y => if i = 1 ∧ y.1.isEmpty = true ∧ isP1 y.2 = true then some word0 else none
  parse := fun s => if i = 1 ∧ s = word0 then some ([], p1) else none
  parse_put := fun y s h => by
    by_cases hc : i = 1 ∧ y.1.isEmpty = true ∧ isP1 y.2 = true
    · rw [if_pos hc] at h
      rw [← Option.some.inj h, if_pos ⟨hc.1, rfl⟩]
      obtain ⟨y1, y2⟩ := y
      have e1 : y1 = [] := List.isEmpty_iff.1 hc.2.1
      have e2 : y2 = p1 := (hp y2).1 hc.2.2
      rw [e1, e2]
    · rw [if_neg hc] at h
      cases h
  put_parse := fun s y h => by
    by_cases hc : i = 1 ∧ s = word0
    · rw [if_pos hc] at h
      rw [← Option.some.inj h, hc.2]
      exact if_pos ⟨hc.1, rfl, (hp p1).2 rfl⟩
    · rw [if_neg hc] at h
      cases h

/-- Every string that it writes has at least 64 bits. -/
theorem rcS_len (i : ℕ) (y : List (Dig 256) × PlainPart (shapeOf L tg) (annOf L tg)) (s : List Bool)
    (h : (rcS L tg p1 isP1 hp i).put y = some s) : 64 ≤ s.length := by
  have h0 : (if i = 1 ∧ y.1.isEmpty = true ∧ isP1 y.2 = true then some word0 else none) =
      some s := h
  by_cases hc : i = 1 ∧ y.1.isEmpty = true ∧ isP1 y.2 = true
  · rw [if_pos hc] at h0
    rw [← Option.some.inj h0]
    unfold word0
    rw [length_bytesToBits]
    exact Nat.le_refl 64
  · rw [if_neg hc] at h0
    cases h0

/-- The data of the chain from which the seeds of a stored table's record are drawn: its label;
the number of the kind "seeds"; no work; `rcS`. -/
def chainDS : ChainD L tg where
  label := _root_.Fmt.recordLabel
  kind := fun _ => _root_.Fmt.Kind.seeds.num
  work := fun _ => 0
  rc := rcS L tg p1 isP1 hp
  hrc := rcS_len L tg p1 isP1 hp

/-- The drawing round's query, with the number of a block of its answer. -/
def secondPS (K : ℕ) : PCode (FbIn 256 L tg × Fin (K + 1)) := p162 (chainDS L tg p1 isP1 hp) K

/-- The typed block K, the chain's next value, is block 0 of the format's row. -/
theorem blockNo_last (K : ℕ) : blockNo 0 K (Fin.last K) = 0 := by
  simp [blockNo]

/-- The typed block k below K is block k + 1 of the format's row. -/
theorem blockNo_cast (K : ℕ) (k : Fin K) : blockNo 0 K k.castSucc = k.val + 1 := by
  unfold blockNo
  rw [if_neg (by show k.val ≠ K; exact Nat.ne_of_lt k.isLt), if_pos rfl]
  rfl

/-- A typed block's number in the row is at most K. -/
theorem blockNo_le (K : ℕ) (j : Fin (K + 1)) : blockNo 0 K j ≤ K := by
  rw [blockNo_eq 0 K j (Or.inr rfl)]
  exact Nat.le_of_lt_succ (blockTo _ K j).isLt

/-- What it writes is the string of one half of the format's call number 162 on the seeds'
chain, for a chain value of 256 bits and K below 2 ^ 48: round 1, start ρ, no message, the kind
"seeds", no work, the nonce 0; b, the typed block's number in the format's row, gives the half and
the number of the call. -/
theorem secondPS_put (K : ℕ) (hK : K < 2 ^ 48) (ρ : List Bool) (hρ : ρ.length = 256)
    (j : Fin (K + 1)) :
    (secondPS L tg p1 isP1 hp K).put (⟨1, .f2 none ρ, [], p1⟩, j) =
      some (bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (blockNo 0 K j % 2)) 162
        _root_.Fmt.recordLabel 1 (bitsToBytes ρ)
        (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 (blockNo 0 K j / 2)))) := by
  have hb : (blockTo (decide ((0 : ℕ) ≠ 0)) K j).val = blockNo 0 K j :=
    (blockNo_eq 0 K j (Or.inr rfl)).symm
  have hle := blockNo_le K j
  have ht : toTup (chainDS L tg p1 isP1 hp) K ((⟨1, .f2 none ρ, [], p1⟩ : FbIn 256 L tg), j) =
      some (decide (blockNo 0 K j % 2 = 1), ρ, 1, (([], p1), blockNo 0 K j / 2)) := by
    show some (decide ((blockTo (decide ((0 : ℕ) ≠ 0)) K j).val % 2 = 1), ρ, 0 + 1,
      (([], p1), (blockTo (decide ((0 : ℕ) ≠ 0)) K j).val / 2)) = _
    rw [hb]
  have hw : (pKwc _root_.Fmt.Kind.seeds.num 0).put (blockNo 0 K j / 2) =
      some (bytesToBits (_root_.Fmt.u64n (3 + 256 * 0 + 65536 * (blockNo 0 K j / 2)))) := by
    show (kwcTo 3 0 (blockNo 0 K j / 2)).bind pWord.put = _
    unfold kwcTo
    rw [if_pos ⟨by norm_num, by norm_num, by omega⟩]
    exact if_pos (by omega)
  have hr : (rcS L tg p1 isP1 hp 1).put ([], p1) = some word0 :=
    if_pos ⟨rfl, rfl, (hp p1).2 rfl⟩
  have hw1 : pWord.put 1 = some (bytesToBits (_root_.Fmt.u64n 1)) := by
    show (if (1 : ℕ) < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n 1)) else none) = _
    exact if_pos (by norm_num)
  have h5 := ins_some (rcS L tg p1 isP1 hp 1) (pKwc _root_.Fmt.Kind.seeds.num 0) 64 64
    (pKwc_len _ _) (rcS_len L tg p1 isP1 hp 1) ([], p1) (blockNo 0 K j / 2) _ _ hr hw
  have h4 := cons_some pWord 64 pWord_len
    (fun i => ((chainDS L tg p1 isP1 hp).rc i).ins
      (pKwc ((chainDS L tg p1 isP1 hp).kind i) ((chainDS L tg p1 isP1 hp).work i)) 64 64
      (pKwc_len _ _) ((chainDS L tg p1 isP1 hp).hrc i)) 1 (([], p1), blockNo 0 K j / 2) _ _
    hw1 h5
  have h3 :=
    pre_some (bytesToBits (_root_.Fmt.u64n (162 + 65536 * _root_.Fmt.recordLabel))) _ _ _ h4
  have h2 := cons_some (pBits 256) 256 (pBits_len 256) (fun _ => PCode.pre
    (bytesToBits (_root_.Fmt.u64n (162 + 65536 * _root_.Fmt.recordLabel))) _) ρ _ _ _
    (if_pos hρ : (pBits 256).put ρ = some ρ) h3
  have h1 := pre_some mid32 _ _ _ h2
  have h0 := cons_some pHalf 8 pHalf_len (fun _ => PCode.pre mid32 _)
    (decide (blockNo 0 K j % 2 = 1)) _ _ _ rfl h1
  have e0 : (secondPS L tg p1 isP1 hp K).put ((⟨1, .f2 none ρ, [], p1⟩ : FbIn 256 L tg), j) =
      (toTup (chainDS L tg p1 isP1 hp) K ((⟨1, .f2 none ρ, [], p1⟩ : FbIn 256 L tg), j)).bind
        (pTup (chainDS L tg p1 isP1 hp)).put := rfl
  rw [e0, ht]
  refine Eq.trans h0 (congrArg some ?_)
  rw [oStr64_bits _ _ _ _ _ (size_bitsToBytes ρ 32 hρ),
    bytesToBits_bitsToBytes ρ ((whole_iff ρ).2 ⟨32, hρ⟩), ← half_bits]
  have hl : word0.length = 64 := by
    unfold word0
    rw [length_bytesToBits]
    rfl
  have et : bytesToBits (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 (blockNo 0 K j / 2)) =
      bytesToBits (_root_.Fmt.u64n (3 + 256 * 0 + 65536 * (blockNo 0 K j / 2))) ++ word0 := by
    rw [ByteArray.empty_append]
    unfold _root_.Fmt.tail word0
    rw [bytesToBits_append]
    rfl
  rw [et, hl, Nat.sub_self, List.take_zero, List.drop_zero, List.nil_append]

/-- Whatever it writes, it writes at a query of round 1 in the later rounds' format, with no root
and the round's fixed plain part. -/
theorem secondPS_only (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) (s : List Bool)
    (h : (secondPS L tg p1 isP1 hp K).put x = some s) :
    ∃ ρ, x.1 = ⟨1, .f2 none ρ, [], p1⟩ := by
  have h' : (p162 (chainDS L tg p1 isP1 hp) K).put x = some s := h
  obtain ⟨t, ht, hs⟩ := PCode.pull_put _ _ _ _ _ x s h'
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
        obtain ⟨u, v, -, hv, rfl⟩ := PCode.cons_put _ _ _ _ _ s hs
        obtain ⟨v1, hv1, rfl⟩ := PCode.pre_put' _ _ _ v hv
        obtain ⟨u2, v2, -, hv2, rfl⟩ := PCode.cons_put _ _ _ _ _ v1 hv1
        obtain ⟨v3, hv3, rfl⟩ := PCode.pre_put' _ _ _ v2 hv2
        obtain ⟨u4, v4, -, hv4, rfl⟩ := PCode.cons_put _ _ _ _ _ v3 hv3
        obtain ⟨s0, w0, hs0, -, rfl⟩ := PCode.ins_put _ _ _ _ _ _ _ v4 hv4
        have h0 : (if i + 1 = 1 ∧ rt.isEmpty = true ∧ isP1 plain = true then some word0
            else none) = some s0 := hs0
        by_cases hc : i + 1 = 1 ∧ rt.isEmpty = true ∧ isP1 plain = true
        · refine ⟨ρ, ?_⟩
          have e1 : rt = [] := List.isEmpty_iff.1 hc.2.1
          have e2 : plain = p1 := (hp plain).1 hc.2.2
          rw [hc.1, e1, e2]
        · rw [if_neg hc] at h0
          cases h0
    | f1 _ _ _ => cases ht
    | f3 _ _ => cases ht
    | f4 _ _ => cases ht
    | f5 _ => cases ht

end TypedOracleCompiler.Run.SeedRound
