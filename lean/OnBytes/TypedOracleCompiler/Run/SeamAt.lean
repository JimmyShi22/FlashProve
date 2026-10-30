-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/SeamAt.lean: a typed chain query at ONE fixed round, with no root, as the pair of
its chain value and a part of its plain part; partial codes of such pairs carried over to codes of
queries; and the code of the hash under the number 173 that binds a first chain's seal.

In the sibling (a second form of the library's soundness road, under OnBytes/TypedOracleCompiler/) a file's
several chains are typed as one chain, with further rounds, the seams, between them
(OnBytes/TypedOracleCompiler/Slice/Plain3.lean). At a seam the prover sends a plain part alone and the verifier
draws nothing. On bytes a seam is one hash call that is no round of any chain: the leaf of the
binding tree, or the first value of the next chain. Its input holds the typed chain value (the seal;
the binding root) and what the seam's plain part carries. This file has what all such codes share.
 - `SeamD L tg Z`: the data: the typed round; how the chain value stands in the head (`mkH`, `selH`,
   both laws); how a value of Z stands in the type of plain parts (`inS`, `outS`, both laws);
 - `selS`, `mkS`, with both laws; `seamP D p : PCode (FbIn 256 L tg)` for a code p of pairs (chain
   value, value of Z); `seamP_some`: where p writes, it writes the same at ⟨round, mkH ρ, [], inS
   z⟩; `seamP_put`, `seamP_only`: whatever it writes, p writes, at such a query;
 - `tailP p K`: a code of queries as a code of (query, block), at the block of the typed tail alone;
   `tailP_some`, `tailP_put`;
 - `p173 c n`: the code of (chain value of 256 bits, salt of n bits): a fixed string c, the chain
   value, the salt; `p173_some`; `p173_str`: at c := `head173 cfg place index` and whole bytes that
   is the bits of `Fmt.oStr 0 173 place index cfg (value's bytes ++ salt's bytes)`.

Main definitions: `SeamD`, `selS`, `mkS`, `seamP`, `tailP`, `p173`, `head173`.
Main theorems: `mkS_selS`, `selS_mkS`, `seamP_some`, `seamP_put`, `seamP_only`, `tailP_some`,
`p173_some`, `p173_str`.

Not claimed. CODES, NO PAGE: that their strings are apart from other codes' is not said. `place` and
`index` are free numbers here. That the format's leaf of a binding tree is hashed at this string is
not shown: it wants place = `Fmt.leafPlace 0 4 (salt's words)`, index = 2 ^ depth + slot, a salt of
5 to 8 words, and that four words of the seal, a fill and the salt (library, Fmt/Rules7.lean:
`bindLeafW`, `leafBytes`) are the seal's 32 bytes and the salt: the fill is empty for every salt of
at most 80 bytes. A binding tree of depth 0 alone has its root at this call. `head173` holds the
label as `Fmt.label 173 place index`, not as two words (OnBytes/TypedOracleCompiler/Run/Apart.lean: `lw_173` has the
words). Nothing on any hash. Nothing on soundness.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.CodingPut
import OnBytes.TypedOracleCompiler.Run.PutSome

set_option autoImplicit false

namespace TypedOracleCompiler.Run.SeamAt
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PutSome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type}

/-- The data of a seam: its typed round, the head that holds the chain value, and how a value of
Z stands among the plain parts. -/
structure SeamD (L : BatchProtocolWithLeafBody I X) (tg : Tag) (Z : Type) where
  /-- the typed round -/
  round : ℕ
  /-- the head that holds the chain value ρ -/
  mkH : Bits → Head 256 X
  /-- the chain value of such a head -/
  selH : Head 256 X → Option Bits
  /-- reading undoes making -/
  hsel : ∀ ρ, selH (mkH ρ) = some ρ
  /-- making undoes reading -/
  hmk : ∀ h ρ, selH h = some ρ → mkH ρ = h
  /-- a value of Z as a plain part -/
  inS : Z → PlainPart (shapeOf L tg) (annOf L tg)
  /-- and back -/
  outS : PlainPart (shapeOf L tg) (annOf L tg) → Option Z
  /-- the way back undoes the way in -/
  hout : ∀ z, outS (inS z) = some z
  /-- the way in undoes the way back -/
  hin : ∀ y z, outS y = some z → inS z = y

variable {L : BatchProtocolWithLeafBody I X} {tg : Tag} {Z : Type}

/-- A query at the seam's round, with no root, as (chain value, value of Z). -/
def selS (D : SeamD L tg Z) (q : FbIn 256 L tg) : Option (Bits × Z) :=
  if q.round = D.round ∧ q.rt.isEmpty = true then
    match D.selH q.head, D.outS q.plain with
    | some ρ, some z => some (ρ, z)
    | _, _ => none
  else none

/-- And back. -/
def mkS (D : SeamD L tg Z) (a : Bits × Z) : Option (FbIn 256 L tg) :=
  some ⟨D.round, D.mkH a.1, [], D.inS a.2⟩

/-- The way back undoes the way there. -/
theorem mkS_selS (D : SeamD L tg Z) (q : FbIn 256 L tg) (a : Bits × Z)
    (h : selS D q = some a) : mkS D a = some q := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold selS at h
  dsimp only at h
  by_cases hc : round = D.round ∧ rt.isEmpty = true
  · rw [if_pos hc] at h
    cases h1 : D.selH head with
    | none => rw [h1] at h; cases h
    | some ρ =>
      cases h2 : D.outS plain with
      | none => rw [h1, h2] at h; cases h
      | some z =>
        rw [h1, h2] at h
        rw [← Option.some.inj h]
        unfold mkS
        dsimp only
        rw [D.hmk head ρ h1, D.hin plain z h2, ← hc.1, ← List.isEmpty_iff.1 hc.2]
  · rw [if_neg hc] at h
    cases h

/-- What `selS` gives at a query that `mkS` makes. -/
theorem selS_at (D : SeamD L tg Z) (ρ : Bits) (z : Z) :
    selS D ⟨D.round, D.mkH ρ, [], D.inS z⟩ = some (ρ, z) := by
  unfold selS
  dsimp only
  rw [if_pos ⟨rfl, rfl⟩, D.hsel ρ, D.hout z]

/-- The way there undoes the way back. -/
theorem selS_mkS (D : SeamD L tg Z) (a : Bits × Z) (q : FbIn 256 L tg)
    (h : mkS D a = some q) : selS D q = some a := by
  rw [← Option.some.inj h]
  exact selS_at D a.1 a.2

/-- A code of pairs (chain value, value of Z) as a code of queries at the seam. -/
def seamP (D : SeamD L tg Z) (p : PCode (Bits × Z)) : PCode (FbIn 256 L tg) :=
  p.pull (selS D) (mkS D) (mkS_selS D) (selS_mkS D)

/-- Where p writes, the code of queries writes the same string. -/
theorem seamP_some (D : SeamD L tg Z) (p : PCode (Bits × Z)) (ρ : Bits) (z : Z) (s : List Bool)
    (h : p.put (ρ, z) = some s) : (seamP D p).put ⟨D.round, D.mkH ρ, [], D.inS z⟩ = some s :=
  pull_some _ _ _ _ _ _ _ _ (selS_at D ρ z) h

/-- Whatever the code of queries writes, p writes. -/
theorem seamP_put (D : SeamD L tg Z) (p : PCode (Bits × Z)) (q : FbIn 256 L tg) (s : List Bool)
    (h : (seamP D p).put q = some s) : ∃ a, p.put a = some s := by
  obtain ⟨a, -, ha⟩ := PCode.pull_put _ _ _ _ _ q s h
  exact ⟨a, ha⟩

/-- Whatever it writes, it writes at a query of the seam's round, with no root. -/
theorem seamP_only (D : SeamD L tg Z) (p : PCode (Bits × Z)) (q : FbIn 256 L tg) (s : List Bool)
    (h : (seamP D p).put q = some s) : ∃ ρ z, q = ⟨D.round, D.mkH ρ, [], D.inS z⟩ := by
  obtain ⟨a, ha, -⟩ := PCode.pull_put _ _ _ _ _ q s h
  exact ⟨a.1, a.2, (Option.some.inj (mkS_selS D q a ha)).symm⟩

/-! ## At the block of the typed tail alone -/

/-- A query with the block of the typed tail. -/
def selT (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) : Option (FbIn 256 L tg) :=
  if x.2 = Fin.last K then some x.1 else none

/-- And back. -/
def mkT (K : ℕ) (q : FbIn 256 L tg) : Option (FbIn 256 L tg × Fin (K + 1)) := some (q, Fin.last K)

/-- The way back undoes the way there. -/
theorem mkT_selT (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) (q : FbIn 256 L tg)
    (h : selT K x = some q) : mkT K q = some x := by
  unfold selT at h
  by_cases hc : x.2 = Fin.last K
  · rw [if_pos hc] at h
    rw [← Option.some.inj h]
    exact congrArg some (Prod.ext rfl hc.symm)
  · rw [if_neg hc] at h
    cases h

/-- The way there undoes the way back. -/
theorem selT_mkT (K : ℕ) (q : FbIn 256 L tg) (x : FbIn 256 L tg × Fin (K + 1))
    (h : mkT K q = some x) : selT K x = some q := by
  rw [← Option.some.inj h]
  exact if_pos rfl

/-- A code of queries as a code of (query, block): at the block of the typed tail alone. The
other blocks of such an answer have no string. -/
def tailP (p : PCode (FbIn 256 L tg)) (K : ℕ) : PCode (FbIn 256 L tg × Fin (K + 1)) :=
  p.pull (selT K) (mkT K) (mkT_selT K) (selT_mkT K)

/-- Where p writes, it writes the same string at the tail's block. -/
theorem tailP_some (p : PCode (FbIn 256 L tg)) (K : ℕ) (q : FbIn 256 L tg) (s : List Bool)
    (h : p.put q = some s) : (tailP p K).put (q, Fin.last K) = some s :=
  pull_some _ _ _ _ _ _ _ _ (if_pos rfl) h

/-- Whatever it writes, p writes at the query, and the block is the tail's. -/
theorem tailP_put (p : PCode (FbIn 256 L tg)) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1))
    (s : List Bool) (h : (tailP p K).put x = some s) : p.put x.1 = some s ∧ x.2 = Fin.last K := by
  obtain ⟨q, hq, hs⟩ := PCode.pull_put _ _ _ _ _ x s h
  unfold selT at hq
  by_cases hc : x.2 = Fin.last K
  · rw [if_pos hc] at hq
    rw [Option.some.inj hq]
    exact ⟨hs, hc⟩
  · rw [if_neg hc] at hq
    cases hq

/-! ## The hash under the number 173 -/

/-- The code of (chain value of 256 bits, salt of n bits): a fixed string, the value, the
salt. -/
def p173 (c : List Bool) (n : ℕ) : PCode (Bits × Bits) :=
  PCode.pre c ((pBits 256).cons 256 (pBits_len 256) fun _ => pBits n)

/-- What it writes. -/
theorem p173_some (c : List Bool) (n : ℕ) (ρ sa : Bits) (hρ : ρ.length = 256)
    (hs : sa.length = n) : (p173 c n).put (ρ, sa) = some (c ++ (ρ ++ sa)) :=
  pre_some c _ _ _ (cons_some (pBits 256) 256 (pBits_len 256) (fun _ => pBits n) ρ sa ρ sa
    (if_pos hρ) (if_pos hs))

/-- The fixed string before the seal in the format's string of the call: a byte 0 and 32 fixed
bytes, the start cfg, the label of (173, place, index). -/
def head173 (cfg : ByteArray) (place index : ℕ) : List Bool :=
  pre33 ++ (bytesToBits cfg ++ bytesToBits (_root_.Fmt.label 173 place index))

/-- At that fixed string it writes `Fmt.oStr 0 173 place index cfg` of the value's and the salt's
bytes, for a start of 32
bytes and a salt of k whole bytes. -/
theorem p173_str (cfg : ByteArray) (hc : cfg.size = 32) (place index k : ℕ) (ρ sa : Bits)
    (hρ : ρ.length = 256) (hs : sa.length = 8 * k) :
    (p173 (head173 cfg place index) (8 * k)).put (ρ, sa) =
      some (bytesToBits (_root_.Fmt.oStr 0 173 place index cfg
        (bitsToBytes ρ ++ bitsToBytes sa))) := by
  rw [p173_some _ _ ρ sa hρ hs, oStr32_bits _ _ _ _ _ (by decide) hc, bytesToBits_append,
    bytesToBits_bitsToBytes ρ ((whole_iff ρ).2 ⟨32, hρ⟩),
    bytesToBits_bitsToBytes sa ((whole_iff sa).2 ⟨k, hs⟩)]
  unfold head173
  simp only [List.append_assoc]

end TypedOracleCompiler.Run.SeamAt
