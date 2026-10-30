-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/CallDom.lean: the calls of the page of a file with three joined chains lie in the
domain of the format's hash, under plain bounds on the data.

The cut of the page's code to one file writes a call's string only where the call passes `inDom`
(OnBytes/K/Arm/KeyCut.lean): its half is 0 or 1, and it lies in the domain of the format's hash
(`Fmt.hDom`, Fmt/Rules23.lean). Here that test is shown of each maker of a call in
OnBytes/Maker/Page/Frame.lean, from bounds on the label, the index and the lengths. The bounds are
spelt with the format's own functions (`Fmt.treeBound`, `Fmt.idxOK`, `Fmt.saltLenOK`) at the rows'
named numbers, and with `domBytes`. The format has no name for its bound on the length of a call's
bytes: `domBytes` types that number again, and `hDom_size_le` holds it to `Fmt.hDom`'s own clause.

Main names:
  `domBytes`, `hDom_size_le`: a call in the domain has at most that many bytes.
  `startBytes`, `size_start`: the bytes of a start; a chain value as a start.
  `hDom_of_inDom`, `inDom_of`: `inDom` is `Fmt.hDom` at the call's fields, and a half of 0 or 1.
  `half_ok`: the byte of b mod 2 is 0 or 1.
  `size_roundBytes`, `firstBytes_size`: lengths.
  `rowCall_inDom`, `firstCall_inDom`, `gCallJ_inDom`, `rnodeCall_inDom`, `rleafCall_inDom`.

Limits: that the data of any file meet these bounds is not said here. No theorem here says that a
query that passes a cut's test of fitness is written by the cut. Nothing on leaves and vertices of
the trees over oracles. Nothing on any hash. Nothing on soundness. For proofs only; the program does
not import this file.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.KeyCut
import OnBytes.K.Arm.StrInj
import Fmt.Rules7

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type}

/-- The bound of `Fmt.hDom` on the number of a call's bytes, typed again. -/
def domBytes : ℕ := 2 ^ 32 - 144

/-- A call in the domain has at most `domBytes` bytes. -/
theorem hDom_size_le {n t i : ℕ} {s b : ByteArray} (h : Fmt.hDom n t i s b = true) :
    b.size ≤ domBytes := by
  simp only [Fmt.hDom, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- The bytes of a start, which are those of a digest. -/
def startBytes : ℕ := digBits / 8

/-- A call that passes `inDom` lies in the domain of the format's hash. (The test `callIn c` of
OnBytes/K/Arm/FileInj.lean is the right side, by its definition.) -/
theorem hDom_of_inDom {c : Fmt.OQ} (h : inDom c = true) :
    Fmt.hDom c.number c.tree c.index c.start c.bytes = true := by
  unfold inDom at h
  exact (Bool.and_eq_true _ _ ▸ h).2

/-- The way back, for a half of 0 or 1. -/
theorem inDom_of {c : Fmt.OQ} (hh : (c.half == 0 || c.half == 1) = true)
    (hd : Fmt.hDom c.number c.tree c.index c.start c.bytes = true) : inDom c = true := by
  unfold inDom
  rw [hh, hd]
  rfl

/-- The byte of b mod 2 is 0 or 1. -/
theorem half_ok (b : ℕ) :
    (UInt8.ofNat (b % 2) == 0 || UInt8.ofNat (b % 2) == 1) = true := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> rw [h] <;> rfl

/-- The bytes of a call of a round: the message and two words. -/
theorem size_roundBytes (msg : ByteArray) (kind w c nonce : ℕ) :
    (roundBytes msg kind w c nonce).size = msg.size + 8 + 8 := by
  unfold roundBytes
  rw [ByteArray.size_append, ByteArray.size_append, Fmt.size_u64n, Fmt.size_u64n]

/-- A chain value of as many bits as a digest has is a start of the format's length. -/
theorem size_start {ρ : List Bool} (h : ρ.length = digBits) : (bitsToBytes ρ).size = startBytes :=
  size_bitsToBytes ρ startBytes h

/-- The bytes of the call that makes a chain's first value. -/
theorem firstBytes_size (pd st : ByteArray) (salt : List Bool) :
    (firstBytes pd st salt).size = pd.size + 8 + st.size + 8 +
      (if salt.isEmpty = true then 8 else 8 + (bitsToBytes salt).size) := by
  unfold firstBytes
  split_ifs <;>
    simp only [ByteArray.size_append, Fmt.size_u64n]

/-- **A row's call.** -/
theorem rowCall_inDom {lab idx kind work nonce ow K : ℕ} {ρ : List Bool} {msg : ByteArray}
    (j : Fin (K + 1)) (hl : lab < Fmt.treeBound nRow) (hi : Fmt.idxOK nRow idx = true)
    (hρ : ρ.length = digBits) (hm : msg.size + 8 + 8 ≤ domBytes) :
    inDom (rowCall lab idx ρ msg kind work nonce ow K j) = true := by
  unfold inDom rowCall
  simp only [Bool.and_eq_true]
  refine ⟨half_ok _, ?_⟩
  simp only [Fmt.hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
    size_roundBytes]
  exact ⟨⟨⟨⟨⟨⟨⟨by decide, hl⟩, Or.inl (by decide)⟩, hi⟩, hm⟩, size_start hρ⟩, Or.inl (by decide)⟩,
    Fmt.leafOK_other _ _ _ rfl⟩

/-- **A first call.** -/
theorem firstCall_inDom {lab : ℕ} {pd stm : ByteArray} {run : List Bool}
    (hi : Fmt.idxOK nFirst lab = true) (hm : (firstBytes pd stm run).size ≤ domBytes) :
    inDom (firstCall lab pd stm run) = true := by
  unfold inDom firstCall
  simp only [Bool.and_eq_true]
  refine ⟨rfl, ?_⟩
  simp only [Fmt.hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, Or.inr trivial⟩, hi⟩, hm⟩, rfl⟩, Or.inr rfl⟩,
    Fmt.leafOK_other _ _ _ rfl⟩

variable {L : BatchProtocolWithLeafBody I X} {t : Tag}

/-- **The call of a query for the slot value.** -/
theorem gCallJ_inDom {F : FileJ L t} {q : JoiningRoundQuery 256 L t} {c : Fmt.OQ} (h : gCallJ F q = some c)
    (hl : F.lab₁ < Fmt.treeBound nRow) (hi : Fmt.idxOK nRow F.J = true)
    (hρ : q.ρ.length = digBits) : inDom c = true := by
  unfold gCallJ at h
  split_ifs at h
  rw [← Option.some.inj h]
  unfold inDom
  simp only [Bool.and_eq_true]
  refine ⟨rfl, ?_⟩
  simp only [Fmt.hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
    size_roundBytes]
  exact ⟨⟨⟨⟨⟨⟨⟨by decide, hl⟩, Or.inl (by decide)⟩, hi⟩, by decide⟩, size_start hρ⟩,
    Or.inl (by decide)⟩, Fmt.leafOK_other _ _ _ rfl⟩

/-- **A vertex of the request tree.** -/
theorem rnodeCall_inDom {cfg : ByteArray} {q : List Bool × List Bool} {c : Fmt.OQ}
    (h : rnodeCall cfg q = some c) (hc : cfg.size = startBytes) (h1 : q.1.length = digBits)
    (h2 : q.2.length = digBits) : inDom c = true := by
  unfold rnodeCall at h
  rw [← Option.some.inj h]
  unfold inDom
  simp only [Bool.and_eq_true]
  refine ⟨rfl, ?_⟩
  simp only [Fmt.hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
    ByteArray.size_append, size_start h1, size_start h2]
  exact ⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, Or.inr trivial⟩, by decide⟩, by decide⟩, hc⟩,
    Or.inl (by decide)⟩, Fmt.leafOK_other _ _ _ rfl⟩

/-- **A leaf of the request tree.** -/
theorem rleafCall_inDom {cfg : ByteArray} {sR : ℕ} {q : List Bool} {c : Fmt.OQ}
    (h : rleafCall cfg sR q = some c) (hc : cfg.size = startBytes)
    (hs : Fmt.saltLenOK sR = true) (hi : Fmt.idxOK nRLeaf c.index = true) : inDom c = true := by
  unfold rleafCall at h
  split_ifs at h with hq
  have e := Option.some.inj h
  subst e
  simp only [Fmt.saltLenOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  have h8 : 8 * (sR / 8) = sR := by omega
  have hz : (bitsToBytes (q.take (256 + 8 * sR))).size = startBytes + sR :=
    size_bitsToBytes _ _ (by rw [List.length_take, hq]; unfold startBytes digBits; omega)
  unfold inDom
  simp only [Bool.and_eq_true]
  refine ⟨rfl, ?_⟩
  simp only [Fmt.hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, hz]
  refine ⟨⟨⟨⟨⟨⟨⟨by decide, Fmt.leafPlace_lt _ _ _ (by decide) (by decide) (by omega)⟩,
    Or.inl (by decide)⟩, hi⟩, by unfold startBytes digBits; omega⟩, hc⟩, Or.inl (by decide)⟩, ?_⟩
  unfold Fmt.leafOK
  rw [Fmt.placeW_leafPlace _ _ _ (by decide) (by decide),
    Fmt.placeS_leafPlace _ _ _ (by decide) (by decide),
    Fmt.placeTree_leafPlace _ _ _ (by decide), h8]
  have hf : Fmt.leafFill 4 sR = 0 := by
    unfold Fmt.leafFill
    rw [if_pos (by omega)]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hf, hz]
  refine Or.inr ⟨⟨⟨⟨⟨by decide, by omega⟩, by omega⟩, Or.inr trivial⟩,
    by unfold startBytes digBits; omega⟩, ?_⟩
  have h0 : ((bitsToBytes (q.take (256 + 8 * sR))).extract (8 * 4) (8 * 4 + 0)).size = 0 := by
    rw [ByteArray.size_extract]
    omega
  rw [empty_of_size _ h0]
  rfl

end OnBytes.K.Arm
