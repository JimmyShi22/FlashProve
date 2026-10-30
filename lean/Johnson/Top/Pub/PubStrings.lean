-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Pub/PubStrings.lean: the two public strings of the entry's arm: the strings on which the
format's hash is called for the configuration's digest and for the parameters' digest of the entry's
chain; and the public algorithm of two questions at the oracle that is made from the format's hash.

Why. Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublic.lean bounds the entry's arm where two public digests are
answers of the drawn function: c at a string s0, then p at a string `s1 c` (`pub2`). It asks of the
strings that `s1 c` is never s0, and that both code points of the spare oracle. By the format both
digests are one call each, under the number 169: index 2 on the public files' bytes, index 1 on the
chain's parameter bytes, which hold the first digest (library, Fmt/Rules4.lean: `configDigestW`,
`paramsDigestW`).

Main definitions.
 `s0Of pol lay KL`   the bits of the string of the call 169, index 2, on `Fmt.configBytes` of the
                     three public files.
 `s1Of G c`          the bits of the string of the call 169, index 1, on the parameter bytes of the
                     description `entryXD G` at the bytes of c.
Main theorems.
 `s0_call169`, `s1_call169`   both are strings of a call with the number 169 (`IsCall169`,
                     OnBytes/TypedOracleCompiler/Run/PageXJoin.lean).
 `s1_ne_s0`          `s1Of G c` is never `s0Of pol lay KL`: the labels' second words differ.
 `pub2_oBits`        at `Run.oBits`, the oracle made from the format's hash, `pub2` at these strings
                     returns the program's digest of the three public files and `EntryRunTop.pdOf`
                     of the description at that digest. Asked: both calls' bytes are within the
                     hash's bound on lengths.

What is not claimed. One fixed oracle in `pub2_oBits`; no probability; nothing on soundness. That a
program asks these strings in a run is not said: the equation is between values. The two bounds on
lengths are premises. Nothing on any other chain's parameters' digest.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublic
import OnBytes.TypedOracleCompiler.Slice.EntryRunTop
import OnBytes.TypedOracleCompiler.Slice.EntryDesc
import OnBytes.TypedOracleCompiler.Run.PageXJoin
import OnBytes.Hash.HEq
import Run.ParserHashProofs
import Fmt.Rules23Laws

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm.Pub
open Rom TypedOracleCompiler.Run TypedOracleCompiler.Slice TypedOracleCompiler.Compile.Batch.Cms
open _root_.Run (bytesToBits bytesToDig digToBytes oBits)
open _root_.Iop (Dig)
open OnBytes.Tie (EntryGround)

/-- The string of the call that hashes the three public files: number 169, index 2. -/
def s0Of (pol lay KL : ByteArray) : List Bool :=
  bytesToBits (Fmt.oStr 0 169 0 2 Fmt.zero32 (Fmt.configBytes [pol, lay, KL]))

/-- The string of the call that hashes the parameter bytes of the entry's chain at the configuration
digest c: number 169, index 1. -/
def s1Of (G : EntryGround) (c : Dig 256) : List Bool :=
  bytesToBits (Fmt.oStr 0 169 0 1 Fmt.zero32 (entryXD G (digToBytes c)).base.params)

/-- The first public string is the string of a call with the number 169. -/
theorem s0_call169 (pol lay KL : ByteArray) : IsCall169 (s0Of pol lay KL) :=
  ⟨0, 0, 2, Fmt.zero32, _, Or.inl rfl, rfl, rfl⟩

/-- So is the second, at every first digest. -/
theorem s1_call169 (G : EntryGround) (c : Dig 256) : IsCall169 (s1Of G c) :=
  ⟨0, 0, 1, Fmt.zero32, _, Or.inl rfl, rfl, rfl⟩

/-- The second public string is never the first: the second word of a call's label is its index. -/
theorem s1_ne_s0 (G : EntryGround) (pol lay KL : ByteArray) (c : Dig 256) :
    s1Of G c ≠ s0Of pol lay KL := by
  intro h
  have e := _root_.Run.bytesToBits_inj h
  have w1 := Fmt.oStr_w1 0 169 0 1 Fmt.zero32 (entryXD G (digToBytes c)).base.params rfl
  have w2 := Fmt.oStr_w1 0 169 0 2 Fmt.zero32 (Fmt.configBytes [pol, lay, KL]) rfl
  rw [e, w2] at w1
  exact absurd w1 (by decide)

/-- On the hash's domain, at a number other than 162, the oracle made from the format's hash answers
the bits of a call's string with the call's value. -/
theorem oBits_call (n t i : ℕ) (st bs : ByteArray) (hn : n ≠ 162)
    (hd : Fmt.hDom n t i st bs = true) :
    oBits () (bytesToBits (Fmt.oStr 0 n t i st bs)) = bytesToDig (Fmt.formatHash n t i st bs) := by
  rw [_root_.Run.oBits_bytes _ (_root_.Run.plain_oStr 0 n t i st bs (Or.inl rfl))]
  have h := Fmt.HO_oracle n t i st bs hd
  unfold Fmt.HO at h
  rw [if_neg hn] at h
  rw [h]

/-- A call 169 with the index 1 or 2, the start of zeros and bytes within the bound is in the hash's
domain. -/
theorem hDom_169 (i : ℕ) (hi : i = 1 ∨ i = 2) (bs : ByteArray) (hb : bs.size ≤ 2 ^ 32 - 144) :
    Fmt.hDom 169 0 i Fmt.zero32 bs = true := by
  have e1 : decide (bs.size ≤ 2 ^ 32 - 144) = true := decide_eq_true hb
  have e2 : Fmt.leafOK 169 0 bs = true := by simp [Fmt.leafOK, Fmt.isLeaf]
  unfold Fmt.hDom
  rw [e1, e2]
  rcases hi with rfl | rfl <;> decide

/-- At the oracle made from the format's hash the public algorithm returns the program's digest of
the three public files, and the parameters' digest of the entry's description at that digest. -/
theorem pub2_oBits (G : EntryGround) (pol lay KL : ByteArray)
    (h0 : (Fmt.configBytes [pol, lay, KL]).size ≤ 2 ^ 32 - 144)
    (h1 : (entryXD G (Params.configurationDigest [pol, lay, KL])).base.params.size ≤
      2 ^ 32 - 144) :
    (pub2 (s0Of pol lay KL) (s1Of G)).det oBits =
      (bytesToDig (Params.configurationDigest [pol, lay, KL]),
        EntryRunTop.pdOf (entryXD G (Params.configurationDigest [pol, lay, KL]))) := by
  have hc : oBits () (s0Of pol lay KL) =
      bytesToDig (Params.configurationDigest [pol, lay, KL]) := by
    unfold s0Of
    rw [oBits_call 169 0 2 _ _ (by decide) (hDom_169 2 (Or.inr rfl) _ h0)]
    unfold Params.configurationDigest Fmt.configDigestW
    rw [formatHashFastForm_eq_formatHash]
  have hb : digToBytes (bytesToDig (Params.configurationDigest [pol, lay, KL])) =
      Params.configurationDigest [pol, lay, KL] :=
    _root_.Run.digToBytes_bytesToDig _ (Params.configurationDigest_size _)
  have hp : oBits () (s1Of G (bytesToDig (Params.configurationDigest [pol, lay, KL]))) =
      EntryRunTop.pdOf (entryXD G (Params.configurationDigest [pol, lay, KL])) := by
    unfold s1Of
    rw [hb, oBits_call 169 0 1 _ _ (by decide) (hDom_169 1 (Or.inl rfl) _ h1)]
    rfl
  show ((oBits () (s0Of pol lay KL)), oBits () (s1Of G (oBits () (s0Of pol lay KL)))) = _
  rw [hc, hp]
  rfl

end OnBytes.K.Arm.Pub
