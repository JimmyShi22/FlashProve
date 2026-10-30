-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Pub/PubMany.lean: the public algorithm of any number of digests (`pubN`,
Johnson/TypedOracleCompiler/RecCompile/PublicMany.lean) at the format's own strings: the call that hashes the three
public files, then the calls that hash a list of parameter bytes made of that digest. At the oracle
made from the format's hash it returns the program's digest of the three files and the format's
digests of these parameter bytes.

Why. Johnson/Top/Pub/PubStrings.lean says this of two digests (`pub2_oBits`): the entry's arm. The
readings of a proof file and of a key file have four public digests: the first, and three chains'
parameters' digests. Here the list of parameter bytes is a letter: `par`, from the bytes of a digest
of the public files to a list of byte strings (at use: a planner's plain steps at a given digest;
the empty list where it refuses).

Main names.
  `sParOf b`: the bits of the string of the call 169, index 1, on the bytes b. `s1Of_eq`: `s1Of G c`
    is that at the entry's parameter bytes.
  `ssOf par`: the list of these strings, as a function of the first digest.
  `oBits_cfg`, `oBits_par`: that oracle's answers at the two kinds of strings, each under a bound on
    the length of what is hashed.
  `pubN_oBits_own`: the value at that oracle, with the first digest as the program's and the others
    as that oracle's own answers. One premise: the bound on the three files' bytes.
  `pubN_oBits`: the same with the format's digests `Fmt.formatHash 169 0 1 ..` in the list. A second premise:
    the bound on each parameter string at the program's digest.
  `ptN_call169`: every public string here is the string of a call with the number 169.

What is not claimed. One fixed oracle in the four theorems on values; no probability; nothing on
soundness. That a program asks these strings in a run is not said: the equations are between values.
The bounds on lengths are premises. `par` is a letter: that it gives what a planner plans is the
user's to show. No type of public digests is fixed: κ is a letter.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.Pub.PubStrings
import Johnson.TypedOracleCompiler.RecCompile.PublicMany

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm.Pub
open Rom TypedOracleCompiler.Run TypedOracleCompiler.Slice TypedOracleCompiler.Compile.Batch.Cms
open _root_.Run (bytesToBits bytesToDig digToBytes oBits)
open _root_.Iop (Dig)
open OnBytes.Tie (EntryGround)

/-- The string of the call that hashes parameter bytes b: number 169, index 1. -/
def sParOf (b : ByteArray) : List Bool := bytesToBits (Fmt.oStr 0 169 0 1 Fmt.zero32 b)

/-- The second public string of the entry's arm is that at the entry's parameter bytes. -/
theorem s1Of_eq (G : EntryGround) (c : Dig 256) :
    s1Of G c = sParOf (entryXD G (digToBytes c)).base.params := rfl

/-- It is the string of a call with the number 169. -/
theorem sParOf_call169 (b : ByteArray) : IsCall169 (sParOf b) :=
  ⟨0, 0, 1, Fmt.zero32, _, Or.inl rfl, rfl, rfl⟩

/-- The strings of the calls that hash the parameter bytes `par` gives at the bytes of c. -/
def ssOf (par : ByteArray → List ByteArray) (c : Dig 256) : List (List Bool) :=
  (par (digToBytes c)).map sParOf

/-- At the oracle made from the format's hash the answer at the first public string is the program's
digest of the three public files. Asked: what is hashed is within the hash's bound on lengths. -/
theorem oBits_cfg (pol lay KL : ByteArray)
    (h0 : (Fmt.configBytes [pol, lay, KL]).size ≤ 2 ^ 32 - 144) :
    oBits () (s0Of pol lay KL) = bytesToDig (Params.configurationDigest [pol, lay, KL]) := by
  unfold s0Of
  rw [oBits_call 169 0 2 _ _ (by decide) (hDom_169 2 (Or.inr rfl) _ h0)]
  unfold Params.configurationDigest Fmt.configDigestW
  rw [formatHashFastForm_eq_formatHash]

/-- At that oracle the answer at the string of parameter bytes b is the format's digest of b. Asked:
b is within the hash's bound on lengths. -/
theorem oBits_par (b : ByteArray) (hb : b.size ≤ 2 ^ 32 - 144) :
    oBits () (sParOf b) = bytesToDig (Fmt.formatHash 169 0 1 Fmt.zero32 b) := by
  unfold sParOf
  rw [oBits_call 169 0 1 _ _ (by decide) (hDom_169 1 (Or.inl rfl) _ hb)]

variable {D : Type} (κ : Dig 256 → List (Dig 256) → D) (pol lay KL : ByteArray)
  (par : ByteArray → List ByteArray)

/-- At the oracle made from the format's hash the public algorithm returns κ of the program's digest
of the three public files and of that oracle's own answers at the strings of the parameter bytes
that `par` gives at that digest. One premise: the bound on the three files' bytes. -/
theorem pubN_oBits_own (h0 : (Fmt.configBytes [pol, lay, KL]).size ≤ 2 ^ 32 - 144) :
    (pubN κ (s0Of pol lay KL) (ssOf par)).det oBits =
      κ (bytesToDig (Params.configurationDigest [pol, lay, KL]))
        ((par (Params.configurationDigest [pol, lay, KL])).map fun b => oBits () (sParOf b)) := by
  rw [pubN_det, oBits_cfg pol lay KL h0]
  unfold ssOf
  rw [_root_.Run.digToBytes_bytesToDig _ (Params.configurationDigest_size _), List.map_map]
  rfl

/-- The same with the format's own digests of these parameter bytes. A second premise: each of them
is within the hash's bound on lengths. -/
theorem pubN_oBits (h0 : (Fmt.configBytes [pol, lay, KL]).size ≤ 2 ^ 32 - 144)
    (h1 : ∀ b ∈ par (Params.configurationDigest [pol, lay, KL]), b.size ≤ 2 ^ 32 - 144) :
    (pubN κ (s0Of pol lay KL) (ssOf par)).det oBits =
      κ (bytesToDig (Params.configurationDigest [pol, lay, KL]))
        ((par (Params.configurationDigest [pol, lay, KL])).map fun b =>
          bytesToDig (Fmt.formatHash 169 0 1 Fmt.zero32 b)) := by
  rw [pubN_oBits_own κ pol lay KL par h0]
  exact congrArg _ (List.map_congr_left fun b hb => oBits_par b (h1 b hb))

/-- Every public string here is the string of a call with the number 169. -/
theorem ptN_call169 (s : List Bool) (h : PtN (s0Of pol lay KL) (ssOf par) s) : IsCall169 s := by
  rcases h with rfl | ⟨c, hc⟩
  · exact s0_call169 pol lay KL
  · obtain ⟨b, _, rfl⟩ := List.mem_map.1 hc
    exact sParOf_call169 b

end OnBytes.K.Arm.Pub
