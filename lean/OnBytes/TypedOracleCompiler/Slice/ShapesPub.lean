-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesPub.lean: THE PUBLIC STRINGS, written; the parts' one written reading at a
configuration; and what the two tables hold at the oracle that is made from the format's hash: at
that oracle itself (one file's own tables), and patched at the strings of requests.

`Three` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) has two sets of public strings: S₀, and S₁ at the values at
S₀. A part holds values of the hash as constants: the digest of the three configuration files, and
the digests of chains' parameter bytes, which hold that first digest. Here the two sets are written:
the string of the call on the configuration files; the strings of the calls on the parameter bytes
at the digest that the first table holds.

Main definitions.
 `scAt cfg`            the string of the call number 169 on the three configuration files, the
                       parameter file first.
 `dgOf cfg T₀`         the configuration digest that the first table holds: its value at that
                       string.
 `pubS₀ cfg`, `pubS₁ prm cfg T₀`   the public strings; prm: for each chain, its parameter bytes as a
                       function of the configuration digest.
 `rdC z cfg`           the parts' one written reading: `rdAt z (dgOf cfg)`.
Main theorems.
 `pubS₀_169`, `pubS₁_169`   all are strings of calls with the number 169.
 `dgOf_size`           the digest has 32 bytes.
 `call169_oBits`       the oracle made from the format's hash has, at the string of a call number
                       169 from 32 zero bytes, the format's own hash of that call.
 `dgOf_pub₀`           at that oracle, patched by a quiet function, the first table holds the
                       program's digest of the three files.
 `pub₁_at`             and the second table holds, at the string of each chain's parameter bytes
                       at that digest, the format's digest of these bytes.

What is not claimed. Which chains' parameter bytes a part needs, and that they are any function of
the digest: prm is an argument. That a part reads its tables at these strings alone. The four
theorems on tables ask that what is hashed has at most 2^32 - 144 bytes. Nothing here unfolds a
hash: `Fmt.formatHash`, `Fmt.oracle`, `Run.oBits` and their laws are taken from the library by name. No
probability. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesReadsPart
import OnBytes.TypedOracleCompiler.Slice.ShapesOBits
import OnBytes.TypedOracleCompiler.Slice.ShapesOne
import OnBytes.Hash.HEq
import OnBytes.Params.Configure

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open _root_.Iop Rom _root_.Run

/-! ## The strings -/

/-- The string of the call on the three configuration files: number 169, index 2, from 32 zero
bytes, the parameter file first, then the layout, then the scale file (`scOf`,
OnBytes/Slice/PartEntryTables.lean, at these three). -/
def scAt (cfg : Cfg) : List Bool := scOf [cfg.pol, cfg.lay, cfg.KL]

/-- The configuration digest that the first table holds: the bytes of its value at that
string. -/
def dgOf (cfg : Cfg) (T₀ : Tab) : ByteArray := cOf (scAt cfg) T₀

/-- It has 32 bytes. -/
theorem dgOf_size (cfg : Cfg) (T₀ : Tab) : (dgOf cfg T₀).size = 32 := cOf_size _ _

/-- The first public strings: the configuration's string alone. -/
def pubS₀ (cfg : Cfg) : Finset (List Bool) := {scAt cfg}

/-- The public strings that hang on the value at the first: for each chain, the string of the
call number 169, index 1, on its parameter bytes at the digest that the first table holds. -/
def pubS₁ (prm : List (ByteArray → ByteArray)) (cfg : Cfg) (T₀ : Tab) : Finset (List Bool) :=
  (prm.map fun p => s0Of (p (dgOf cfg T₀))).toFinset

/-- The first are strings of calls with the number 169. -/
theorem pubS₀_169 (cfg : Cfg) : ∀ s ∈ pubS₀ cfg, IsCall169 s := by
  intro s hs
  rw [Finset.mem_singleton.1 hs]
  exact isCall169_configStr _

/-- So are the second. -/
theorem pubS₁_169 (prm : List (ByteArray → ByteArray)) (cfg : Cfg) (T₀ : Tab) :
    ∀ s ∈ pubS₁ prm cfg T₀, IsCall169 s := by
  intro s hs
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs)
  exact isCall169_digestStr _

/-- The parts' one written reading at the sizes z and a configuration: `rawBy` at the digest
that the first table holds at the configuration's string, z's depth and salt length. -/
noncomputable def rdC (z : Size) (cfg : Cfg) : Tab → Tab → Trace (rom 256) → Dig 256 →
    Raw Run.PQ.SgX :=
  rdAt z (dgOf cfg)

/-- It does not see the entries at the public strings: what the bound for one file in one world asks
of the written reading. -/
theorem rdC_off (z : Size) (cfg : Cfg) (prm : List (ByteArray → ByteArray)) (T₀ T₁ : Tab)
    (S : Finset (List Bool)) (σ : Trace (rom 256)) (cm : Dig 256)
    (hS : S = pubS₀ cfg ∨ ∃ T, S = pubS₁ prm cfg T) :
    rdC z cfg T₀ T₁ (offSet S σ) cm = rdC z cfg T₀ T₁ σ cm := by
  show rawBy (dgOf cfg T₀) z.T.a z.shape.saltBytes (offSet S σ) cm =
    rawBy (dgOf cfg T₀) z.T.a z.shape.saltBytes σ cm
  refine rawBy_offSet _ _ _ S ?_ σ cm
  rcases hS with rfl | ⟨T, rfl⟩
  · exact pubS₀_169 cfg
  · exact pubS₁_169 prm cfg T

/-! ## What the tables hold at the patched oracle -/

/-- The oracle made from the format's hash has, at the string of a call number 169 from 32 zero
bytes, the format's own hash of that call, for an index of at most 2 and at most 2^32 - 144 bytes.
-/
theorem call169_oBits (i : ℕ) (hi : Fmt.idxOK 169 i = true) (bs : ByteArray)
    (hb : bs.size ≤ 2 ^ 32 - 144) :
    oB (oBits ()) (Fmt.oStr 0 169 0 i Fmt.zero32 bs) = Fmt.formatHash 169 0 i Fmt.zero32 bs := by
  have h1 := Fmt.HO_oracle 169 0 i Fmt.zero32 bs (dom0 169 i bs (by decide) (by decide) hi hb)
  unfold Fmt.HO at h1
  rw [if_neg (by decide)] at h1
  rw [ph_oStr 0 169 0 i Fmt.zero32 bs (Or.inl rfl)]
  exact h1

section
variable {D : DecR} {Xi : Type} (Θ : Three D Xi)

/-- AT THAT ORACLE, PATCHED BY A QUIET FUNCTION, THE FIRST TABLE HOLDS THE PROGRAM'S DIGEST OF THE
THREE CONFIGURATION FILES. Asked: the first public strings are `pubS₀ cfg`; what is hashed has at
most 2^32 - 144 bytes. -/
theorem dgOf_pub₀ (cfg : Cfg) (h₀ : Θ.S₀ = pubS₀ cfg) {f : List Bool → Option (Dig 256)}
    (hf : Quiet f) (hb : (Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144) :
    dgOf cfg (Θ.pub₀ (patch oBits f)) = Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL] := by
  have hm : scAt cfg ∈ Θ.S₀ := by
    rw [h₀]
    exact Finset.mem_singleton.2 rfl
  have e1 : Θ.pub₀ (patch oBits f) (scAt cfg) = oBits () (scAt cfg) := by
    unfold Three.pub₀ cutT own
    rw [if_pos hm]
    exact patch_none oBits f (scAt cfg) (hf.pub _ (isCall169_configStr _))
  unfold dgOf cOf
  rw [e1]
  show oB (oBits ()) (Fmt.oStr 0 169 0 2 Fmt.zero32
    (Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL])) = _
  rw [call169_oBits 2 (by decide) _ hb]
  unfold Params.configurationDigest
  rw [formatHashFastForm_eq_formatHash]
  rfl

/-- AND THE SECOND TABLE HOLDS, AT THE STRING OF A CHAIN'S PARAMETER BYTES, THE FORMAT'S DIGEST OF
THESE BYTES. Asked: the string is among the second public strings at the first table; the bytes
are at most 2^32 - 144. -/
theorem pub₁_at {f : List Bool → Option (Dig 256)} (hf : Quiet f) (params : ByteArray)
    (hm : s0Of params ∈ Θ.S₁ (Θ.pub₀ (patch oBits f))) (hb : params.size ≤ 2 ^ 32 - 144) :
    digToBytes (Θ.pub₁ (patch oBits f) (s0Of params)) = Fmt.paramsDigest params := by
  have e1 : Θ.pub₁ (patch oBits f) (s0Of params) = oBits () (s0Of params) := by
    unfold Three.pub₁ cutT own
    rw [if_pos hm]
    exact patch_none oBits f (s0Of params) (hf.pub _ (isCall169_digestStr _))
  rw [e1]
  show oB (oBits ()) (Fmt.oStr 0 169 0 1 Fmt.zero32 params) = _
  rw [call169_oBits 1 (by decide) _ hb]
  rfl

end

/-! ## The same at the oracle itself, for one file's tables -/

/-- THE FIRST TABLE THAT THE ORACLE MADE FROM THE FORMAT'S HASH ITSELF HOLDS, at `pubS₀ cfg`,
HOLDS THE PROGRAM'S DIGEST OF THE THREE CONFIGURATION FILES. -/
theorem dgOf_own₀ (cfg : Cfg)
    (hb : (Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144) :
    dgOf cfg (FileSpec.own₀ (pubS₀ cfg) oBits) =
      Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL] := by
  have e1 : FileSpec.own₀ (pubS₀ cfg) oBits (scAt cfg) = oBits () (scAt cfg) := by
    have hm : scAt cfg ∈ pubS₀ cfg := Finset.mem_singleton.2 rfl
    unfold FileSpec.own₀ cutT own
    rw [if_pos hm]
  unfold dgOf cOf
  rw [e1]
  show oB (oBits ()) (Fmt.oStr 0 169 0 2 Fmt.zero32
    (Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL])) = _
  rw [call169_oBits 2 (by decide) _ hb]
  unfold Params.configurationDigest
  rw [formatHashFastForm_eq_formatHash]
  rfl

/-- AND THE SECOND, at `pubS₁ prm cfg`, HOLDS AT THE STRING OF EACH CHAIN'S PARAMETER BYTES AT
THAT DIGEST THE FORMAT'S DIGEST OF THESE BYTES. -/
theorem own₁_at (cfg : Cfg) (prm : List (ByteArray → ByteArray)) (p : ByteArray → ByteArray)
    (hp : p ∈ prm) (hb : (Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)
    (hb' : (p (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])).size ≤ 2 ^ 32 - 144) :
    digToBytes (FileSpec.own₁ (pubS₀ cfg) (pubS₁ prm cfg) oBits
      (s0Of (p (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])))) =
      Fmt.paramsDigest (p (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])) := by
  have hm : s0Of (p (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])) ∈
      pubS₁ prm cfg (FileSpec.own₀ (pubS₀ cfg) oBits) := by
    unfold pubS₁
    rw [dgOf_own₀ cfg hb]
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨p, hp, rfl⟩)
  have e1 : FileSpec.own₁ (pubS₀ cfg) (pubS₁ prm cfg) oBits
      (s0Of (p (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))) =
      oBits () (s0Of (p (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))) := by
    unfold FileSpec.own₁ cutT own
    rw [if_pos hm]
  rw [e1]
  show oB (oBits ()) (Fmt.oStr 0 169 0 1 Fmt.zero32
    (p (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))) = _
  rw [call169_oBits 1 (by decide) _ hb']
  rfl

end OnBytes.Slice.Shapes
