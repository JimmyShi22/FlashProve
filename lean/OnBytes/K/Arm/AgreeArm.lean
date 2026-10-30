-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/AgreeArm.lean: the encoding of the entry file's part (`ArmRead.implL2`,
OnBytes/TypedOracleCompiler/Slice/ArmRead.lean) gives every leaf query and every vertex query the same string as the
encoding of any function that writes there what `implL2`'s own two codes write.

`AgreeTrees` (OnBytes/K/Arm/AgreeTrees.lean) asks of two pages that they write the same at leaves
and vertices, and that their total codes do. The page of `implL2` writes at a leaf what its code of
leaves V writes, carried along the pair `leafM` at bd, and at a vertex what the library's code of
vertices writes under the digest cfg (`pNode`, Run/CodingPage166.lean): both by unfolding. For
proofs only; the program does not import this file.

Main theorems.
 `implL2_leafPut`, `implL2_nodePut`   what the page of `implL2` writes at a leaf and at a vertex.
 `agree_implL2`   `AgreeTrees (implL2 … K back) (implOf put inj hd back)`, for a function `put` on
                 the real points of the same interface, with the same number K of blocks and THE
                 SAME total code `back`, if `put` writes at a leaf what the carried V writes and at
                 a vertex what `pNode cfg` writes.
 `agree_implS`    two encodings `implS` (OnBytes/TypedOracleCompiler/Run/SeedPage.lean) with one code of leaves, one
                 digest and one total code agree on the trees, whatever their seeds' data and their
                 codes of the link's chain queries.

Not claimed. That any function meets what is asked. That one code of leaves spells the leaf calls
of all three files and of the stored tables as the programs do. Nothing on the request tree's two
oracles. Nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.TypedOracleCompiler.Slice.ArmLinkCode
import OnBytes.K.Arm.AgreeTrees

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.PageOf TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkAlongM
open TypedOracleCompiler.Slice.ArmRead TypedOracleCompiler.Slice.ArmLinkCode
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- **Two encodings `implS` with one code of leaves, one digest and one total code.** -/
theorem agree_implS {I X : Type} (L : BatchProtocolWithLeafBody I X)
    (p0 p1 q0 q1 : PlainPart (shapeOf L .test) (annOf L .test))
    (isP0 isP1 isQ0 isQ1 : PlainPart (shapeOf L .test) (annOf L .test) → Bool)
    (cfgL cfgL' : List (Dig 256)) (sh sh' : Bits)
    (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
    (hq0 : ∀ p, isQ0 p = true ↔ p = q0) (hq1 : ∀ p, isQ1 p = true ↔ p = q1)
    (rest rest' : ByteArray) (K : ℕ) (Lk Lk' : LinkCode L K) (V : Leaves L) (cfg : ByteArray)
    (hcfg : cfg.size = 32) (back : StrCode (AllPts 256 K L)) :
    AgreeTrees (implS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back)
      (implS L q0 q1 isQ0 isQ1 cfgL' sh' hq0 hq1 rest' K Lk' V cfg hcfg back) :=
  agree_of_back (pageS L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K Lk V cfg hcfg back)
    (pageS L q0 q1 isQ0 isQ1 cfgL' sh' hq0 hq1 rest' K Lk' V cfg hcfg back) (fun _ => rfl)
    (fun _ => rfl) rfl

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (V : Leaves (Ls D d₁))
  {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))
  (bd : L2.Bd ≃ (Ls D d₁).Bd)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf L2 .link) (annOf L2 .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (K : ℕ) (back : StrCode (AllPts 256 K L2))

/-- The page of which `implL2` is the encoding. -/
abbrev pageL2 : Page L2 K :=
  pageS L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K
    (linkAt D d₁ cfg hcfg pd rest1 L2 pbF isPL hpL cA tr hinj hlen htr K)
    (leavesAlong (leafM (Ls D d₁) L2 bd) V) cfg hcfg back

/-- At a leaf it writes what the carried code of leaves writes. -/
theorem implL2_leafPut (q : LeafIn L2) :
    (pageL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr
      hinj hlen htr K back).real.put (.inl q) =
      (leavesAlong (leafM (Ls D d₁) L2 bd) V).lf.put q := rfl

/-- At a vertex it writes what the library's code of vertices writes under cfg. -/
theorem implL2_nodePut (q : Bits × Bits) :
    (pageL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr
      hinj hlen htr K back).real.put (.inr (.inl q)) = (pNode cfg).put q := rfl

/-- **The entry file's encoding against the encoding of a function.** -/
theorem agree_implL2 (put : RealPts 256 K L2 → Option (List Bool))
    (inj : ∀ a b s, put a = some s → put b = some s → a = b)
    (hd : ∀ a s, put a = some s → ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s)
    (hl : ∀ q : LeafIn L2, put (.inl q) = (leavesAlong (leafM (Ls D d₁) L2 bd) V).lf.put q)
    (hn : ∀ q : Bits × Bits, put (.inr (.inl q)) = (pNode cfg).put q) :
    AgreeTrees (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
      isPL hpL cA tr hinj hlen htr K back)
      (implOf put inj hd back) :=
  agree_implOf (pageL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL
    hpL cA tr hinj hlen htr K back) put inj hd (fun q => (hl q).symm) fun q => (hn q).symm

end OnBytes.K.Arm
