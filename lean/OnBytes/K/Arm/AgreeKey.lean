-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/AgreeKey.lean: the encoding of the entry file's part and the encoding of the key
file's part, cut out of the page of all three files, give every leaf query and every vertex query
the same string.

`cutKey` (OnBytes/K/Arm/KeyCut.lean) writes at a leaf what the page's taken spelling of leaves
writes (`PageJ.leafX`, OnBytes/Maker/Page/Frame.lean) and at a vertex what the library's code of
vertices writes under the page's digest. `agree_implL2` (OnBytes/K/Arm/AgreeArm.lean) asks just
that. For proofs only; the program does not import this file.

Main theorem.
 `agree_entry_key`   `AgreeTrees (implL2 … K back) (implOf (cutKey C) inj hd back)`. Asked: the
                    page's taken spelling of leaves is the entry's code of leaves, carried; the
                    page's digest is the entry's; one number K of blocks and one total code `back`.

Not claimed. That `cutKey C` is one to one where it writes, or that its strings begin with the byte
0 or 1: both are hypotheses, as `implOf` takes them. That any page meets the two equations. The
first is an equation of functions: the key file's encoding gives a leaf the spelling's string
exactly where the entry's code of leaves writes; every other leaf, even one of the key file's own,
goes to `back`. That one code of leaves spells the leaf calls of both files and of the stored tables
as the programs do. Nothing on the proof file's part. Nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.AgreeArm
import OnBytes.K.Arm.KeyCut

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

/-- **The entry file's encoding and the key file's agree on the trees.** -/
theorem agree_entry_key (C : KeyCut L2 K)
    (inj : ∀ a b s, cutKey C a = some s → cutKey C b = some s → a = b)
    (hd : ∀ a s, cutKey C a = some s → ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s)
    (hX : C.P.leafX = (leavesAlong (leafM (Ls D d₁) L2 bd) V).lf.put) (hc : C.P.cfg = cfg) :
    AgreeTrees (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
      isPL hpL cA tr hinj hlen htr K back)
      (implOf (cutKey C) inj hd back) :=
  agree_implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA
    tr hinj hlen htr K back (cutKey C) inj hd (fun q => by rw [cutKey_leaf, hX])
    fun q => by rw [cutKey_node, hc]

end OnBytes.K.Arm
