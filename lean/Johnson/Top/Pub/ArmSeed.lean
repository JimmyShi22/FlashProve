-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Pub/ArmSeed.lean: the coding `mAt` of the entry's arm (Johnson/Top/TieArmAt.lean) is one
coding at any two record's wires: it does not hang on that argument.

By the definitions' text, which no theorem here states: `mAt` reads of its record's wire two fields
of `s0At` (Johnson/Top/TieSeedArm.lean), and `s0At` lays both over the wire that it is given: the
configuration's digest as `cfgL`, and the tables' shape.

Main theorem: `mAt_seed`, by rfl.

What it is for. A family of codings over configuration digests holds one record's wire as a letter,
while a written input of the arm holds the wire at its own digest. The two codings are compared
through this lemma, with both wires as letters.

What is not claimed. Nothing on the arm, whose seeds' tests do read the record's wire. Nothing on
soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.TieArmAt

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm.Pub

open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb (p0E)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (seedEntry)
open OnBytes.Tie (EntryGround)
open OnBytes.K OnBytes.K.Arm

variable (G' : EntryGround) (c : ByteArray)
  (d₁ : Sd1 G'.q.link.table.cubeBits G'.q.link.table.answers) (rest1 : ByteArray) (nb : ℕ)
  (hcfg : (entryXD G' c).base.cfg.size = 32)
  {I Y : Type} {L : HolographicProtocol I Y} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (S0 S0' : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig 256))
  (pbF : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) ≃
    PlainPart (shapeOf (EntryFill.Ls (entryXD G' c) d₁) .link)
      (annOf (EntryFill.Ls (entryXD G' c) d₁) .link))
  (bd : (typedOracleCarrier L Bd aT aL).Bd ≃ (EntryFill.Ls (entryXD G' c) d₁).Bd)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (isPL : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E (entryXD G' c) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry G'.q.link.table.cubeBits G'.q.link.table.answers)))
  (tr : L.OutOfDomainAnswer → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (back : StrCode (AllPts 256 W.K (typedOracleCarrier L Bd aT aL)))

/-- The coding of the arm is one coding at any two record's wires. -/
theorem mAt_seed :
    mAt G' c d₁ rest1 nb hcfg W S0 cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen htr
        back =
      mAt G' c d₁ rest1 nb hcfg W S0' cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen htr
        back := rfl

end OnBytes.K.Arm.Pub
