-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Pub/ArmOther.lean: the coding of the entry's arm with the parameters' digest as a
letter; and: under that coding, at all its letters, the string of a hash call with the number 169
codes a point of the spare oracle.

Why. The coding `mAt` of the entry's arm (Johnson/Top/TieArmAt.lean) holds two public digests: the
configuration's digest c, and the parameters' digest, which is there the format's hash of the
parameter bytes of the description at c (`EntryRunTop.pdOf`). A bound in which the two digests are
answers of the drawn function (Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublic.lean: `arm_pr_pub2`) takes a
family of codings over pairs of digests, and asks that under each the two public strings code points
of the spare oracle (`IsOther`, LinkAnsPublicArm.lean).

Main names.
 `isOther_implArmD`   under `ArmDirect.implArmD` (OnBytes/TypedOracleCompiler/Run/ArmDirect.lean), at all its data,
                      the string of a call 169 codes a point of the spare oracle.
 `mAtP`               the text of `mAt` with a letter pd in the place of `EntryRunTop.pdOf`.
 `mAt_eq`             `mAt` is `mAtP` at that digest: by rfl.
 `isOther_mAtP`       `IsOther (mAtP ..) s` for every string s of a call 169, at all letters.

What is not claimed. No family is built here, and no bound is stated. Nothing on any hash: a
statement on strings and codes. Nothing on calls with another number. Nothing on soundness; no
probability.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.TieArmAt
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublicArm
import OnBytes.TypedOracleCompiler.Run.Other169

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.ArmDirect
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.SeedPoints TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkOf
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I1 X1 I2 X2 : Type} {L1 : BatchProtocolWithLeafBody I1 X1} (L2 : BatchProtocolWithLeafBody I2 X2)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (K : ℕ) (l : ℕ) (hlt : l < 2 ^ 48) (hne : l ≠ _root_.Fmt.recordLabel)
  (f0 : PCode (FbIn 256 L2 .link)) (h0 : ∀ q s, f0.put q = some s → Is160 l s)
  (F : FbPair L1 L2) (pR : PCode (FbIn 256 L1 .link × Fin (K + 1)))
  (hR : ∀ x s, pR.put x = some s → Is162 l s) (G : LeafPair L1 L2) (V : Leaves L1)
  (cfg : ByteArray) (hcfg : cfg.size = 32) (back : StrCode (AllPts 256 K L2))

/-- Under the encoding over a second interface, at all its data, the string of a call with the
number 169 codes a point of the spare oracle. -/
theorem isOther_implArmD (s : List Bool) (hs : IsCall169 s) :
    ((implArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR hR G V cfg hcfg
      back).dec s).1 = TypedOracleCompiler.Compile.Batch.OracleName.other :=
  congrArg Sigma.fst (Other169.implS_inv169 L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K
    (linkD L2 K l hlt hne f0 h0 F pR hR) (leavesAlong G V) cfg hcfg back s hs)

end TypedOracleCompiler.Run.ArmDirect

namespace OnBytes.K.Arm

open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)
open TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb (p0E e162 e162_is)
open TypedOracleCompiler.Run.LinkAlongM (laterM leafM)
open TypedOracleCompiler.Run.LinkFirstAns (lf0 lf0_is)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Slice.EntryFill (Ls L0 pinsE)
open TypedOracleCompiler.Slice.ArmRead (implL2)
open OnBytes.Slice (seedEntry)
open OnBytes.Tie (EntryGround)
open OnBytes.K

variable (G : EntryGround) (c : ByteArray) (pd : Dig 256)
  (d₁ : Sd1 G.q.link.table.cubeBits G.q.link.table.answers) (rest1 : ByteArray) (nb : ℕ)
  (hcfg : (entryXD G c).base.cfg.size = 32)
  {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (S0 : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig 256))
  (pbF : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) ≃
    PlainPart (shapeOf (Ls (entryXD G c) d₁) .link) (annOf (Ls (entryXD G c) d₁) .link))
  (bd : (typedOracleCarrier L Bd aT aL).Bd ≃ (Ls (entryXD G c) d₁).Bd)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (isPL : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)))
  (tr : L.OutOfDomainAnswer → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (back : StrCode (AllPts 256 W.K (typedOracleCarrier L Bd aT aL)))

/-- The coding of the arm, with the parameters' digest as a letter. -/
abbrev mAtP : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL)) 256 :=
  implL2 (entryXD G c) d₁ (entryXD G c).base.cfg hcfg pd rest1
    (KeyLeaves.leavesAt (L0 (entryXD G c) d₁) nb (entryXD G c).base.cfg) (typedOracleCarrier L Bd aT aL) pbF
    bd p0 p1 isP0 isP1 (s0At W S0 c G.q.link.table).cfg (s0At W S0 c G.q.link.table).shape hp0 hp1
    (restOf G.q.link.table c) isPL hpL cA tr hinj hlen htr W.K back

/-- The coding of the arm is `mAtP` at the format's digest of the description's parameter bytes. -/
theorem mAt_eq :
    mAt G c d₁ rest1 nb hcfg W S0 cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen htr back =
      mAtP G c (EntryRunTop.pdOf (entryXD G c)) d₁ rest1 nb hcfg W S0 cA pbF bd p0 p1 isP0 isP1 hp0
        hp1 isPL hpL tr hinj hlen htr back := rfl

/-- Under the coding of the arm, at all its letters, the string of a call with the number 169 codes
a point of the spare oracle. -/
theorem isOther_mAtP (s : List Bool) (hs : IsCall169 s) :
    IsOther (mAtP G c pd d₁ rest1 nb hcfg W S0 cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj
      hlen htr back) s :=
  ArmDirect.isOther_implArmD (s := s) (hs := hs) ..

end OnBytes.K.Arm
