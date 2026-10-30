-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Pub/ArmFamily.lean: the codings of the entry's arm as a family over pairs of public
digests; at the program's own two digests it is the coding of the tie; under each of its members the
two public strings code points of the spare oracle.

Why. `arm_pr_pub2` (Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublic.lean) bounds the entry's arm where the
configuration's digest and the parameters' digest are answers of the drawn function. It is said for
every family of codings over pairs of digests that meets three premises on the two public strings;
its head says that no such family is built. Here one is: the coding of the tie (`mAt`,
Johnson/Top/TieArmAt.lean) with both digests as letters.

Main names.
 `mPub d`        `mAtP` (Johnson/Top/Pub/ArmOther.lean) at the bytes of d.1 as the configuration's
                 digest and at d.2 as the parameters' digest. The letters of `mAt` whose types name
                 the description at c (pbF, bd, isPL, hpL), rest1 and back are families over c here.
 `mPub_at`       at (the digest c of 32 bytes, `EntryRunTop.pdOf` of the description at c) it is
                 `mAt` at c and at the families' members at c.
 `isOther_mPub`  under every member the string of a call 169 codes a point of the spare oracle.
 `mPub_s0`, `mPub_s1`   so do the two public strings of Johnson/Top/Pub/PubStrings.lean.

What is not claimed. No bound is stated here (Johnson/Top/Pub/ArmPublicAt.lean). That families pbF,
bd, isPL with hpL exist at an object L and a wire W is not shown here: they are letters, as in
`mAt`. Nothing on any hash; nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.Pub.ArmOther
import Johnson.Top.Pub.PubStrings

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm.Pub

open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig digToBytes oBits)
open TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb (p0E)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Slice.EntryFill (Ls)
open OnBytes.Slice (seedEntry)
open OnBytes.Tie (EntryGround)
open OnBytes.K OnBytes.K.Arm

variable (G : EntryGround)
  (d₁ : Sd1 G.q.link.table.cubeBits G.q.link.table.answers) (rest1 : ByteArray → ByteArray) (nb : ℕ)
  {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (S0 : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig 256))
  (pbF : ∀ c : ByteArray,
    PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) ≃
      PlainPart (shapeOf (Ls (entryXD G c) d₁) .link) (annOf (Ls (entryXD G c) d₁) .link))
  (bd : ∀ c : ByteArray, (typedOracleCarrier L Bd aT aL).Bd ≃ (Ls (entryXD G c) d₁).Bd)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (isPL : ByteArray →
    PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) → Bool)
  (hpL : ∀ c p, isPL c p = true ↔
    p = (pbF c).symm (p0E (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)))
  (tr : L.OutOfDomainAnswer → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (back : ByteArray → StrCode (AllPts 256 W.K (typedOracleCarrier L Bd aT aL)))

/-- The family of codings of the arm over pairs of public digests: the first as the configuration's
digest, the second as the parameters' digest. -/
def mPub (d : Dig 256 × Dig 256) : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL)) 256 :=
  mAtP G (digToBytes d.1) d.2 d₁ (rest1 (digToBytes d.1)) nb (_root_.Run.size_digToBytes d.1) W S0
    cA (pbF (digToBytes d.1)) (bd (digToBytes d.1)) p0 p1 isP0 isP1 hp0 hp1 (isPL (digToBytes d.1))
    (hpL (digToBytes d.1)) tr hinj hlen htr (back (digToBytes d.1))

/-- At a configuration digest c of 32 bytes and the format's digest of the parameter bytes of the
description at c, the family's member is the coding of the tie at c. -/
theorem mPub_at (c : ByteArray) (hc : c.size = 32) :
    mPub G d₁ rest1 nb W S0 cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen htr back
        (bytesToDig c, EntryRunTop.pdOf (entryXD G c)) =
      mAt G c d₁ (rest1 c) nb hc W S0 cA (pbF c) (bd c) p0 p1 isP0 isP1 hp0 hp1 (isPL c) (hpL c) tr
        hinj hlen htr (back c) := by
  have key : ∀ (c' : ByteArray) (_ : c' = c) (h' : c'.size = 32),
      mAtP G c' (EntryRunTop.pdOf (entryXD G c)) d₁ (rest1 c') nb h' W S0 cA (pbF c') (bd c') p0 p1
          isP0 isP1 hp0 hp1 (isPL c') (hpL c') tr hinj hlen htr (back c') =
        mAtP G c (EntryRunTop.pdOf (entryXD G c)) d₁ (rest1 c) nb hc W S0 cA (pbF c) (bd c) p0 p1
          isP0 isP1 hp0 hp1 (isPL c) (hpL c) tr hinj hlen htr (back c) := by
    rintro _ rfl _
    rfl
  exact key _ (_root_.Run.digToBytes_bytesToDig c hc) _

/-- Under every member of the family the string of a call with the number 169 codes a point of the
spare oracle. -/
theorem isOther_mPub (d : Dig 256 × Dig 256) (s : List Bool) (hs : IsCall169 s) :
    IsOther (mPub G d₁ rest1 nb W S0 cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen htr
      back d) s :=
  isOther_mAtP G (digToBytes d.1) d.2 d₁ (rest1 (digToBytes d.1)) nb
    (_root_.Run.size_digToBytes d.1) W S0 cA (pbF (digToBytes d.1)) (bd (digToBytes d.1)) p0 p1 isP0
    isP1 hp0 hp1 (isPL (digToBytes d.1)) (hpL (digToBytes d.1)) tr hinj hlen htr
    (back (digToBytes d.1)) s hs

/-- The first public string codes a point of the spare oracle under every member. -/
theorem mPub_s0 (pol lay KL : ByteArray) (d : Dig 256 × Dig 256) :
    IsOther (mPub G d₁ rest1 nb W S0 cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen htr
      back d) (s0Of pol lay KL) :=
  isOther_mPub G d₁ rest1 nb W S0 cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen htr back d
    _ (s0_call169 pol lay KL)

/-- So does the second, at every first digest. -/
theorem mPub_s1 (d : Dig 256 × Dig 256) (c : Dig 256) :
    IsOther (mPub G d₁ rest1 nb W S0 cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen htr
      back d) (s1Of G c) :=
  isOther_mPub G d₁ rest1 nb W S0 cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen htr back d
    _ (s1_call169 G c)

end OnBytes.K.Arm.Pub
