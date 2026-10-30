-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Pub/ArmPublicAt.lean: the bound on the entry's arm with the lax Link, at both sizes,
where the configuration's digest and the parameters' digest are answers of the drawn function, at
the family of the tie's own codings and the format's own two strings: no premise on strings is left.

`atFull_arm_pub2` and `atSmall_arm_pub2` (Johnson/Flat/ArmSibPublic.lean) take a family m of codings
and two strings s0, s1 as letters, with three premises: under every m d the strings s0 and s1 c code
points of the spare oracle, and s1 c is never s0. Here m is `mPub` (Johnson/Top/Pub/ArmFamily.lean):
the coding of the tie with both digests laid in; s0 and s1 are `s0Of`, `s1Of`
(Johnson/Top/Pub/PubStrings.lean): the strings of the format's two calls with the number 169. The
three premises are theorems there.

Main theorems: `atFull_arm_public`, `atSmall_arm_public`; `armAtFullPub_at`, `armAtSmallPub_at`: at
a configuration digest of 32 bytes the arm made of the public digests is the arm at that digest.

To be read with them. `mPub_at`: at the program's digest c of the public files and the format's
digest of the parameter bytes at c, the family's member is the tie's coding `mAt`. `pub2_oBits`: at
the oracle made from the format's hash the public algorithm returns these two digests.

What is not claimed. Soundness of one arm alone, with the lax Link; the limits in the heads of
ArmSibPublic.lean, LinkAnsPublic.lean and LinkAnsMaker.lean hold. The hypothesis on codes is the
theorem on codes, taken as given. The letters of the coding (pbF, bd, isPL, hpL, back as families
over the configuration's digest; p0, p1; tr) and of the arm (T, W, cfgOf, shape, pl0, pl1, code,
num) stay letters: that they can be filled at one object and wire is not shown here. So does the
ground G: "at both sizes" is of the written link alone, and nothing here ties G to it. No yes is
shown: the bound would hold of an arm that refuses everything. The run's value, which the format
hashes from the parameters' digest and bytes that the prover picks, is no public digest and is not
treated. No theorem carries the probability from the drawn function to the fixed hash.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.Pub.ArmFamily
import Johnson.Flat.ArmSibPublic

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm.Pub

open _root_.Compile TypedOracleCompiler.Iop Rom Prob Hiop TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice OnBytes.Flat Cb Cb.Ood
open OnBytes.RunA (RestR LrG)
open TypedOracleCompiler.Run.PQ (SOf)
open _root_.Run (ckP)
open TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb (p0E)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Slice.EntryFill (Ls)
open OnBytes.Tie (EntryGround)
open scoped ENNReal

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (frS.toDecR frZ 402653181).Claims X}
  {R : (frS.toDecR frZ 402653181).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 29 → GE) × NZ)
    ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a linkSibFull)
  (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (Bd : Type) (aT : RoundSplits T.test.shape)
  (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
  (t : Tag) (cfgOf : Dig 256 → List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS recLg recS).b ≤ W.K) (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))
  (G : EntryGround) (d₁ : Sd1 G.q.link.table.cubeBits G.q.link.table.answers)
  (rest1 : ByteArray → ByteArray) (nb : ℕ)
  (S0 : OutOfDomainSampleQueryLayout 256 W.K (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))
  (pbF : ∀ c : ByteArray,
    PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .link)
        (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .link) ≃
      PlainPart (shapeOf (Ls (entryXD G c) d₁) .link) (annOf (Ls (entryXD G c) d₁) .link))
  (bd : ∀ c : ByteArray,
    (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))).Bd ≃
      (Ls (entryXD G c) d₁).Bd)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (isPL : ByteArray → PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .link)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .link) → Bool)
  (hpL : ∀ c p, isPL c p = true ↔
    p = (pbF c).symm (p0E (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)))
  (tr : (LrG T).OutOfDomainAnswer → List T3) (hinj : Function.Injective (cAAtFull T))
  (hlen : ∀ a a', (cAAtFull T a).length = (cAAtFull T a').length)
  (htr : Function.Injective tr)
  (back : ByteArray → StrCode (AllPts 256 W.K
    (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))))

/-- At a configuration digest c of 32 bytes, with `SeedVals.cfgL` of the digest's bytes behind the
root in the first seed query, the arm made of the public digests is the arm with the lax Link at the
record's wire at `cfgL c`. The second digest stands in no typed query. -/
theorem armAtFullPub_at (c : ByteArray) (hc32 : c.size = 32) (p : Dig 256) :
    armAtFullPub T Bd aT W t (fun e => SeedVals.cfgL (_root_.Run.digToBytes e)) shape pl0 pl1 code
        num h dS (_root_.Run.bytesToDig c, p) =
      armL W (sdAtFull T Bd aT W t (SeedVals.cfgL c) shape pl0 pl1 code num h dS)
        (cAAtFull T) := by
  unfold armAtFullPub
  dsimp only
  rw [_root_.Run.digToBytes_bytesToDig c hc32]

include hd hc in
/-- The bound of `atFull_arm_pub2` at the family `mPub` of codings and the format's two public
strings. The maker runs; then the arm asks the function at the string of the call that hashes the
three public files, for c, and at the string of the call that hashes the parameter bytes of the
entry's chain at c, for p, and runs at them, through the tie's coding with c and p laid in. It
accepts, and what it promises fails on the one-block entries, under that coding, of the maker's log
of strings, with probability at most n 2^-128 + 2 (n + 1)² / 2^256 at n = 5 (tq + tVL W).
Hypotheses: the theorem on codes; `OKLA W`; the bound on the maker's calls; and the laws on the
letters: hd, hc on T; h on the wire's number of blocks; hp0, hp1, hpL, hinj, hlen, htr on the
coding's. No premise on the strings is left. The ground G is a free letter. -/
theorem atFull_arm_public (hA : BCHKS46At GF GE) (hW : OKLA W) (pol lay KL : ByteArray)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (expPub (armAtFullPub T Bd aT W t cfgOf shape pl0 pl1 code num h dS)
        (mPub G d₁ rest1 nb W S0 (cAAtFull T) pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen
          htr back)
        (pub2 (s0Of pol lay KL) (s1Of G)) Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHolds W (singleTr (mPub G d₁ rest1 nb W S0 (cAAtFull T) pbF bd p0 p1 isP0 isP1 hp0
              hp1 isPL hpL tr hinj hlen htr back x.2.1) x.1.2)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atFull_arm_pub2 T hd hc Bd aT W t cfgOf shape pl0 pl1 code num h dS hA hW _ _ _
    (mPub_s0 G d₁ rest1 nb W S0 (cAAtFull T) pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen
      htr back pol lay KL)
    (mPub_s1 G d₁ rest1 nb W S0 (cAAtFull T) pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen
      htr back)
    (s1_ne_s0 G pol lay KL) Mk tq hq

end

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (srS.toDecR srZ 524285).Claims X}
  {R : (srS.toDecR srZ 524285).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 19 → GE) × NZ)
    ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a linkSibSmall)
  (hd : T.dcd = (DecR.configurationOfStoredTable A R).D) (hc : T.coll = (DecR.configurationOfStoredTable A R).coll)
  (Bd : Type) (aT : RoundSplits T.test.shape)
  (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
  (t : Tag) (cfgOf : Dig 256 → List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS 19 1).b ≤ W.K) (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))
  (G : EntryGround) (d₁ : Sd1 G.q.link.table.cubeBits G.q.link.table.answers)
  (rest1 : ByteArray → ByteArray) (nb : ℕ)
  (S0 : OutOfDomainSampleQueryLayout 256 W.K (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))
  (pbF : ∀ c : ByteArray,
    PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .link)
        (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .link) ≃
      PlainPart (shapeOf (Ls (entryXD G c) d₁) .link) (annOf (Ls (entryXD G c) d₁) .link))
  (bd : ∀ c : ByteArray,
    (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))).Bd ≃
      (Ls (entryXD G c) d₁).Bd)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (isPL : ByteArray → PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .link)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .link) → Bool)
  (hpL : ∀ c p, isPL c p = true ↔
    p = (pbF c).symm (p0E (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)))
  (tr : (LrG T).OutOfDomainAnswer → List T3) (hinj : Function.Injective (cAAtSmall T))
  (hlen : ∀ a a', (cAAtSmall T a).length = (cAAtSmall T a').length)
  (htr : Function.Injective tr)
  (back : ByteArray → StrCode (AllPts 256 W.K
    (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))))

/-- At a configuration digest c of 32 bytes, with `SeedVals.cfgL` of the digest's bytes behind the
root in the first seed query, the arm made of the public digests is the arm with the lax Link at the
record's wire at `cfgL c`. The second digest stands in no typed query. -/
theorem armAtSmallPub_at (c : ByteArray) (hc32 : c.size = 32) (p : Dig 256) :
    armAtSmallPub T Bd aT W t (fun e => SeedVals.cfgL (_root_.Run.digToBytes e)) shape pl0 pl1 code
        num h dS (_root_.Run.bytesToDig c, p) =
      armL W (sdAtSmall T Bd aT W t (SeedVals.cfgL c) shape pl0 pl1 code num h dS)
        (cAAtSmall T) := by
  unfold armAtSmallPub
  dsimp only
  rw [_root_.Run.digToBytes_bytesToDig c hc32]

include hd hc in
/-- The bound of `atSmall_arm_pub2` at the family `mPub` of codings and the format's two public
strings. The maker runs; then the arm asks the function at the string of the call that hashes the
three public files, for c, and at the string of the call that hashes the parameter bytes of the
entry's chain at c, for p, and runs at them, through the tie's coding with c and p laid in. It
accepts, and what it promises fails on the one-block entries, under that coding, of the maker's log
of strings, with probability at most n 2^-128 + 2 (n + 1)² / 2^256 at n = 5 (tq + tVL W).
Hypotheses: the theorem on codes; `OKLA W`; the bound on the maker's calls; and the laws on the
letters: hd, hc on T; h on the wire's number of blocks; hp0, hp1, hpL, hinj, hlen, htr on the
coding's. No premise on the strings is left. The ground G is a free letter. -/
theorem atSmall_arm_public (hA : BCHKS46At GF GE) (hW : OKLA W) (pol lay KL : ByteArray)
    (Mk : OComp (rom 256) (OutLA 256 (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
    (tq : ℕ) (hq : Mk.QueryBound tq) :
    Rom.Pr (expPub (armAtSmallPub T Bd aT W t cfgOf shape pl0 pl1 code num h dS)
        (mPub G d₁ rest1 nb W S0 (cAAtSmall T) pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen
          htr back)
        (pub2 (s0Of pol lay KL) (s1Of G)) Mk)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHolds W (singleTr (mPub G d₁ rest1 nb W S0 (cAAtSmall T) pbF bd p0 p1 isP0 isP1 hp0
              hp1 isPL hpL tr hinj hlen htr back x.2.1) x.1.2)
            x.1.1.1 x.1.1.2.1 x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  atSmall_arm_pub2 T hd hc Bd aT W t cfgOf shape pl0 pl1 code num h dS hA hW _ _ _
    (mPub_s0 G d₁ rest1 nb W S0 (cAAtSmall T) pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen
      htr back pol lay KL)
    (mPub_s1 G d₁ rest1 nb W S0 (cAAtSmall T) pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen
      htr back)
    (s1_ne_s0 G pol lay KL) Mk tq hq

end

end OnBytes.K.Arm.Pub
