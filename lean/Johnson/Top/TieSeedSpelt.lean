-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieSeedSpelt.lean: the typed oracle functions that a page's encoding reads out of the
oracle made from Lean's BLAKE2b answer the seed's two typed queries as the format's oracle answers
at the two written strings (`SeedSpelt`, Johnson/Top/TieSeedPort.lean), if the page takes the seeds'
code in (`TakesIn`, OnBytes/TypedOracleCompiler/Run/SeedPoints.lean).

Main names:
  `seedQ0_q0`, `seedQ1_q1`: the two typed queries of `outOfDomainSeedIs` (Johnson/TypedOracleCompiler/RecCompile/Seeds.lean)
    are the two typed forms of OnBytes/TypedOracleCompiler/Run/SeedPoints.lean, at the wire's tag, plain parts and
    typed pieces of a name: by rfl.
  `seedStr_eq`: the string of a block of the seeds' round (OnBytes/K/SeedBytes.lean), with the half
    written as a byte of the block's number modulo 2.
  `spelt_of_page`: `SeedSpelt` at `readBlocks (PageG.implG C) oBits`.
  `sdTest S0 p0 p1`: a seeds' wire with the tag of Test and two given plain parts; all else S0's.
  `spelt_arm`: `SeedSpelt` at that wire and at the encoding `implArmD`
    (OnBytes/TypedOracleCompiler/Run/ArmDirect.lean) at the wire's own number of digests, plain parts and typed
    pieces of a name: no hypothesis on a page is left.

Limits: in `spelt_of_page`, that a page takes the code in is a hypothesis. Nothing ties the wire's
typed pieces (`OutOfDomainSampleQueryLayout.cfg`, `OutOfDomainSampleQueryLayout.shape`) to the bytes `rest`. Nothing on soundness.


-/
import Johnson.Top.TieSeedPort
import OnBytes.TypedOracleCompiler.Run.ArmCodes

set_option autoImplicit false

namespace OnBytes.K

open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig digToBytes bitsToBytes)
open _root_.Run (oBits)
open TypedOracleCompiler.Run (PageG.Page PageG.implG)
open TypedOracleCompiler.Run.SeedPoints (q0 q1 TakesIn read_q0 read_q1)

variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)

/-- The first typed query of a seed is the first typed form. -/
theorem seedQ0_q0 (cm : Dig 256) :
    seedQ0 W S cm = q0 (typedOracleCarrier L Bd aT aL) S.t S.pl0 S.cfg S.shape cm := rfl

/-- The second typed query of a seed is the second typed form. -/
theorem seedQ1_q1 (v : Bits) : seedQ1 W S v = q1 (typedOracleCarrier L Bd aT aL) S.t S.pl1 v := rfl

/-- The string of a block of the seeds' round, with the half as a byte. -/
theorem seedStr_eq (ρ0 : ByteArray) (b : ℕ) :
    seedStr ρ0 b = Fmt.oStr (UInt8.ofNat (b % 2)) 162 Fmt.recordLabel 1 ρ0
      (ByteArray.empty ++ Fmt.tail .seeds 0 0 (b / 2)) := by
  unfold seedStr
  rcases Nat.mod_two_eq_zero_or_one b with e | e
  · rw [e, if_pos rfl]
    rfl
  · rw [e, if_neg (by decide)]
    rfl

/-- **A page that takes the seeds' code in spells the two queries.** -/
theorem spelt_of_page
    (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) S.t) (annOf (typedOracleCarrier L Bd aT aL) S.t) → Bool)
    (hp0 : ∀ p, isP0 p = true ↔ p = S.pl0) (hp1 : ∀ p, isP1 p = true ↔ p = S.pl1)
    (rest : ByteArray) (C : PageG.Page (typedOracleCarrier L Bd aT aL) W.K)
    (hC : TakesIn (typedOracleCarrier L Bd aT aL) S.t S.pl0 S.pl1 isP0 isP1 S.cfg S.shape hp0 hp1 rest W.K C)
    (hr : rest.size < 2 ^ 32) (hK : W.K < 2 ^ 48) :
    SeedSpelt W S (readBlocks (PageG.implG C) oBits) rest where
  first := fun cm =>
    read_q0 (typedOracleCarrier L Bd aT aL) S.t S.pl0 S.pl1 isP0 isP1 S.cfg S.shape hp0 hp1 rest W.K C hC cm
      hr
  round := fun v hv k => by
    rw [seedStr_eq]
    exact read_q1 (typedOracleCarrier L Bd aT aL) S.t S.pl0 S.pl1 isP0 isP1 S.cfg S.shape hp0 hp1 rest W.K C
      hC hK v hv k

/-- A seeds' wire with the tag of Test and two given plain parts; all else is S0's. -/
def sdTest (S0 : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)
    (p0 p1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test)) :
    OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL :=
  { S0 with t := .test, pl0 := p0, pl1 := p1 }

section
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.ArmDirect
open _root_.Run (PCode)

variable {I1 X1 : Type} {L1 : BatchProtocolWithLeafBody I1 X1} (S0 : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (l : ℕ) (hlt : l < 2 ^ 48) (hne : l ≠ Fmt.recordLabel)
  (f0 : PCode (FbIn 256 (typedOracleCarrier L Bd aT aL) .link))
  (h0 : ∀ q s, f0.put q = some s → Is160 l s) (F : FbPair L1 (typedOracleCarrier L Bd aT aL))
  (pR : PCode (FbIn 256 L1 .link × Fin (W.K + 1))) (hR : ∀ x s, pR.put x = some s → Is162 l s)
  (G : LeafPair L1 (typedOracleCarrier L Bd aT aL)) (V : Leaves L1) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (back : StrCode (AllPts 256 W.K (typedOracleCarrier L Bd aT aL)))

/-- **The arm's encoding spells the seed's two queries.** -/
theorem spelt_arm (hr : rest.size < 2 ^ 32) (hK : W.K < 2 ^ 48) :
    SeedSpelt W (sdTest W S0 p0 p1)
      (readBlocks (implArmD (typedOracleCarrier L Bd aT aL) p0 p1 isP0 isP1 S0.cfg S0.shape hp0 hp1 rest W.K l
        hlt hne f0 h0 F pR hR G V cfg hcfg back) oBits) rest :=
  spelt_of_page W (sdTest W S0 p0 p1) isP0 isP1 hp0 hp1 rest
    (pageArmD (typedOracleCarrier L Bd aT aL) p0 p1 isP0 isP1 S0.cfg S0.shape hp0 hp1 rest W.K l hlt hne f0 h0
      F pR hR G V cfg hcfg back)
    (takesIn_pageS (typedOracleCarrier L Bd aT aL) p0 p1 isP0 isP1 S0.cfg S0.shape hp0 hp1 rest W.K _ _ cfg
      hcfg back) hr hK

end

end OnBytes.K
